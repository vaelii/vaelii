;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.resolution
  "Unification, pattern matching against the indexed store, and backward chaining.

  Matching is *type-aware*: a unary type predicate is matched over the subtype
  closure, so an antecedent `(animal ?x)` is satisfied by a stored `(dog Muffet)`.
  This is how increasing an individual's specificity never loses the reasoning
  that applied to its more general types — we consult the genl closure at match
  time rather than materializing supertype facts."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.datetime :as datetime]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

;; ---- unification --------------------------------------------------------

(def no-bindings {})

;; unify, unify-args and unify-var are mutually recursive (a term's arguments unify as a
;; sequence, each element as a term, and a bound variable is chased back through unify),
;; so one forward declaration is genuinely required here.
(declare unify-args unify-var)

(defn- dot-tail
  "The remaining sequence a dotted rest-variable binds to, as a canonical list."
  [y] (if (sequential? y) (apply list y) (list y)))

(defn unify
  "Unify terms x and y under `bindings`, returning an extended binding map or nil.
  A `(Quote X)` form (`sx/quote-form?`) is a constant: it unifies with a variable or with
  an equal form, and a variable inside it binds nothing.  Supports dotted rest patterns:
  a sublist `(. ?rest)` binds `?rest` to the whole remaining sequence, so
  `(?pred . ?args)` unifies with `(parentOf Tom Bob)` giving `?pred=parentOf`,
  `?args=(Tom Bob)`."
  ([x y] (unify x y no-bindings))
  ([x y bindings]
   (cond
     (nil? bindings)  nil
     (= x y)          bindings
     (sx/variable? x) (unify-var x y bindings)
     (sx/variable? y) (unify-var y x bindings)
     (or (sx/quote-form? x) (sx/quote-form? y)) nil
     :else            (unify-args x y bindings))))

(defn unify-args
  "Unify two argument sequences element by element, each element as a term (`unify`).
  The entry point for a caller holding argument lists, such as `(rest literal)`, rather
  than terms: the list `(Quote X)` is a quoted form as a term and the symbol `Quote`
  followed by X as an argument list."
  ([xs ys] (unify-args xs ys no-bindings))
  ([xs ys bindings]
   (cond
     (nil? bindings) nil
     (= xs ys)       bindings
     (and (sequential? xs) (= '. (first xs))) (unify-var (second xs) (dot-tail ys) bindings)
     (and (sequential? ys) (= '. (first ys))) (unify-var (second ys) (dot-tail xs) bindings)
     (and (sequential? xs) (sequential? ys) (seq xs) (seq ys))
     (unify-args (rest xs) (rest ys) (unify (first xs) (first ys) bindings))
     (and (sequential? xs) (sequential? ys) (empty? xs) (empty? ys))
     bindings
     :else           nil)))

(defn- occurs?
  "Does variable `v` occur in `x`, resolving `x`'s variables through `bindings`?  The
  guard `unify-var` needs before binding `v` to `x`: without it, unifying `?x` with
  `(f ?x)` builds the cyclic binding `{?x (f ?x)}`, and `substitute` — which assumes
  acyclic bindings — loops on it.  Resolves each variable inline rather than
  substituting `x` whole first, so it needs no forward reference to `substitute` and
  stops at the first occurrence.  Terminates because every prior binding was itself
  occurs-checked, so `bindings` is acyclic.  A `(Quote X)` form holds no occurrence,
  since `unify` reads its variables as constants."
  [v x bindings]
  (cond
    (sx/variable? x)     (or (= v x)
                             (when-let [b (get bindings x)] (occurs? v b bindings)))
    (sx/quote-form? x)   false
    (sequential? x)      (boolean (some #(occurs? v % bindings) x))
    :else                false))

(defn- unify-var [v x bindings]
  (if-let [bound (get bindings v)]
    (unify bound x bindings)
    ;; occurs-check: binding `v` to a term that contains `v` would make the
    ;; substitution cyclic, so reject the unification instead of building it
    (when-not (occurs? v x bindings)
      (assoc bindings v x))))

(defn substitute
  "Replace bound variables in a pattern with their values (recursively).  A dotted
  rest pattern `(head ... . ?rest)` is spliced: `(?pred . ?args)` with `?args=(Tom Bob)`
  becomes `(parentOf Tom Bob)`.  A `(Quote X)` form comes back whole, since `unify` never
  binds inside it.  Eager, and a `PersistentList`: docs/inference.md, Resolution reads."
  [pattern bindings]
  (cond
    (sx/variable? pattern) (if-let [b (get bindings pattern)]
                             (substitute b bindings)
                             pattern)
    (sx/quote-form? pattern) pattern
    (and (sequential? pattern) (some #{'.} pattern))
    (let [head (mapv #(substitute % bindings) (take-while #(not= '. %) pattern))
          tail (substitute (second (drop-while #(not= '. %) pattern)) bindings)]
      (clojure.lang.PersistentList/create
       (if (sequential? tail)
         (into head tail)                  ; bound rest-var → splice the tail in
         (conj head '. tail))))            ; still unbound → keep the dotted form intact
    (sequential? pattern)
    (clojure.lang.PersistentList/create (mapv #(substitute % bindings) pattern))
    :else pattern))

(defn resolve-bindings
  "Fully dereference every variable in a binding map so chained variables
  (?g -> ?x -> Tom) collapse to their ground value."
  [bindings]
  (into {} (map (fn [[k _]] [k (substitute k bindings)])) bindings))

(defn project-answer
  "A finished derivation's bindings, resolved and cut down to the variables the query
  asked about.  `nil` `answer-vars` projects nothing.  The projection is by name, so a
  query that writes `?var0` gets `?var0`.  See docs/inference.md, Resolution reads."
  [bindings answer-vars]
  (let [resolved (resolve-bindings bindings)]
    (if (nil? answer-vars) resolved (select-keys resolved answer-vars))))

;; ---- matching against the store -----------------------------------------

(defn lazy-mapcat
  "`mapcat` that calls `f` **one element at a time**.

  Not a stylistic preference — `clojure.core/mapcat` is `(apply concat (map f coll))`,
  and `map` realizes a whole 32-element chunk at once when its source is chunked.
  Over a handful of contexts or subtypes that means *every* branch is expanded (each
  its own trie walk) before the first result is handed back, which is exactly the
  cost the matching layers exist to avoid.  Here the recursive call sits inside
  `lazy-seq`, so a caller taking one solution expands one branch."
  [f coll]
  (lazy-seq
   (when-let [s (seq coll)]
     (concat (f (first s)) (lazy-mapcat f (rest s))))))

(defn- unary? [s] (and (sequential? s) (= 2 (count s))))

(def ^:dynamic *arg-root-retrieval*
  "Whether `match-one` may retrieve candidate handles from a secondary argument root
  instead of always walking the trie.  `candidate-handles` intersects the pattern's scoped
  argument roots (`sentexes-with-args`).  The candidates are a superset of the trie's hits
  and `unify` filters them, so the switch changes cost and never the matches.  Binding it
  false forces the trie, which `arg_root_retrieval_test` compares against.  Default true.
  See docs/indexing.md, Argument-root retrieval."
  true)

(def ^:dynamic *structural-index*
  "Whether `candidate-handles` may use the structural trie to narrow a positive pattern
  with a nested compound argument, `(mass ?o (QuantityFn ?n Kilogram))`.  On (default),
  `p/lookup` narrows on the compound's interior; off, the functor extent is the superset.
  The structural key is written unconditionally, so direct `p/lookup` paths always walk it.
  On and off return the same matches (`structural_index_test`).  Negative and flat patterns
  are untouched."
  true)

(defn- ctx-scope
  "The contexts an argument-root read of pattern sentex `pat` is restricted to: its own
  context when that is ground, every context (nil) when it is a variable."
  [pat]
  (let [c (:context pat)] (when-not (sx/variable? c) #{c})))

(def ^:dynamic *split-negative-roots?*
  "Does an open negative pattern's argument-root read leave out the positive facts at the
  index (`negative-root-handles`)?  A pure cost decision, like `*hierarchical-retrieval*`:
  `match-one` drops a positive candidate on polarity either way, so the answer set is the
  same.  Bind it false for the reference read, which fetches every candidate's record
  (`negative_roots_test`)."
  true)

(defn- negative-root-handles
  "The candidates of an open negative pattern on `pred` (nil for an open functor) over the
  argument roots of `ground`, in `ctxs` (nil for every context): the `:negative-roots`
  read of `candidate-handles`, less the positive facts it would name.  A negative roots
  under its positive body's functor, so the extent and the roots hold both polarities.
  Positive facts of each length are an index family (`:shape-tuple`).  When `ctxs` hold no
  denial of `pred` (`reads/stored-count-denials-in`) nothing is a candidate; otherwise an
  extent read drops each candidate the positive leaves hold before it is fetched."
  [ix pred ground ctxs]
  (if (or (nil? pred) (not *split-negative-roots?*))
    (p/sentexes-with-args ix pred ground ctxs)
    (let [cs (or ctxs p/every-context)]
      (if (zero? (reads/stored-count-denials-in ix pred cs))
        #{}
        (let [cands (p/sentexes-with-args ix pred ground ctxs)]
          (if (seq ground)
            cands
            ;; each length's positive leaves, as sets: a leaf comes back as stored, which
            ;; is a set on every backend that keeps one, and is copied otherwise
            (let [pos (into [] (map #(let [hs (reads/as-stored-shape-tuples-in ix pred % cs)]
                                       (if (set? hs) hs (set hs))))
                            (reads/as-stored-shape-lengths ix pred))]
              (into #{} (remove (fn [h] (some #(contains? % h) pos))) cands))))))))

(defn- candidate-handles
  "The stored handles to unify `pat` against: a superset of the positional trie hits that
  `match-one`'s `unify` filters to the identical set, chosen to minimize index lookups.
  The decision is one of seven keywords (`vaelii.impl.profile` tallies it) and a `case`
  does the read.  The trie keeps a fully-ground test, a ground left prefix under a variable
  context, and a non-indexable token; the other shapes divert to argument roots (intersected
  over every ground argument), the predicate-agnostic root for a variable functor, the
  structural trie (`*structural-index*`) or the context-scoped leaf.  See docs/indexing.md,
  Argument-root retrieval."
  [kb pat]
  (let [ix   (:index kb)
        body (sx/body pat)]
    (if (or (not (sequential? body)) (empty? body))
      (do (prof/record-goal pat :trie)
          (p/lookup ix (sx/path pat)))
      (let [f       (first body)
            args    (vec (rest body))
            pred    (when (and (symbol? f) (not (sx/variable? f))) f)
            var-fn? (and (symbol? f) (sx/variable? f))
            var-idx (first (keep-indexed (fn [i a] (when-not (sx/ground-term? a) i)) args))
            ground  (keep-indexed (fn [i a] (when (sx/indexable-term? a) [(inc i) a])) args)
            ;; an open functor puts every argument behind it, so no root is readable and the trie keeps the case
            stuck?  (and (seq ground)
                         (or var-fn?
                             (and var-idx
                                  (some (fn [[pos _]] (> (dec pos) var-idx)) ground))))
            ;; a ground context, which the trie reaches only after fanning over every
            ;; open argument, and arguments the roots key exactly (variables and
            ;; indexable terms), so the context's leaves are the whole candidate set
            scoped? (and pred var-idx (seq ground)
                         (not (sx/variable? (:context pat)))
                         (every? #(or (sx/variable? %) (sx/indexable-term? %)) args))
            extent? (and pred (seq args) (every? sx/variable? args)
                         (not (sx/variable? (:context pat))))
            path
            (cond
              (and pred (some #(= sx/dot-marker %) args)) :functor-extent

              ;; A negative key holds its whole body as one token, so the trie matches a negative only exactly
              ;; and `p/lookup` answers `#{}` for every open negative. The secondary indexes (predicate extent,
              ;; argument roots) see inside a negative. Unconditional: the trie is no reference for this shape.
              (and (sx/negative? pat) (not (sx/ground-term? body)))
              (if (or pred (seq ground)) :negative-roots :negative-fan)

              ;; A ground argument after a variable: the argument root keys even a compound whole, so it binds in
              ;; one read what the trie must fan out to reach.
              (and *arg-root-retrieval* (or stuck? scoped?)) :arg-roots

              ;; Every argument open in a ground context: the predicate extent ends in the context, so its leaf is
              ;; the candidate set.
              (and *arg-root-retrieval* extent?) :context-extent

              ;; A positive pattern with a nested compound argument: `p/lookup` narrows on the interior; off, the
              ;; functor extent is the fallback superset. A variable functor always takes the trie.
              (and (not (sx/negative? pat)) (some sequential? args))
              (if (or *structural-index* (nil? pred)) :structural :functor-extent)

              ;; trie: left-prefix, test, or number-only
              :else :trie)]
        (prof/record-goal pat path)
        (case path
          ;; a ground context is matched exactly (`match-one` unifies it), so the argument
          ;; roots read that context's leaves alone
          :negative-roots (negative-root-handles ix pred ground (ctx-scope pat))
          :negative-fan   (let [pth (sx/path pat)]
                            (into #{} (mapcat #(p/lookup ix (assoc pth 1 %)))
                                  (p/children ix [:false])))
          :arg-roots      (p/sentexes-with-args ix pred ground (ctx-scope pat))
          :context-extent (p/sentexes-with-args ix pred [] (ctx-scope pat))
          :structural     (p/lookup ix (sx/path pat))
          :functor-extent (p/sentexes-with-args ix pred [] (ctx-scope pat))
          :trie           (p/lookup ix (sx/path pat)))))))

(defn holding-class
  "`handle → class` for a separation's denial (`tax/monotonic-route-witness`) and the
  contrapositive fan (`contrapositive-predicates`): the live
  JTMS defeat class of the handle, nil while it is OUT, and `:monotonic` for a believed
  literal in the forced-monotonic set (`decide/forced-literal?`) whatever strength it
  was written at.  A separation is outside that set (docs/nmtms.md, \"The
  forced-monotonic set\"), so the part edges a `:default` `covering` installs read
  `:default`."
  [kb]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        tax  (reasoning/taxonomy kb)]
    (fn [h]
      (when-let [c (jtms/defeat-class tms h)]
        (if (and (not= :monotonic c)
                 (some->> (p/get-sentex recs h) :sentence (decide/forced-literal? tax)))
          :monotonic
          c)))))

(defn contrapositive-predicates
  "`[straight swapped]`: the predicates a negated pattern on `f` fans over from the vantage
  `context`, `f`'s `genl` closure through the edges the reader holds at `:monotonic`
  (`tax/contrapositive-closure` under `holding-class`).  `straight` members are read with
  their arguments as written, `swapped` ones with arguments 1 and 2 exchanged.  The one
  definition the negated arms of `match1`, `subsuming-unify` and `fanned-match` read."
  [kb f context]
  (tax/contrapositive-closure (reasoning/taxonomy kb) f context (holding-class kb)))

(defn- fan-closure
  "`[straight swapped]` for `f` in direction `dir`: `tax/signed-closure` `:down` for a
  positive pattern, `contrapositive-predicates` for a negated one's body (`:up`)."
  [kb dir f context]
  (if (= dir :up)
    (contrapositive-predicates kb f context)
    (tax/signed-closure (reasoning/taxonomy kb) :down f context)))

(defn- contraposes?
  "Does a negated pattern on `af` fan to `ff` from `context`?  The unscoped-strength
  closure is tested first, since it is held across clock stretches and most pairs fail it."
  [kb af ff context]
  (and (contains? (first (tax/signed-closure (reasoning/taxonomy kb) :up af context)) ff)
       (contains? (first (contrapositive-predicates kb af context)) ff)))

(defn- swapped-unify
  "Bindings unifying the binary `pattern` with `fact` read with its two arguments
  exchanged, when `fact`'s predicate is in `pattern`'s predicate's swapped `dir` fan
  (`fan-closure`, `:down` for a positive pattern, `:up` for a negated one's body), else
  nil.  nil off one map read on a KB declaring no `genlInverse`."
  [kb dir pattern fact bindings context]
  (let [tx (reasoning/taxonomy kb)]
    (when-not (tax/genl-inverse-free? tx)
      (let [pf (when (sequential? pattern) (first pattern))
            ff (when (sequential? fact) (first fact))]
        (when (and (symbol? pf) (not (sx/variable? pf)) (symbol? ff) (not (sx/variable? ff))
                   (= 3 (count pattern)) (= 3 (count fact))
                   (contains? (second (fan-closure kb dir pf context)) ff))
          (unify-args (rest pattern) (list (nth fact 2) (nth fact 1)) bindings))))))

(defn match1
  "Unify a single antecedent pattern against a ground fact sentence, honoring predicate
  specificity: a fact whose functor is a spec of the antecedent's functor (via the genl
  closure) satisfies it.  Under a negation the fan reverses: `(not (dog ?x))` is met by a
  negative fact on a genl of `dog`, over the edges the reader holds at `:monotonic`
  (`contrapositive-predicates`).  With a `context`, the closure walks only edges that
  context sees.  The two-arity is unscoped, for callers that fix visibility elsewhere
  (`chain/fire-rules-for`).  See docs/inference.md, predicate specificity."
  ([kb antecedent fact] (match1 kb antecedent fact nil))
  ([kb antecedent fact context]
   (cond
     (and (sx/negation? antecedent) (sx/negation? fact))
     (let [a  (second antecedent)
           f  (second fact)
           af (when (sequential? a) (first a))
           ff (when (sequential? f) (first f))]
       (or (if (and (symbol? af) (not (sx/variable? af)) (symbol? ff) (not= af ff)
                    (contraposes? kb af ff context))
             (unify-args (rest a) (rest f))             ; genl of the body: unify the arguments
             (unify antecedent fact))
           ;; a `genlInverse` above the body's predicate: the arguments swapped
           (swapped-unify kb :up a f no-bindings context)))

     (and (unary? antecedent) (unary? fact))
     (let [[t a]  antecedent
           [t' x] fact]
       (if (and (symbol? t) (not (sx/variable? t)))
         (when (contains? (tax/specs (reasoning/taxonomy kb) t context) t') (unify a x))
         ;; a variable functor: `specs` is reflexive, so it never holds a concrete `t'` —
         ;; unify the whole literal, functor and argument, the way the n-ary `:else` arm
         ;; already does for its own variable-functor case
         (unify antecedent fact)))

     :else
     (let [af (when (sequential? antecedent) (first antecedent))
           ff (when (sequential? fact) (first fact))]
       (or (if (and (symbol? af) (not (sx/variable? af)) (symbol? ff) (not= af ff)
                    (contains? (first (tax/signed-closure (reasoning/taxonomy kb) :down af context)) ff))
             (unify-args (rest antecedent) (rest fact))  ; sub-predicate: unify the arguments
             (unify antecedent fact))
           ;; a `genlInverse` spec: the arguments swapped
           (swapped-unify kb :down antecedent fact no-bindings context))))))

(defn subsuming-unify
  "Unify a query `goal` against a rule's `consequent`, honoring predicate specificity: a
  consequent whose functor is a spec of the goal's functor answers the goal, binding the
  goal variable to the more specific instance.  The backward dual of `match1`; a negated
  goal fans as in `match1` and falls through to plain `unify` against a positive
  consequent.  With a `context` the genl closure is scoped to the edges it sees, as
  `match1` does; the arities without one are unscoped."
  ([kb goal consequent] (subsuming-unify kb goal consequent no-bindings nil))
  ([kb goal consequent bindings] (subsuming-unify kb goal consequent bindings nil))
  ([kb goal consequent bindings context]
   (let [neg? (and (sx/negation? goal) (sx/negation? consequent))
         g    (if neg? (second goal) goal)
         c    (if neg? (second consequent) consequent)
         gf   (when (sequential? g) (first g))
         cf   (when (sequential? c) (first c))
         ;; the polarity picks the direction: a *spec* conclusion answers a positive
         ;; goal, a *genl* conclusion answers a negated one
         reach? (if neg?
                  #(contraposes? kb %1 %2 context)
                  #(contains? (first (tax/signed-closure (reasoning/taxonomy kb) :down %1 context)) %2))]
     (or (if (and (symbol? gf) (not (sx/variable? gf))
                  (symbol? cf) (not (sx/variable? cf))
                  (not= gf cf)
                  (reach? gf cf))
           (unify-args (rest g) (rest c) bindings)
           (unify goal consequent bindings))
         ;; a `genlInverse` spec conclusion (a genl one, under a negation): swapped
         (swapped-unify kb (if neg? :up :down) g c bindings context)))))

(defn concluding-rule-handles
  "Handles of rules whose consequent predicate is `pred` or a spec of it, the backward dual
  of `fire-rules-for`.  Plus the variable-consequent catch-all bucket
  (`p/var-consequent-key`).  A variable `pred` answers every rule stated where `visible`
  reaches (`reads/as-stored-rules-in`).  A non-symbol `pred` degrades to the plain lookup.
  With `context` the spec fan walks the genl edges visible from it; with `visible`, a
  context set, each index read returns only rules stated in one of those contexts.  The
  cost is one probe per spec.  See docs/inference.md, Resolution reads."
  ([kb pred] (concluding-rule-handles kb pred nil nil))
  ([kb pred context] (concluding-rule-handles kb pred context nil))
  ([kb pred context visible]
   (let [idx        (:index kb)
         by-conseq  (fn [k] (if visible
                              (reads/as-stored-rules-by-consequent-in idx k visible)
                              (reads/as-stored-rules-by-consequent-global idx k)))
         var-conseq (set (by-conseq p/var-consequent-key))]
     (cond
       (sx/variable? pred)
       (into var-conseq (if visible
                          (reads/as-stored-rules-in idx :rule visible)
                          (reads/as-stored-rules-in-global idx :rule)))

       (symbol? pred)
       (into var-conseq
             (mapcat by-conseq)
             (let [[st sw] (tax/signed-closure (reasoning/taxonomy kb) :down pred context)]
               (if (empty? sw) st (into st sw))))

       :else
       (into var-conseq (by-conseq pred))))))

(defn concludes?
  "Is `concluding-rule-handles` non-empty, asked in every context: the same buckets, read
  until the first one holding a rule.  `provers/shadowing-channels` asks only this, once per
  goal.  It reads past the reader's ancestor set because the answer only decides whether a
  computed prover may answer alone: a rule the reader cannot see sends the goal down the
  union path, which costs time and never an answer."
  [kb pred context]
  (let [idx  (:index kb)
        held (fn [k] (seq (reads/as-stored-rules-by-consequent-global idx k)))]
    (boolean
     (or (held p/var-consequent-key)
         (cond
           (sx/variable? pred) (seq (reads/as-stored-rules-in-global idx :rule))
           (symbol? pred)      (let [[st sw] (tax/signed-closure (reasoning/taxonomy kb) :down pred context)]
                                 (or (some held st) (some held sw)))
           :else               (held pred))))))

(defn rule-visible-from?
  "May a rule stored in `rule-ctx` answer a goal asked from `context`?  A context reasons
  with the rules its `genlCx` ancestor set holds and no others, so the backward chainers
  agree with forward placement.  An open `?ctx` (or nil) is the unscoped path."
  [kb context rule-ctx]
  (or (not (and (symbol? context) (not (sx/variable? context))))
      (tax/sees? (reasoning/taxonomy kb) context rule-ctx)))

(def ^:dynamic *belief-blind*
  "Read the store as stored rather than as believed: `CxEverything`, and nothing else.
  A named opt-out of the belief-filtering invariant, so it is a dynamic var scoped to one
  read by the entry point that resolves the symbol.  It gives a syntactic query with no
  JTMS read, the only one that sees a defeated default.  An answer taken under it is not a
  justification and must not reach `why`."
  false)

(defn belief-blind?
  "`*belief-blind*`, read once by a retrieval path rather than once per candidate: a
  `^:dynamic` deref per candidate handle is measurable in the innermost loop.  Hoisting
  is sound because the entry point binds it around the whole read and `blind-seq`
  re-establishes it per realization step."
  []
  *belief-blind*)

(defn blind-seq
  "`s`, realized under `*belief-blind*` one element at a time, with the binding
  re-established for each.  A plain `binding` around a read is wrong here: the read
  answers with a lazy seq, the frame is popped before the first element is computed, and
  the belief filter runs unbound with nothing reporting it."
  [s]
  (lazy-seq
   (binding [*belief-blind* true]
     (when-let [c (seq s)]
       (cons (first c) (blind-seq (rest c)))))))

(defn rule-believed?
  "May the rule at `handle` chain: is it believed?  A stored rule is not a believed one,
  and the rule index posts on storage, so both chainers filter through this (a derived
  rule, docs/generators.md, leaves only when its licence does).  A sentex the TMS holds no
  node for is available, not disbelieved; for a rule that arm is defence, since
  `core/assert-inert` refuses a rule no entry point premised, and a wrong answer would
  silently stop a rule firing.  An inert rule is believed
  and kept from firing by its `:engines` alone (`rules/forward-sentex?` /
  `backward-sentex?`, docs/inference.md)."
  [kb handle]
  (let [tms (reasoning/tms kb)]
    (or *belief-blind*
        (not (jtms/known-datum? tms handle))
        (jtms/in? tms handle))))

(defn supporter-believed?
  "Is stored supporter `handle` believed from `context`: IN in the network, and not hidden
  there by a believed `except` or a placed `defeat` in force at `context`, or by resting
  only on a hidden handle (`exc/excepted?`, the read walk)?  `defeats?` false reads the
  excepts alone (`exc/excepted-in-network?`).  The taxonomy's `visible?` callback
  (`kb/attach-visibility!`): it decides whether a closure walk may cross an edge.  Its
  ancestor-set reads go through `tax/context-up-global`, so asking it inside a scoped walk
  never re-enters the filtered closure.  A context that disbelieves a `genl` edge stops
  reaching over it.  See docs/taxonomy.md."
  ([kb handle context] (supporter-believed? kb handle context true))
  ([kb handle context defeats?]
   (boolean
    (and (jtms/in? (reasoning/tms kb) handle)
         ;; `placed-reads?` is two count reads; `exc/closure-excepted-anywhere?` is an `exc/excepted?` per
         ;; context holding an except, so it comes second.
         (or (and (or (not defeats?) (not (exc/placed-reads? kb)))
                  (not (exc/closure-excepted-anywhere? kb handle)))
             (not (if defeats?
                    (exc/excepted? kb handle context)
                    (exc/excepted-in-network? kb handle context))))))))

(defn supporter-visible?
  "Is stored supporter `handle` believed, inherited, and not excepted from `context`?
  `defeats?` false leaves the placed defeats unread (`supporter-believed?`), as a
  firing's placement reads them."
  ([kb handle context] (supporter-visible? kb handle context true))
  ([kb handle context defeats?]
   (boolean
    (and (supporter-believed? kb handle context defeats?)
         (when-let [sentex (p/get-sentex (:records kb) handle)]
           (tax/sees? (reasoning/taxonomy kb) context (:context sentex)))))))

(defn exception-aware-placements
  "Placement candidates for `handles` stated in `contexts`: the maximal common
  descendants of `contexts`, or, while an except hides one of `handles` somewhere, the
  maximal contexts among them that see every handle with no except hiding it
  (`supporter-visible?` with no `defeat` read).  `exc/closure-excepted-anywhere?` is the
  coarse presence check, so the ordinary path walks no ancestor set when no except reaches
  the supporters.  A reading pass holds the check per handle (`tax/pass-held`).  Assertion
  contexts alone do not decide the case, since an except can hide a supporter at its own
  context while a meta-exception restores it in only one descendant ancestor set."
  [kb handles contexts]
  (let [tax (reasoning/taxonomy kb)]
    (if (some #(tax/pass-held [::closure-excepted-anywhere %]
                              (fn [] (exc/closure-excepted-anywhere? kb %)))
              handles)
      (let [common  (tax/common-descendants tax contexts)
            visible (filter (fn [ctx]
                              (every? #(supporter-visible? kb % ctx false) handles))
                            common)]
        (tax/max-cxs tax visible))
      (tax/maximal-common-descendant-contexts tax contexts))))

(defn visible-supporter-fn
  "`handle -> boolean`, memoized: is the sentex `handle` believed, inherited by
  `context`, and not hidden there by a visibility exception?  nil when `context` is nil
  or a `?var`, the unscoped read, which every caller reads as *no filter*.  The predicate
  a context-scoped equality read takes: the partition records its supporters as handles."
  [kb context]
  (when (and (symbol? context) (not (sx/variable? context)))
    (memoize #(supporter-visible? kb % context))))

(defn declared-by
  "The believed statements of the `kind` property of `pred` (`tax/prop-supporter-contexts`)
  that `context` sees, as a set of handles; every believed one for a nil or `?var` context.
  Every one, since naming one of two would decide a justification by arrival order."
  [kb kind pred context]
  (let [tx (reasoning/taxonomy kb)
        hs (tax/prop-supporter-contexts tx kind pred)]
    (if (empty? hs)
      #{}
      (let [tms (reasoning/tms kb)
            up  (when (and (symbol? context) (not (sx/variable? context)))
                  (set (tax/context-up tx context)))]
        (into #{}
              (keep (fn [[h c]] (when (and (or (nil? up) (nil? c) (contains? up c)) (jtms/in? tms h)) h)))
              hs)))))

(defn representative-in
  "`term`'s equality-class representative as `visible?` sees the merges.  The global
  representative, one map lookup, when nothing has merged `term`, when `visible?` is nil,
  or when the reader sees the whole class (`tax/class-fully-visible?`); `tax/scoped-class`
  otherwise."
  [kb visible? term]
  (let [tax (reasoning/taxonomy kb)]
    (if (and visible? (tax/merged? tax term) (not (tax/class-fully-visible? tax term visible?)))
      (second (tax/scoped-class tax term visible?))
      (tax/representative tax term))))

(defn same-class-in?
  "Do `a` and `b` denote one thing as `context` sees the merges?  The scoped twin of
  `tax/same-class?`, through `representative-in`; a nil or `?var` context gives the global
  answer.  `admit?` also refuses a supporter it does not hold for: `special/covered-merges`
  reads only the merges stored above a copy's context."
  ([kb a b context] (same-class-in? kb a b context nil))
  ([kb a b context admit?]
   (let [vis      (visible-supporter-fn kb context)
         visible? (if (and vis admit?) (every-pred admit? vis) vis)]
     (= (representative-in kb visible? a)
        (representative-in kb visible? b)))))

(defn- spelling-representative-in
  "`term`'s spelling-only representative as `visible?` sees the rewriteOf renames — used
  inside a quoting function's arguments, where a mention tracks a spelling rename but not
  an identity merge (`tax/spelling-representative`).  The lookup runs only when `merged?`
  holds, so an unmerged symbol is one map miss."
  [kb visible? term]
  (let [tax (reasoning/taxonomy kb)]
    (if (tax/merged? tax term)
      (tax/spelling-representative tax term visible?)
      term)))

(def ^:private equality-mention-heads
  "The equality relations, whose argument positions are **mentions**: a `sameAs` /
  `equals` merge does not fold them onto a class representative and a `rewriteOf` spelling
  rename does, as in a quoted position.  So a stored `(not (sameAs A B))` is not restated
  as `(not (sameAs A A))` by the merge it denies, and `rewrite/normalize-sentence` leaves
  these positions unrewritten too.  `kb/equality-predicates` holds the same set
  (`equality_test/the-mention-set-mirrors-the-canonical-equality-predicate-set`)."
  rewrite/equality-relations)

(defn equation?
  "Is `sentence` a positive equation, `(rewriteOf P D)`, `(sameAs A B)` or `(equals A B)`
  at the top?  Migration never restates one, so `retired-for?` never reports one retired
  and `goal-normal-form` asks an equation goal as spelled (docs/equality.md, \"Answering
  an equation\")."
  [sentence]
  (and (sequential? sentence) (contains? equality-mention-heads (first sentence))))

(defn- names-equality-relation?
  "Does `term` hold an equality relation at any depth — `(not (sameAs A B))`, say?  The
  flat per-symbol read in `retired-for?` does not know that such a relation's arguments
  are mentions, so a sentence this answers true for takes the structural walk instead."
  [term]
  (and (sequential? term)
       (or (contains? equality-mention-heads (first term))
           (boolean (some names-equality-relation? term)))))

(defn- spelling-term-plain
  "The spelling-only congruence walk — every non-variable symbol to its `rewriteOf`
  spelling representative (`spelling-representative-in`), never a `sameAs` / `equals`
  identity merge, recursively.  What an equality relation's argument positions take."
  [kb visible? term]
  (cond
    (sequential? term) (apply list (map #(spelling-term-plain kb visible? %) term))
    (symbol? term)     (if (sx/variable? term) term (spelling-representative-in kb visible? term))
    :else              term))

(defn- representative-term-plain
  "The ordinary congruence walk — every non-variable symbol to its class representative,
  recursively, for a sentence with no quoted position (`any-mention-position?`).  An
  equality relation's arguments are a mention: rewritten by spelling only, never folded
  onto a `sameAs` referent (`equality-mention-heads`)."
  [kb visible? term]
  (cond
    (sequential? term)
    (if (equality-mention-heads (first term))
      (apply list (first term) (map #(spelling-term-plain kb visible? %) (rest term)))
      (apply list (map #(representative-term-plain kb visible? %) term)))
    (symbol? term)     (if (sx/variable? term) term (representative-in kb visible? term))
    :else              term))

(defn attitude-application?
  "Is `term` `(P agent proposition)` for a declared `modal_predicate` `P` — the shape
  `BeliefProjectionProver` projects?  Its **third** argument is what the agent holds true,
  and the shape test is the prover's own: arity 2, over a sentence-shaped proposition.  A
  `(believes A Foo)` naming a bare term is not one — that argument refers rather than
  quotes, and stays transparent."
  [modal term]
  (and (= 3 (count term))
       (contains? modal (first term))
       (sequential? (nth term 2))))

(defn- any-mention-position?
  "Does `term` contain a quoted position at all — a quoting function's application, or an
  attitude?  This presence check keeps the flat reads flat: almost every sentence quotes
  nothing, and this answers that with a structural walk and two set lookups per compound
  head."
  [marks term]
  (boolean
   (when (sequential? term)
     (or (contains? (:quoting marks) (first term))
         (attitude-application? (:modal marks) term)
         (some #(any-mention-position? marks %) term)))))

(defn- representative-term-mention
  "The mention-aware walk.  Inside a quoted position (a quoting function's arguments, or
  the proposition a `modal_predicate` attributes to its agent) symbols are rewritten by
  spelling (`rewriteOf`) only, and `spelling?` stays on all the way down.  The operator's
  head and an attitude's agent are rewritten normally.  See docs/belief.md, Opacity."
  [kb visible? marks term spelling?]
  (cond
    (sequential? term)
    (cond
      (and (not spelling?) (equality-mention-heads (first term)))
      (apply list (first term)
             (map #(representative-term-mention kb visible? marks % true) (rest term)))

      (and (not spelling?) (contains? (:quoting marks) (first term)))
      (apply list
             (representative-term-mention kb visible? marks (first term) false)
             (map #(representative-term-mention kb visible? marks % true) (rest term)))

      (and (not spelling?) (attitude-application? (:modal marks) term))
      (list (representative-term-mention kb visible? marks (first term) false)
            (representative-term-mention kb visible? marks (second term) false)
            (representative-term-mention kb visible? marks (nth term 2) true))

      :else
      (apply list (map #(representative-term-mention kb visible? marks % spelling?) term)))
    (symbol? term)
    (if (sx/variable? term)
      term
      (if spelling?
        (spelling-representative-in kb visible? term)
        (representative-in kb visible? term)))
    :else term))

(defn representative-term
  "`term` with every non-variable symbol replaced by its class representative
  (`representative-in`) at any depth, so `(QuantityFn 5 Kilogram)` and `(QuantityFn 5 Kg)`
  meet under `(sameAs Kilogram Kg)`.  A mention position (a quoting function's arguments
  (`sx/quoting-functors`), a `modal_predicate`'s proposition) is rewritten by `rewriteOf`
  spelling only (docs/belief.md, Opacity).  The marks are read once, unscoped
  (`tax/mention-marks`)."
  [kb visible? term]
  (representative-term-mention kb visible? (tax/mention-marks (reasoning/taxonomy kb)) term false))

(defn- displacements-mention
  "Mention-aware collector, the traversal `representative-term-mention` rewrites by: inside
  a quoted position — a quoting function's arguments, or a `modal_predicate`'s proposition —
  a symbol moves by *spelling* (`rewriteOf`) only, so a quoted term whose referent merged
  under a `sameAs` is **not** recorded displaced.  The `why-not` map then names only the
  terms the rewrite actually moved."
  [kb visible? marks term spelling? acc]
  (cond
    (sequential? term)
    (cond
      (and (not spelling?) (equality-mention-heads (first term)))
      (reduce #(displacements-mention kb visible? marks %2 true %1)
              (displacements-mention kb visible? marks (first term) false acc)
              (rest term))

      (and (not spelling?) (contains? (:quoting marks) (first term)))
      (reduce #(displacements-mention kb visible? marks %2 true %1)
              (displacements-mention kb visible? marks (first term) false acc)
              (rest term))

      (and (not spelling?) (attitude-application? (:modal marks) term))
      (displacements-mention
       kb visible? marks (nth term 2) true
       (displacements-mention
        kb visible? marks (second term) false
        (displacements-mention kb visible? marks (first term) false acc)))

      :else
      (reduce #(displacements-mention kb visible? marks %2 spelling? %1) acc term))
    (and (symbol? term) (not (sx/variable? term)))
    (let [r (if spelling?
              (spelling-representative-in kb visible? term)
              (representative-in kb visible? term))]
      (if (not= r term) (assoc acc term r) acc))
    :else acc))

(defn displaced-terms-in
  "The `{old-term representative}` rewrites `sentence` undergoes under `visible?`, by the
  traversal `representative-term` rewrites with, so a mention held opaque to a `sameAs` is
  not reported displaced."
  [kb visible? sentence]
  (displacements-mention kb visible? (tax/mention-marks (reasoning/taxonomy kb)) sentence false {}))

(defn rewrite-rules-in
  "The believed oriented rewrite rules the reader `visible?` sees (nil: every one).  Every
  normal form reads its rules here: `normal-form`, `provers/EqualityProver` and an
  exception's goal rewrite."
  [kb visible?]
  (cond->> (tax/rewrite-rules (reasoning/taxonomy kb))
    visible? (filterv #(visible? (:handle %)))))

(defn normal-form
  "`term` (a sentence or a term) in the equality **normal form** the KB stores and asks in:
  `representative-term`, then argument terms reduced by the schematic equations the same
  reader sees (`rewrite/normalize-sentence`).  Migration and query both go through here.
  `visible?` is a built supporter predicate (`visible-supporter-fn`), nil for the unscoped
  read; `kb/rewrite-term` takes a context instead."
  [kb term visible?]
  (rewrite/normalize-sentence (rewrite-rules-in kb visible?)
                              (representative-term kb visible? term)))

(defn goal-held-as-spelled?
  "Is `goal` asked **as spelled**, exempt from the goal rewrite?  A `different` goal is,
  since its prover reads class membership, and so is a positive equation (`equation?`),
  whose arguments are mentions (docs/equality.md, \"What a merge does\" step 3)."
  [goal]
  (and (sequential? goal)
       (or (= 'different (nm/functor goal))
           (equation? goal))))

(defn goal-normal-form
  "`normal-form` for a **goal**, as `context` sees the merges, except for a goal
  `goal-held-as-spelled?` exempts.  `kb/rewrite-goal` is the read entry points' spelling;
  `BeliefProjectionProver` calls this one to put a proposition into the normal form of
  the **agent** whose belief it is."
  [kb goal context]
  (if (goal-held-as-spelled? goal)
    goal
    (normal-form kb goal (visible-supporter-fn kb context))))

(defn permuted-functor
  "The predicate whose permuting marks decide how `sentence` is spelled when stored — its
  functor, under a `not` — or nil."
  [sentence]
  (when (sequential? sentence)
    (let [s (if (= 'not (first sentence)) (second sentence) sentence)]
      (when (sequential? s)
        (let [f (first s)] (when (symbol? f) f))))))

(def nat-quoting-predicates
  "Predicates whose expression argument is a verbatim NAT payload, neither reified nor
  type-checked as a term."
  '#{natFormula rewriteOf})

(defn opaque-fn
  "`sx/sentex`'s `:opaque?` read: the functors whose applications keep their arguments as
  written below the literal.  A NAT-quoting predicate's expression is a verbatim payload,
  and a reifiable function's ground application is named by the constant its
  `nat-read/sorted-expression` hashes to (docs/nat.md), so neither is sorted here.  The
  reifiable mark is read unscoped: the walk decides the stored key, which every reader
  shares."
  [tax]
  #(or (contains? nat-quoting-predicates %) (tax/has-prop? tax :reifiable %)))

(defn meet-order
  "`sx/sentex`'s `:meet-order` read: for a function `f` some `(meetFunctionOf f R)`
  declares, `(fn [a b])` answering whether `a` lies below `b` by the registered
  comparator of any such `R` (`datetime/order-comparators`), or nil when no declared
  order has one.  A stored `(R a b)` fact is never read, so the canonical form does not
  move with belief."
  [tax]
  (fn [f]
    (let [rs (tax/meet-orders tax f)]
      (when (seq rs)
        (when-let [cs (seq (keep datetime/order-comparators (sort-by nm/name-key rs)))]
          (fn [a b] (boolean (some #(% a b) cs))))))))

(defn distinct-from
  "`sx/sentex`'s `:distinct-from` read: for a function `f` some `(distinctInArgAndRest f n)`
  declares, the least such `n`, or nil."
  [tax]
  (fn [f] (let [ns (tax/distinct-positions tax f)] (when (seq ns) (apply min ns)))))

(defn mention-declarations
  "The JTMS-IN `quotedArg` and `quotedArgAndRest` declarations on `f` typing position `n`,
  as stored sentexes: a `(quotedArg f n T)`, or a `(quotedArgAndRest f k T)` with `k` at
  most `n`.  Read only for a functor the taxonomy marks as declaring one, and KB-wide: the
  store's spelling, which every reader shares, keeps a mention any context declares, and
  a per-reader read filters the declarations (`without-unread-mentions`)."
  [kb tax f n]
  (let [q?   (tax/has-prop? tax :declares-quoted-arg f)
        qr?  (tax/has-prop? tax :declares-quoted-arg-and-rest f)
        read (fn [kind at?] (keep #(when-let [sx (p/get-sentex (:records kb) %)]
                                     (let [k (nth (:sentence sx) 2 nil)]
                                       (when (and (integer? k) (at? (long k))) sx)))
                                  (reads/believed-with-args kb kind {1 f})))]
    (when (or q? qr?)
      (concat (when q? (read 'quotedArg #(= (long n) %)))
              (when qr? (read 'quotedArgAndRest #(<= % (long n))))))))

(defn mention-at
  "`sx/sentex`'s `:mention-at?` read: whether position `n` of an application of `f` is a
  mention, which the walk keeps as written: one `mention-declarations` names.  Read
  unscoped: the walk decides the stored key, which every reader shares."
  [kb tax]
  (fn [f n] (boolean (seq (mention-declarations kb tax f n)))))

(defn store-marks
  "`sx/sentex`'s canonicalization reads under every permuting mark, term mark and mention
  position the store spells by.  Read unscoped: the fold decides the stored key, which
  every reader shares."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    {:symmetric?    #(tax/has-prop? tax :symmetric %)
     :groups-of     (fn [f _arity] (tax/commuting-groups tax f))
     :opaque?       (opaque-fn tax)
     :mention-at?   (mention-at kb tax)
     :associative?  #(tax/has-prop? tax :associative %)
     :idempotent?   #(tax/has-prop? tax :idempotent %)
     :meet-order    (meet-order tax)
     :distinct-from (distinct-from tax)}))

(defn probe-spelling
  "Literal `sentence` with every ground compound below it in the order the store holds
  it (`sx/sort-compounds` under `store-marks`), the spelling a match probes the store
  with.  `sentence` itself when no argument is a compound."
  [kb sentence]
  (if (and (seq? sentence) (some #(and (seq? %) (seq %)) (rest sentence)))
    (sx/sort-compounds sentence (store-marks kb))
    sentence))

(defn nested-probes
  "The spellings literal `sentence` is probed in for the compounds below it that hold a
  variable, each in every argument order its own functor's permuting marks let a stored
  fact hold it in (`sx/nested-arrangements` under `store-marks`), `sentence` first.
  `[sentence]` when no argument is a compound holding a variable."
  [kb sentence]
  (let [s (if (and (seq? sentence) (= sx/not-functor (first sentence))) (second sentence) sentence)]
    (if (and (seq? s) (some #(and (seq? %) (seq %) (not (sx/sortable-term? %))) (rest s)))
      (sx/nested-arrangements sentence (store-marks kb))
      [sentence])))

(def ^:dynamic *spelled-by*
  "nil, or `[pred context entries]`: while bound, `kb-sentex` sorts a literal on `pred` in
  `context` by the permuting marks `entries` lists (`mark-entries`' keys) and no others,
  so `chain/respell-rows!` stores, and `core/handle-of` looks up, the spelling a reader
  that believes those marks reads (`spelling-planner`)."
  nil)

(defn- spelling-opts
  "`sx/sentex`'s canonicalization reads in `kb` with predicate `p`'s marks restricted to the
  permuting-mark `entries`.  Every other functor, a compound's below the literal among
  them, is read by the marks the store sorts by.

  The groups are read unscoped: the fold decides the stored key, which every reader
  shares."
  [kb p entries]
  (let [tax (reasoning/taxonomy kb)]
    (assoc (store-marks kb)
           :symmetric? #(if (= p %)
                          (contains? entries [:prop :symmetric %])
                          (tax/has-prop? tax :symmetric %))
           :groups-of  (fn [f _arity] (if (= p f)
                                        (into #{} (filter #(contains? entries [:commuting f %]))
                                              (tax/commuting-groups tax f))
                                        (tax/commuting-groups tax f))))))

;; ---- an open application read through its corresponding predicate ----------
;; docs/nat.md, The corresponding predicate.  `kb-sentex` respells a rule here, below
;; `nat`, because every store and lookup builds its sentex through it.

(def correspondence-predicate
  "The declaration relating a NAT function to the predicate stating the same thing."
  'functionCorrespondingPredicate)

(defn any-corresponding-predicates?
  "Does the KB declare any `functionCorrespondingPredicate`?  One O(1) functor count."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) correspondence-predicate)))

(defn- visible-declarations
  "The believed correspondence declarations `context` sees, as sentexes: IN, and stated in
  `context`'s `genlCx` ancestor set (docs/nat.md, The corresponding predicate).  Every
  believed one when `context` is nil or a variable.  Read off the predicate extent and
  filtered in memory: the declarations are few, while an argument root holds every fact
  about the predicate.  `reads/believed-with-args` reads both arities in one probe."
  [kb context]
  (when (any-corresponding-predicates? kb)
    (let [tax  (reasoning/taxonomy kb)
          sees (if (and (symbol? context) (not (sx/variable? context)))
                 #(tax/sees? tax context (:context %))
                 (constantly true))]
      (->> (reads/believed-with-args kb correspondence-predicate {})
           (keep #(p/get-sentex (:records kb) %))
           (filter sees)))))

(defn believed-correspondences
  "The correspondence declarations `context` sees (`visible-declarations`) as `[function
  predicate position-or-nil]` triples, kept where `match?` holds of the triple."
  [kb context match?]
  (when (any-corresponding-predicates? kb)
    (->> (visible-declarations kb context)
         (map :sentence)
         (filter #(<= 3 (count %) 4))
         (map (fn [[_ f pr n]] [f pr (when (integer? n) n)]))
         distinct
         (filter match?))))

(defn correspondence-of
  "The `[predicate position]` declared for function `f` applied to `m` arguments among
  the declarations `context` sees (`believed-correspondences`), or nil.  `position`
  defaults to `m + 1`, the value last.  Nil when `context` sees more than one declaration
  for `f` (docs/nat.md, The corresponding predicate)."
  [kb f m context]
  (let [ds (believed-correspondences kb context #(= f (first %)))]
    (when (= 1 (count ds))
      (let [[_ pr n] (first ds)
            pos      (or n (inc m))]
        (when (and (symbol? pr) (<= 1 pos (inc m)))
          [pr pos])))))

(defn insert-at
  "`args` with `v` spliced in at 1-based `position`."
  [args position v]
  (let [i (dec position)]
    (concat (take i args) [v] (drop i args))))

(def ^:private application-constructs
  "The antecedent and consequent functors whose literal the respell does not enter: an
  open application under one leaves the rule as written."
  (into '#{unknown thereExists forall exists ist and or implies} (keys sx/aggregate-functors)))

(defn correspondence-declarations
  "The correspondence declarations `context` sees (`visible-declarations`) as `[function
  predicate position-or-nil handle]` rows, in content order of the declaration."
  [kb context]
  (when (any-corresponding-predicates? kb)
    (->> (visible-declarations kb context)
         (filter #(<= 3 (count (:sentence %)) 4))
         (map (fn [{[_ f pr n] :sentence h :id}] [f pr (when (integer? n) n) h]))
         (filter #(symbol? (second %)))
         (sort-by (fn [[f pr n h]] [(nm/print-key [f pr n]) h])))))

(defn- application-of?
  "Is `t` an open application of a function `reifiable?` accepts, not a quoting one?"
  [reifiable? t]
  (and (seq? t) (seq t) (symbol? (first t))
       (not (sx/quoting-functor? (first t)))
       (reifiable? (first t))
       (not (sx/ground-term? t))))

(defn- variable-application?
  "Is `t` an application whose functor is a variable, `(?fn AppleTree)`?  A dotted rest
  pattern, `(?pred . ?args)`, is a sentence pattern and is not one."
  [t]
  (and (seq? t) (< 1 (count t)) (sx/variable? (first t)) (not-any? #{'.} t)))

(defn- term-arguments
  "The arguments of compound `form` whose applications are terms: every one, except the
  proposition of an attitude (`attitude-application?` over the `modal_predicate`s
  `modal`), which is a mention, so only its agent is read."
  [modal form]
  (cond
    (and (seq? form) (attitude-application? modal form)) [(second form)]
    (seq? form) (rest form)
    :else form))

(defn- applications-in
  "The applications `app?` accepts in `form`, at any nesting, outermost first.  A quoting
  function's arguments, a quoting predicate's payload and a modal proposition
  (`term-arguments`) are mentions and are not read."
  [modal app? form]
  (when (and (sequential? form) (seq form)
             (not (sx/quoting-functor? (first form)))
             (not (contains? nat-quoting-predicates (first form))))
    (cond->> (mapcat #(applications-in modal app? %) (term-arguments modal form))
      (app? form) (cons form))))

(defn open-applications
  "The open applications of a function `reifiable?` accepts in `form`, at any nesting,
  outermost first, the propositions of the `modal_predicate`s `modal` unread
  (`applications-in`)."
  [modal reifiable? form]
  (applications-in modal #(application-of? reifiable? %) form))

(defn names-variable-application?
  "Does `form` hold a variable-functor application, `(?fn AppleTree)`, at any nesting
  outside a mention (`applications-in`)?"
  [modal form]
  (boolean (seq (applications-in modal variable-application? form))))

(defn formula-type?
  "Is `t` `formula` or a type under it?  Read unscoped, as `formula-position?` reads it."
  [kb t]
  (and (symbol? t) (not (sx/variable? t))
       (or (= 'formula t) (tax/genl?-global (reasoning/taxonomy kb) t 'formula))))

(defn formula-position?
  "Does a believed `arg`, `argN` or `quotedArg` declaration type position `n` of `pred`
  as a `formula` or a type under it, as `(arg ist 2 sentence)` does?  Read unscoped: a
  rule's stored spelling and its hold are one record every reader shares."
  [kb pred n]
  (and (symbol? pred) (not (sx/variable? pred))
       (let [recs     (:records kb)
             formula? #(formula-type? kb %)
             proj     (some (fn [[f k]] (when (= k n) f)) sx/arg-projections)
             decls    (fn [kind] (keep #(:sentence (p/get-sentex recs %))
                                       (reads/believed-with-args kb kind {1 pred})))]
         (boolean
          (or (some (fn [[_ _ k t]] (and (= n k) (formula? t)))
                    (concat (decls 'arg) (decls 'quotedArg)))
              (when proj (some (fn [[_ _ t]] (formula? t)) (decls proj))))))))

(defn reference-positions
  "A fn from a position of `pred` to whether its argument names a stored sentex by its
  content, or nil when no position does: each position a believed `quotedArg` or
  `quotedArgAndRest` declaration types `sentex_handle_term`, and, when `pred` is a
  `target_following_predicate`, each an `arg` or `argN` declaration types `sentence`.
  `except`'s target is one whatever the KB declares.  Each declaration kind is read only
  for a `pred` its taxonomy mark names.  Read unscoped, as `formula-position?` reads.  See
  docs/canonicalization.md, \"A reference to a stored sentex\"."
  [kb pred]
  (when (and (symbol? pred) (not (sx/variable? pred)))
    (let [recs    (:records kb)
          tax     (reasoning/taxonomy kb)
          decls   (fn [kind] (keep #(:sentence (p/get-sentex recs %))
                                   (reads/believed-with-args kb kind {1 pred})))
          marked  (fn [kind mark] (when (tax/has-prop? tax mark pred) (decls kind)))
          handle  (fn [[_ _ n t]] (when (= 'sentex_handle_term t) n))
          fixed   (cond-> (into #{} (keep handle) (marked 'quotedArg :declares-quoted-arg))
                    (= sx/except-functor pred) (conj 1)
                    (tax/has-prop? tax :target-following pred)
                    (-> (into (keep (fn [[_ _ n t]] (when (= 'sentence t) n))) (decls 'arg))
                        (into (keep (fn [[f n]] (when (some #(= 'sentence (nth % 2 nil)) (decls f)) n)))
                              sx/arg-projections)))
          from    (some->> (seq (keep handle (marked 'quotedArgAndRest :declares-quoted-arg-and-rest)))
                           (apply min))]
      (cond
        from         (fn [i] (or (contains? fixed i) (>= (long i) (long from))))
        (seq fixed)  fixed))))

(defn reference-term?
  "Is `a` an application of a function name (`nm/individual?`), other than a quoting one?
  Its arguments are read at the function's own `reference-positions`: the text writer and
  `assert-entry/resolve-references` descend into one at any argument position."
  [a]
  (and (seq? a) (seq a) (nm/individual? (first a)) (not (sx/quoting-functor? (first a)))))

(defn- respell-walk
  "The tests a respell in `kb` reads: `fixed?`, an open application of a
  `reifiable_function` (the mark read unscoped) or of a data-structure constructor
  (`built?`, `sx/structure-functions`); `app?`, that or a variable-functor
  application; `formula?`, `formula-position?` memoized for one respell; `modal`, the
  `modal_predicate`s, read unscoped (`tax/mention-marks`)."
  [kb]
  (let [tax    (reasoning/taxonomy kb)
        fixed? (fn [t] (application-of? #(or (tax/has-prop? tax :reifiable %)
                                             (contains? sx/structure-functions %))
                                        t))]
    {:modal    (:modal (tax/mention-marks tax))
     :built?   #(application-of? sx/structure-functions %)
     :fixed?   fixed?
     :app?     #(or (variable-application? %) (fixed? %))
     :formula? (memoize #(formula-position? kb %1 %2))}))

(defn- sentence-position?
  "Is 0-based index `i` of a literal on `pred` a sentence position: a construct's
  argument, or a `formula-position?`?"
  [{:keys [formula?]} pred i]
  (or (contains? application-constructs pred) (formula? pred (inc i))))

(defn- arg-app?
  "The application test for argument `a`, at 0-based index `i` of literal `l`: none for
  the proposition of an attitude (`attitude-application?`), whose applications stay as
  written (docs/nat.md, The corresponding predicate); `fixed?` where a variable-functor
  compound is a sentence pattern (`sentence-position?`); `app?` elsewhere."
  [{:keys [app? fixed? modal] :as walk} l i a]
  (cond
    (and (= 1 i) (attitude-application? modal l))                 (constantly false)
    (and (seq (applications-in modal variable-application? a))
         (sentence-position? walk (first l) i))                    fixed?
    :else                                                          app?))

(defn rule-form?
  "Is `l` a rule, its wrappers peeled: a generator's consequent, whose applications the
  rule it generates reads when it is stored?"
  [l]
  (sx/implies? (peek (sx/peel-rule-wrapper l))))

(defn- some-argument?
  "Does `(hit? walk l i a)` hold for an argument `a`, at 0-based index `i`, of literal
  `l`, or of the literal a `not` in `l` wraps?  `walk` is `respell-walk`'s,
  built on first use.  A rule `l` (`rule-form?`) and a quoting predicate's literal are
  not read."
  [kb hit? l]
  (let [walk (delay (respell-walk kb))]
    (letfn [(holds? [l]
              (cond
                (not (and (seq? l) (seq l)))                  false
                (rule-form? l)                                false
                (contains? nat-quoting-predicates (first l))  false
                (and (= 'not (first l)) (= 2 (count l)))      (holds? (second l))
                :else (boolean (some (fn [[i a]] (hit? walk l i a))
                                     (map-indexed vector (rest l))))))]
      (holds? l))))

(defn holds-variable-application?
  "Does literal `l` hold a variable-functor application outside a sentence position
  (`arg-app?`): one a stored rule leaves as written?"
  [kb l]
  (some-argument? kb
                  (fn [walk l i a]
                    (and (seq (applications-in (:modal @walk) variable-application? a))
                         (= (:app? @walk) (arg-app? @walk l i a))))
                  l))

(defn names-no-match?
  "Does literal `l` hold `sx/no-match` at a term position, at any depth: an argument, or
  inside an application at one?  An argument at a `sentence-position?` is a literal of
  its own, read when its prover reads it."
  [kb l]
  (and (sx/some-symbol? #(= sx/no-match %) l)
       (some-argument? kb
                       (fn [walk l i a]
                         (and (or (= sx/no-match a)
                                  (seq (applications-in (:modal @walk) #(some #{sx/no-match} (rest %)) a)))
                              (not (sentence-position? @walk (first l) i))))
                       l)))

(defn- application-variable
  "A variable named for `application`: `?`, the function's name with its `Fn` suffix
  dropped and its first letter lowercased (a variable functor's name as it is), then
  `suffix`, with a hash of `application` appended where `used` holds it already."
  [application suffix used]
  (let [f    (first application)
        n    (if (sx/variable? f) (subs (name f) 1) (name f))
        n    (if (and (str/ends-with? n "Fn") (< 2 (count n))) (subs n 0 (- (count n) 2)) n)
        base (str "?" (str/lower-case (subs n 0 1)) (subs n 1) suffix)]
    (->> (iterate #(str % "-" (Integer/toString (bit-and (hash application) 0x7fffffff) 36))
                  base)
         (map symbol)
         (remove used)
         first)))

(defn- declared-position
  "The value position declaration row `[f pr n h]` gives an application of `m` arguments,
  or nil when it is out of range."
  [[_ _ n _] m]
  (let [pos (or n (inc m))]
    (when (<= 1 pos (inc m)) pos)))

(defn- rule-readings
  "The readings of an application of `f` to `m` arguments in a rule, under declaration
  rows `decls`: one `{:pred :pos :decls}` per distinct believed `[predicate position]`, in
  content order, `:decls` the handles declaring it.  None for a variable functor."
  [decls f m]
  (if (sx/variable? f)
    []
    (->> decls
         (filter #(= f (first %)))
         (keep (fn [d] (when-let [pos (declared-position d m)] [[(second d) pos] (peek d)])))
         (group-by first)
         (map (fn [[[pr pos] ds]] {:pred pr :pos pos :decls (mapv second ds)}))
         (sort-by #(nm/print-key [(:pred %) (:pos %)]))
         vec)))

(defn- goal-readings
  "The readings of an application of `f` to `m` arguments in a goal: `rule-readings`'
  one where `f` has exactly one and the goal reads at one context (`scoped?`), and
  otherwise one `{:functor :n :pos}` per distinct declaration shape among `f`'s
  declarations `decls` (every function's, for a variable `f`), read through a predicate
  variable, so each reader matches the declarations it sees."
  [decls scoped? f m]
  (let [direct (rule-readings decls f m)]
    (if (and scoped? (= 1 (count direct)))
      direct
      (->> decls
           (filter #(or (sx/variable? f) (= f (first %))))
           (keep (fn [d] (when-let [pos (declared-position d m)] {:functor f :n (nth d 2) :pos pos})))
           distinct
           (sort-by #(nm/print-key [(:n %) (:pos %)]))
           vec))))

(defn- reading-literals
  "The literals stating `v` is the value of an application to `args` under `reading`;
  `pv` is the predicate variable a declaration shape reads through."
  [reading args v pv]
  (if-let [pr (:pred reading)]
    [(apply list pr (insert-at args (:pos reading) v))]
    [(apply list (cond-> [correspondence-predicate (:functor reading) pv]
                   (:n reading) (conj (:n reading))))
     (apply list pv (insert-at args (:pos reading) v))]))

(defn- take-reading!
  "The literals stating `v` is the value of application `t'` to `args`, under the reading
  `state`'s `:choice` picks for it, or nil when `readings` gives it none.  Records the
  reading count in `:counts` and the declaring handles in `:decls`."
  [readings state t' args v]
  (let [rs (readings (first t') (count args))
        i  (count (:counts @state))]
    (vswap! state update :counts conj (count rs))
    (when (seq rs)
      (let [r  (nth rs (get (:choice @state) i 0))
            pv (when-not (:pred r) (application-variable t' "Predicate" (:used @state)))]
        (vswap! state #(-> % (update :used into (filter sx/variable?) [v pv])
                           (update :decls conj (:decls r [nil]))))
        (reading-literals r args v pv)))))

(defn- respell-term
  "`t` with each application `app?` accepts in it, innermost first, replaced by its value
  variable; `state` (a volatile `{:vars {application var} :used #{var} :hoisted [lit]
  :choice [k] :counts [n] :decls [[handle]]}`) gathers the literals of each
  (`take-reading!`).  The proposition of an attitude over the `modal_predicate`s `modal`
  stays as written.  Nil when an application has no reading."
  [modal app? readings state t]
  (if (and (seq? t) (seq t) (not (sx/quoting-functor? (first t))))
    (let [modal? (attitude-application? modal t)
          args   (doall (map-indexed #(if (and modal? (= 1 %1)) %2 (respell-term modal app? readings state %2))
                                     (rest t)))]
      (when (every? some? args)
        (let [t' (apply list (first t) args)]
          (if-not (app? t')
            t'
            (or (get-in @state [:vars t'])
                (let [v (application-variable t' (if (sx/variable? (first t')) "Value" "") (:used @state))]
                  (when-let [lits (take-reading! readings state t' args v)]
                    (vswap! state #(-> % (assoc-in [:vars t'] v) (update :hoisted into lits)))
                    v)))))))
    t))

(defn- respell-literal
  "Literal `l` with its applications replaced (`respell-term`), under a `not` too, as a
  vector of literals, or nil when it cannot be: an application with no reading, or a
  construct holding a reifiable one.  `(equals x (F a…))`, either way round, is the
  reading's own literals with `x` the value, and `x` is the application's value in
  `state`.  A rule `l` is returned as it is (`rule-form?`), and a deferred `l` keeps a
  data structure as written: it computes from the value its bindings build."
  [walk readings state l]
  (cond
    (or (not (and (seq? l) (seq l))) (rule-form? l) (contains? nat-quoting-predicates (first l)))
    [l]
    (and (= 'not (first l)) (= 2 (count l)))
    (let [inner (respell-literal walk readings state (second l))]
      (when (= 1 (count inner)) [(list 'not (first inner))]))
    :else
    (let [pr  (first l)
          as  (vec (rest l))
          a?s (cond->> (vec (map-indexed #(arg-app? walk l %1 %2) as))
                (sx/deferred-literal? l) (mapv (fn [a?] #(and (a? %) (not ((:built? walk) %))))))
          app (:app? walk)
          rt  (partial respell-term (:modal walk))]
      (cond
        (not (some seq (map #(applications-in (:modal walk) %1 %2) a?s as))) [l]
        (contains? application-constructs pr) nil
        (and (= 'equals pr) (= 2 (count as)) (not= (boolean (app (as 0))) (boolean (app (as 1)))))
        (let [[a x] (if (app (as 0)) as (rseq as))
              args  (doall (map #(rt app readings state %) (rest a)))
              x'    (rt app readings state x)]
          (when (and x' (every? some? args))
            (let [t' (apply list (first a) args)]
              (vswap! state update :vars #(cond-> % (not (contains? % t')) (assoc t' x')))
              (take-reading! readings state t' args x'))))
        :else (let [args (doall (map #(rt %1 readings state %2) a?s as))]
                (when (every? some? args) [(apply list pr args)]))))))

(defn- readings-of
  "Every reading `f` gives, `[[result decls] …]`: the first takes each application's first
  reading, the rest every other combination.  `f` takes the state volatile
  `respell-term` reads, seeded with `used`, and answers nil when a literal cannot be
  respelled; then this is nil."
  [used f]
  (let [run     (fn [choice]
                  (let [state (volatile! {:vars {} :used used :hoisted [] :choice choice
                                          :counts [] :decls []})]
                    [(f state) @state]))
        [r0 s0] (run [])]
    (when (some? r0)
      (into [[r0 (:decls s0)]]
            (map (fn [c] (let [[r s] (run c)] [r (:decls s)])))
            (rest (reduce (fn [acc n] (for [c acc k (range n)] (conj c k))) [[]] (:counts s0)))))))

(defn- justification-sets
  "Every set of declaring handles a combination's `decls` (one handle vector per
  application) reads, one handle per application, sorted."
  [decls]
  (into [] (comp (map #(vec (sort (remove nil? %)))) (distinct))
        (reduce (fn [acc hs] (for [a acc h hs] (conj a h))) [[]] decls)))

(defn- substitute-bound
  "`form` with each application the antecedents' respell gave a value (`state`'s
  `:vars`) replaced by it, innermost first; every other application left as written.  A
  quoting function's arguments, a quoting predicate's payload and the proposition of an
  attitude over the `modal_predicate`s `modal` are mentions and are left alone."
  [modal state form]
  (if (and (seq? form) (seq form)
           (not (sx/quoting-functor? (first form)))
           (not (contains? nat-quoting-predicates (first form))))
    (let [modal? (attitude-application? modal form)
          f'     (apply list (first form)
                        (map-indexed #(if (and modal? (= 1 %1)) %2 (substitute-bound modal state %2))
                                     (rest form)))]
      (get-in @state [:vars f'] f'))
    form))

(defn- hoisted-order
  "The literals a respell `hoisted` from antecedents `antes`, in the order they can run
  once the generators have bound their variables: a structure's corresponding-predicate
  literal reads it before the one that reads a structure inside it.  A literal that never
  can stays last, for `sx/check-naf-closed` to name."
  [antes hoisted]
  (loop [pending (vec hoisted)
         bound   (into #{} (mapcat sx/form-variables) (remove sx/deferred-literal? (concat antes hoisted)))
         acc     []]
    (if-let [l (first (filter #(every? bound (sx/deferred-input-vars % bound)) pending))]
      (recur (let [i (.indexOf ^java.util.List pending l)] (into (subvec pending 0 i) (subvec pending (inc i))))
             (into bound (sx/form-variables l))
             (conj acc l))
      (into acc pending))))

(defn- respell-rule
  "The `implies` form `r` with every open application in its antecedents respelled under
  `state`'s choice, the literals stating the values added ahead of its deferred ones
  (`hoisted-order`); `r` itself when nothing changed, nil when one cannot be respelled.
  The consequent stays as written, except that an application the antecedents give a
  value takes it (`substitute-bound`): a firing mints the rest (docs/nat.md, The
  corresponding predicate).  A generator's consequent rule is left whole (`rule-form?`)."
  [walk readings state r]
  (let [antes0 (vec (sx/rule-antecedents r))
        conseq (sx/rule-consequent r)
        antes  (mapv #(respell-literal walk readings state %) antes0)]
    (when (every? some? antes)
      (let [antes  (into [] cat antes)
            antes' (into (hoisted-order antes (:hoisted @state)) antes)
            c      (if (rule-form? conseq) conseq (substitute-bound (:modal walk) state conseq))]
        (if (and (= antes' antes0) (= c conseq))
          r
          (sx/rule-sentence antes' c))))))

(defn- map-inner-rule
  "`form` with `f` applied to the `implies` form its rule wrappers enclose, the wrappers
  kept; `form` unchanged when it is no rule."
  [f form]
  (cond
    (sx/implies? form) (f form)
    (not (and (seq? form) (seq form))) form
    (and (= sx/except-wrapper (first form)) (= 3 (count form)) (not (sx/exceptWhen-meta? form)))
    (list (first form) (second form) (map-inner-rule f (nth form 2)))
    (and (= 2 (count form))
         (or (contains? sx/rule-direction-wrappers (first form))
             (contains? sx/constraint-rule-wrappers (first form))
             (contains? #{sx/default-rule-wrapper sx/assumption-rule-wrapper sx/solve-rule-wrapper}
                        (first form))))
    (list (first form) (map-inner-rule f (second form)))
    :else form))

(defn- without-applications
  "Literal `l` with each outermost application `arg-app?` accepts in its arguments, under
  a `not` too, replaced by `v`."
  [walk v l]
  (letfn [(sub [a? form]
            (cond
              (a? form) v
              (and (seq? form) (seq form) (not (sx/quoting-functor? (first form))))
              (apply list (first form) (map #(sub a? %) (rest form)))
              :else form))]
    (cond
      (or (not (and (seq? l) (seq l))) (contains? nat-quoting-predicates (first l))) l
      (and (= 'not (first l)) (= 2 (count l))) (list 'not (without-applications walk v (second l)))
      :else (apply list (first l) (map-indexed #(sub (arg-app? walk l %1 %2) %2) (rest l))))))

(defn goal-alternatives
  "Conjunction `goals` read through the correspondence declarations `context` sees, as the
  vector of conjunctions whose answers the reader merges (docs/nat.md, The corresponding
  predicate).  A nil or variable `context` reads every declaration through a predicate
  variable (`goal-readings`).  An application with one believed correspondence reads its
  predicate; with several, or a variable-functor application outside a sentence position
  (`arg-app?`), one conjunction per distinct declaration shape.  An `and` goal is read as
  its conjuncts.  An application with no reading becomes `unmatched`, so the conjunction
  answers nothing.  The reifiable mark is read unscoped."
  [kb goals unmatched context]
  (let [walk (respell-walk kb)
        app  (:app? walk)]
    (if (not-any? #(and (seq? %) (some (fn [a] (seq (applications-in (:modal walk) app a)))
                                       (term-arguments (:modal walk) %)))
                  goals)
      [goals]
      (let [goals (into [] (mapcat (fn conjuncts [g] (if (and (seq? g) (= 'and (first g)))
                                                       (mapcat conjuncts (rest g))
                                                       [g])))
                        goals)
            decls   (delay (correspondence-declarations kb context))
            scoped? (and (symbol? context) (not (sx/variable? context)))
            rs    (readings-of (sx/form-variables goals)
                               (fn [state]
                                 (let [gs (mapv #(respell-literal walk (fn [f m] (goal-readings @decls scoped? f m))
                                                                  state %)
                                                goals)]
                                   (when (every? some? gs)
                                     (into (:hoisted @state) cat gs)))))]
        (if (seq rs)
          (into [] (comp (map first) (distinct)) rs)
          [(mapv #(without-applications walk unmatched %) goals)])))))

(def ^:dynamic *as-written*
  "While true, `kb-sentex` leaves a rule's open applications as written: the spelling
  `assert` records as a premise's written one (`integrate/spellings-key`)."
  false)

(defn rule-respellings
  "Every spelling of rule `sentence` its antecedents' open `reifiable_function` and
  data-structure applications read through the believed correspondences, as
  `[[spelling handle-sets] …]` (`respell-rule`; the consequent stays as written).  The
  first takes each function's content-least correspondence and is the one `kb-sentex`
  stores; `chain/sync-rule-respellings!` stores the rest.  Nil when `sentence` is no rule
  or no antecedent has a reading (docs/nat.md, The corresponding predicate)."
  [kb sentence context]
  (when (and (not *as-written*) (seq? sentence)
             (or (seq (tax/props (reasoning/taxonomy kb) :reifiable))
                 (sx/some-symbol? sx/structure-functions sentence)))
    (let [inner (volatile! nil)]
      (map-inner-rule #(vreset! inner %) sentence)
      (when-let [r @inner]
        (let [walk (respell-walk kb)]
          (when (some #(seq (applications-in (:modal walk) (:fixed? walk) %)) (sx/rule-antecedents r))
            (let [decls (delay (correspondence-declarations kb context))]
              (some->> (readings-of (sx/form-variables r)
                                    #(respell-rule walk (fn [f m] (rule-readings @decls f m)) % r))
                       (mapv (fn [[r' ds]]
                               [(map-inner-rule (constantly r') sentence) (justification-sets ds)]))
                       ;; a deferred literal's data structure alone leaves the rule as written
                       (remove (fn [[r' _]] (= r' sentence)))
                       not-empty
                       vec))))))))

(defn respell-applications
  "Rule `sentence` as `kb-sentex` stores it in `context`: the first of
  `rule-respellings`, or `sentence` unchanged when that is nil."
  [kb sentence context]
  (or (ffirst (rule-respellings kb sentence context)) sentence))

(defn kb-sentex
  "Build a sentex canonicalized against this KB's taxonomy: a symmetric predicate's
  arguments are sorted, so `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)` become one
  sentex, and the commutativity marks sort a declared set of positions at any arity
  (`tax/commuting-groups`; `store-marks`, docs/canonicalization.md).  Every construction
  that stores or looks one up goes through this.  The property read is global; while
  `*spelled-by*` names this sentence's predicate and context, only the marks it lists
  apply (`spelling-planner`).  A rule's open applications are read through their
  corresponding predicates first (`respell-applications`)."
  [kb sentence context]
  (let [[p ctx entries] *spelled-by*]
    (sx/sentex (respell-applications kb sentence context) context
               (if (and p (= ctx context) (= p (permuted-functor sentence)))
                 (spelling-opts kb p entries)
                 (store-marks kb)))))

;; ---- a permuting mark read per reader --------------------------------------
;;
;; The reads that decide which spelling a reader sees of a fact stored under a mark it does not
;; believe: docs/canonicalization.md, "A mark a reader does not believe".

(defn mark-entries
  "The permuting marks the store sorts `pred` by, as `{entry {handle context}}`: the
  `symmetric` entry `[:prop :symmetric pred]` and one `[:commuting pred group]` per
  commuting group, each with its supporters.  Empty for a predicate nothing permutes."
  [tax pred]
  (let [t @tax]
    (cond-> (into {} (map (fn [g] (let [k [:commuting pred g]] [k (tax/supporters tax k)])))
                  (get (:commuting t) pred))
      (contains? (get-in t [:props :symmetric]) pred)
      (assoc [:prop :symmetric pred] (tax/supporters tax [:prop :symmetric pred])))))

(defn- held-everywhere?
  "Is supporter `h` believed at every reader: IN, and no placed `defeat` or `except` can
  hide it anywhere (`exc/defeated-anywhere?`, `exc/closure-excepted-anywhere?`)?"
  [kb h]
  (and (jtms/in? (reasoning/tms kb) h)
       (not (exc/defeated-anywhere? kb h))
       (not (exc/closure-excepted-anywhere? kb h))))

(defn uniform-marks?
  "Does every reader believe every mark in `entries` (`mark-entries`): each has a
  supporter `held-everywhere?`?  The four permuting marks are read from every context
  (docs/contexts.md, \"A context outside the topology\"), so only a defeat or an except
  makes two readers read one fact differently."
  [kb entries]
  (every? (fn [[_ sup]] (some #(held-everywhere? kb %) (keys sup))) entries))

(defn- split-mention-at
  "`(fn [f n])`: is position `n` of `f` a mention the store keeps as written that a reader
  may not read as one, since no declaration typing it is stated in CxUniverse and
  `held-everywhere?`?"
  [kb tax]
  (fn [f n]
    (let [ds (mention-declarations kb tax f n)]
      (boolean (and (seq ds)
                    (not-any? #(and (= sx/root-context (:context %)) (held-everywhere? kb (:id %)))
                              ds))))))

(defn declares-mention?
  "Does the taxonomy mark `f` as declaring a `quotedArg` or `quotedArgAndRest` position?
  Read unscoped, a superset `split-mention-at` and `without-unread-mentions` narrow per
  reader."
  [tax f]
  (or (tax/has-prop? tax :declares-quoted-arg f) (tax/has-prop? tax :declares-quoted-arg-and-rest f)))

(defn- applies-declared-mention?
  "Does `sentence` hold an application with a compound argument whose functor the taxonomy
  marks as declaring a mention: the only positions `sx/mention-arrangements` probes?"
  [tax sentence]
  (boolean (some (fn [t] (and (seq? t) (symbol? (first t))
                              (some #(and (seq? %) (seq %)) (rest t))
                              (declares-mention? tax (first t))))
                 (tree-seq seq? seq sentence))))

(defn mention-probes
  "The spellings of literal `sentence` beyond itself that a read probes for a fact stored
  under a mention some reader does not read (`split-mention-at`):
  `sx/mention-arrangements`, the rest of each in the store's order (`probe-spelling`).
  Empty when no functor applied to a compound in `sentence` declares a mention."
  [kb sentence]
  (let [tax (reasoning/taxonomy kb)]
    (if (and (seq? sentence) (applies-declared-mention? tax sentence))
      (into [] (comp (map #(probe-spelling kb %)) (distinct) (remove #{sentence}))
            (rest (sx/mention-arrangements sentence (store-marks kb) (split-mention-at kb tax))))
      [])))

(defn- fan-mention-probes
  "The spellings a read of literal `sentence` from `view-context` probes for a row of a
  predicate its fan reads (`fan-closure`, swapped members with arguments 1 and 2
  exchanged) other than its own functor that declares a mention: that predicate's literal
  in every order of each compound at a position it declares (`sx/mention-arrangements`),
  since the store keeps such a compound as written.  Empty when no fan member declares one.
  The declarations are read unscoped, a superset `without-unread-mentions` narrows per
  reader."
  [kb sentence view-context]
  (let [tax  (reasoning/taxonomy kb)
        neg? (sx/negation? sentence)
        body (if neg? (second sentence) sentence)
        f    (when (seq? body) (first body))
        decl (into (tax/props tax :declares-quoted-arg) (tax/props tax :declares-quoted-arg-and-rest))]
    (if-not (and (seq decl) (symbol? f) (not (sx/variable? f))
                 (some #(and (seq? %) (seq %)) (rest body)))
      []
      (let [ctx       (when (and (symbol? view-context) (not (sx/variable? view-context))) view-context)
            [fan swp] (fan-closure kb (if neg? :up :down) f ctx)
            marks     (store-marks kb)
            spell     (fn [g args]
                        (let [lit (apply list g args)]
                          (rest (sx/mention-arrangements (if neg? (list sx/not-functor lit) lit) marks
                                                         (fn [h _] (= h g))))))]
        (into [] (comp (map #(probe-spelling kb %)) (distinct) (remove #{sentence}))
              (concat (for [g (sort-by nm/name-key decl) :when (and (not= g f) (contains? fan g))
                            p (spell g (rest body))]
                        p)
                      (when (= 3 (count body))
                        (for [g (sort-by nm/name-key decl) :when (contains? swp g)
                              p (spell g (reverse (rest body)))]
                          p))))))))

(defn entries-at
  "The entries of `entries` some supporter of which `reader` believes
  (`supporter-believed?`), as a set."
  [kb entries reader]
  (into #{} (keep (fn [[k sup]] (when (some #(supporter-believed? kb % reader) (keys sup)) k)))
        entries))

(defn- hider-contexts
  "The contexts stating a `defeat` or an `except` whose target lies in the support of one
  of `handles`, and the contexts stating an `except` whose target lies in the support of
  one of those: the contexts whose visibility can change whether a reader believes a
  supporter in `handles`."
  [kb handles]
  (let [tms   (reasoning/tms kb)
        idx   (:index kb)
        named (fn [functors hs]
                (for [h hs, t (exc/support tms h (constantly false)), f functors
                      e (reads/as-stored-naming-by-context idx f t)]
                  e))
        one   (named [sx/except-functor sx/defeat-functor] handles)]
    (into #{} (map first) (concat one (named [sx/except-functor] (into #{} (mapcat second) one))))))

(defn spelling-readers
  "The readers whose spellings of a fact stated in `context` can differ, given the
  supporters `handles` of its predicate's marks: `context` and the contexts where it meets
  the contexts that state a hiding `defeat` or `except` (`hider-contexts`,
  `tax/meet-closure`), kept where they see `context`.  A reader below `context` sees one
  of these sets of hiders, so it reads as one of them does."
  [kb context handles]
  (let [tax (reasoning/taxonomy kb)]
    (filterv #(tax/sees? tax % context)
             (tax/meet-closure tax (conj (hider-contexts kb handles) context)))))

(defn spelling-planner
  "`(fn [sentence context])` answering `{spelling entries}`: each spelling the readers of
  `sentence`, written in `context`, read it in, with the marks that reader believes, or
  nil when every reader believes every mark that sorts it (`uniform-marks?`) and so reads
  the store's own spelling.  The fn holds for its own lifetime
  one memo of each predicate's marks and whether they are uniform, and one of each
  `[predicate context]`'s readers: a walk over a predicate's rows reads both once."
  [kb]
  (let [tax  (reasoning/taxonomy kb)
        ents (memoize (fn [p] (let [e (mark-entries tax p)]
                                (when (and (seq e) (not (uniform-marks? kb e))) e))))
        rdrs (memoize (fn [p ctx]
                        (let [e (ents p)]
                          (into [] (comp (map #(entries-at kb e %)) (distinct))
                                (spelling-readers kb ctx (into [] (mapcat (comp keys val)) e))))))]
    (fn [sentence context]
      (when-let [p (permuted-functor sentence)]
        (when (ents p)
          (into {} (map (fn [e] [(sx/sentence-of (sx/sentex sentence context (spelling-opts kb p e))) e]))
                (rdrs p context)))))))

(defn reader-spelled-by
  "The `*spelled-by*` binding that spells `sentence` as `reader` reads it, or nil when the
  store's own spelling is the reader's."
  [kb sentence reader]
  (when (and (symbol? reader) (not (sx/variable? reader)))
    (let [tax  (reasoning/taxonomy kb)
          p    (permuted-functor sentence)
          ents (when p (mark-entries tax p))]
      (when (and (seq ents) (not (uniform-marks? kb ents)))
        [p reader (entries-at kb ents reader)]))))

(def ^:dynamic *prefetch-candidates*
  "Candidate handles per prefetch hint a retrieval path gives its record store, or `false`
  (the default) to give none.  On, a walk takes candidates a chunk at a time and tells a
  store implementing `protocols/Prefetching` which handles the chunk will ask for.  The
  hint returns nothing and every record still arrives through `get-sentex`, so this is a
  cost setting.  It pays over a non-local fetch only; the signal is a large `:fetches`
  tally (`vaelii.impl.profile`) against wall clock.  The chunk is the unit of over-fetch.
  `false` or a positive integer; anything else, `true` above all, is refused where it is
  bound."
  false)

;; Refused at the `binding` form, the only place the wrong value is legible: `true` is truthy and
;; would otherwise reach `(long n)` in `cap/hinting` as a ClassCastException inside a lazy seq.
(set-validator!
 #'*prefetch-candidates*
 (fn [v]
   (or (false? v)
       (and (integer? v) (pos? v))
       (throw (ex-info (str "*prefetch-candidates* is a positive chunk size, or `false` to "
                            "hint nothing — not " (pr-str v))
                       ;; `:unknown-option`, as `vaelii.impl.config` refuses a switch outside its domain.
                       {:type     :unknown-option :mismatch :bad-value
                        :setting  'vaelii.impl.resolution/*prefetch-candidates*
                        :value    v
                        :expected "false, or a positive integer (256 is the measured plateau)"})))))

(defn- hinting
  "`cands` unchanged, with a prefetch hint issued a chunk ahead of the walk when
  `*prefetch-candidates*` is set and the record store can act on one.  Same handles, same
  order, lazy at chunk granularity, so a consumer that stops at the first solution hints
  one chunk.  The belief filter runs before the hint so the store never warms a record the
  walk skips; the walk tests belief again, a RAM read.  Both retrieval paths
  (`matches-hierarchical` and `match-one`'s fan-out) wrap their candidates here."
  [kb cands]
  (let [pf     (when *prefetch-candidates* (cap/prefetcher (:records kb)))
        tms    (reasoning/tms kb)
        blind? (belief-blind?)]
    (cap/hinting (when pf (fn [chunk] (pf (filterv #(or blind? (jtms/in? tms %)) chunk))))
                 (or *prefetch-candidates* 1)
                 cands)))

(defn- match-one
  "Matches are belief-sensitive: a handle stored but currently OUT does not match.  Yields
  `[handle bindings stored-sentex]`; the record is fetched to unify against, so it rides
  along.  Lazy: one solution costs one `get-sentex` (one chunk's hint under
  `*prefetch-candidates*`)."
  [kb sentence context]
  (let [pat   (kb-sentex kb sentence context)
        tms   (reasoning/tms kb)
        recs  (:records kb)
        blind? (belief-blind?)
        ;; a rule-shaped pattern matches a stored rule's whole `implies` form, which a
        ;; rule record does not hold, so both sides are built once here or per candidate;
        ;; a literal pattern reads the stored `:sentence` straight, as every fact is
        rule-pat? (some? (:antecedent pat))
        psent (sx/sentence-of pat)
        pneg? (sx/negative? pat)
        match (fn [h]
                (when (or blind? (jtms/in? tms h))
                  (let [stored (p/get-sentex recs h)]
                    ;; An exceptWhen meta-sentex is the one non-ground stored Literal and bookkeeping, not a fact; skipping
                    ;; it keeps trie and argument-root retrieval in agreement (`provers/rule-exceptions` reads it).
                    (when (and (not (sx/exceptWhen-meta? (:sentence stored)))
                               ;; match polarity: `(?p ?x)` must not bind `?p` to `not` against a stored negation.
                               (= pneg? (sx/negative? stored)))
                      (when-let [b (unify (:context pat) (:context stored)
                                          (unify psent (if rule-pat?
                                                         (sx/sentence-of stored)
                                                         (:sentence stored))))]
                        [h b stored])))))
        ;; a superset of the trie hits when an argument root is tighter than a
        ;; leading-variable fan-out; the unify above filters it to the same set
        cands (candidate-handles kb pat)]
    (keep match (hinting kb cands))))

(defn raw-match-with
  "Match a literal by `probe` (`(probe form)` → a seq of `[handle bindings …]`, one literal
  context) over every argument arrangement the predicate licences: the mirror for a
  symmetric predicate, the other arrangements of the commuting component for a commutative
  one.  This makes lookup order-insensitive, including a fact asserted before its
  `symmetric` declaration.  Deduped by handle and bindings: `(sibOf ?a ?b)` over a stored
  `(sibOf Rex Tib)` binds both ways round, two answers about one handle.  Lazy through the
  fan, over each spelling `nested-probes` gives.  `raw-match` calls it with `match-one`,
  the rete alpha matcher with its memory probe.  The `symmetric` mark is read unscoped."
  [kb probe sentence]
  (let [tax      (reasoning/taxonomy kb)
        sentence (probe-spelling kb sentence)
        hits     (probe sentence)
        ;; the global property, as kb-sentex reads it — the mirror probe exists because
        ;; storage sorted the arguments; a reader that does not believe the mark has the
        ;; mirror dropped by `without-unbelieved-spellings`
        own    (fn [s]
                 (if (sx/symmetric-literal? s #(tax/has-prop? tax :symmetric %))
                   [(sx/mirror-literal s)]
                   ;; The declaration read comes first so an unmarked predicate pays one map lookup and builds no
                   ;; closure; `rest` is the fan-out.
                   (let [f (when (sequential? s) (first s))]
                     (when (and (symbol? f) (seq (tax/commuting-groups tax f)))
                       (rest (sx/commuting-arrangements
                              s (fn [g _] (tax/commuting-groups tax g))))))))
        nested (rest (nested-probes kb sentence))
        others (if (seq nested)
                 (into [] (comp (distinct) (remove #{sentence}))
                       (concat (own sentence) (mapcat #(cons % (own %)) nested)))
                 (own sentence))]
    (if (seq others)
      (letfn [(step [forms seen]
                (when-let [form (first forms)]
                  (let [hs (remove (fn [[h b]] (contains? seen [h b])) (probe form))]
                    (if (next forms)
                      (concat hs (lazy-seq
                                  (step (rest forms)
                                        (into seen (map (fn [[h b]] [h b])) hs))))
                      hs))))]
        (lazy-cat hits (step others (into #{} (map (fn [[h b]] [h b])) hits))))
      hits)))

(defn- as-written-probe
  "The predicate of ground literal `sentence` when some reader may read it as written
  where the store sorts it (`uniform-marks?` false, and the sort moves it), else nil."
  [kb sentence context]
  (when-let [p (permuted-functor sentence)]
    (when (and (not (sx/variable? context)) (sx/ground-term? sentence))
      (let [ents (mark-entries (reasoning/taxonomy kb) p)]
        (when (and (seq ents) (not (uniform-marks? kb ents))
                   (not= sentence (sx/sentence-of (kb-sentex kb sentence context))))
          p)))))

(defn raw-match
  "Match a literal in one **literal** context — no genlCx inheritance, no subtype
  fan-out — over every argument arrangement its predicate licences (`raw-match-with`),
  probing the stored index with `match-one`.  Yields `[handle bindings stored-sentex]`."
  [kb sentence context]
  (let [ms (raw-match-with kb #(match-one kb % context) sentence)]
    (if-let [p (as-written-probe kb sentence context)]
      ;; the row a reader that does not believe the mark reads sits at the written
      ;; spelling, which the sort moves a ground probe off (`without-unbelieved-spellings`
      ;; keeps the one each reader reads)
      (lazy-cat ms (let [seen (into #{} (map (fn [[h b]] [h b])) ms)]
                     (remove (fn [[h b]] (contains? seen [h b]))
                             (binding [*spelled-by* [p context #{}]]
                               (doall (match-one kb sentence context))))))
      ms)))

(defn- read-spelling
  "The fact `goal` reads stored literal `stored` as under bindings `b`: `stored`'s functor
  over the goal's arguments, so a match reached through an argument arrangement reads the
  arrangement.  `stored` itself when the two do not line up."
  [goal b stored]
  (let [g     (substitute goal b)
        neg?  (= 'not (first stored))
        inner #(if (and (seq? %) (= 'not (first %))) (second %) %)
        s     (inner stored)
        gi    (inner g)]
    (if (and (sequential? s) (sequential? gi) (= (count s) (count gi)))
      (let [r (apply list (first s) (rest gi))] (if neg? (list 'not r) r))
      stored)))

(defn- reified-reading
  "`(fn [sentence])` answering whether `view-context` reads stored `sentence` in another
  spelling under a `reifiable_function` mark some reader does not believe: it names a
  constant minted for a function the reader does not believe reifiable, or holds an
  application of one it does, outside a `natFormula` or `rewriteOf` payload.  Nil when
  every reader believes every such mark.

  The marks are read unscoped, a superset that the per-reader test narrows to
  `view-context`."
  [kb view-context]
  (let [tax   (reasoning/taxonomy kb)
        ents  (fn [f] (let [k [:prop :reifiable f]] {k (tax/supporters tax k)}))
        split (into {} (keep (fn [f] (let [e (ents f)]
                                       (when (and (seq (val (first e))) (not (uniform-marks? kb e)))
                                         [f (boolean (seq (entries-at kb e view-context)))]))))
                    (tax/props tax :reifiable))]
    (when (seq split)
      (let [minted (memoize (fn [k] (some (fn [[_ _ st]] (let [e (nth (:sentence st) 2 nil)]
                                                           (when (sequential? e) (first e))))
                                          (raw-match kb (list 'natFormula k '?e) 'CxUniverse))))
            other? (fn other? [form]
                     (cond
                       (symbol? form) (and (namespace form)
                                           (false? (get split (minted form))))
                       (sequential? form)
                       (let [f (first form)]
                         (or (and (true? (get split f)) (sx/ground-term? form))
                             (and (not (contains? '#{natFormula rewriteOf} f))
                                  (boolean (some other? form)))))
                       :else false))]
        other?))))

(defn without-unbelieved-spellings
  "Drop the matches of `goal` whose spelling `view-context` does not read: a row stored as
  written that the marks the reader believes sort otherwise, a row read in an argument
  order those marks do not license, and a row spelled by a `reifiable_function` mark the
  reader takes the other way (`reified-reading`).  A match of a permuting predicate stays
  when the marks the reader believes spell the fact it reads to the stored row.  This runs
  only when a permuting or reifiable mark is stored at all, and per predicate only when
  some reader does not believe a mark (`uniform-marks?`); a variable or nil `view-context`
  filters nothing."
  [kb view-context goal matches]
  (let [tax (reasoning/taxonomy kb)]
    (if-not (and (symbol? view-context) (not (sx/variable? view-context))
                 (or (seq (tax/props tax :symmetric)) (tax/commuting-declared? tax)
                     (seq (tax/props tax :reifiable))))
      matches
      (let [memo (volatile! {})
            at   (fn [p]
                   (let [m @memo]
                     (if (contains? m p)
                       (get m p)
                       (let [ents (mark-entries tax p)
                             v    (when (and (seq ents) (not (uniform-marks? kb ents)))
                                    (entries-at kb ents view-context))]
                         (vswap! memo assoc p v)
                         v))))
            ;; forced by the first match: it reads every `reifiable_function` mark, 1.4 ms
            ;; under 2,061 of them, and most reads answer nothing
            rr   (delay (reified-reading kb view-context))]
        (remove (fn [[_ b stored]]
                  (let [s (sx/sentence-of stored)]
                    (or (when-not (:antecedent stored)
                          (when-let [pf (permuted-functor s)]
                            (when-let [e (at pf)]
                              (not= s (sx/sentence-of
                                       (sx/sentex (read-spelling goal b s) view-context
                                                  (spelling-opts kb pf e)))))))
                        (boolean (when-let [rr @rr] (rr s))))))
                matches)))))

(defn sub-predicates
  "The sub-predicate (genl spec) closure the matching fan-out walks for functor `f`, with
  the predicates an even number of `genlInverse` edges reach (`tax/signed-closure`),
  from the vantage `context` — the global closure when the vantage is a variable or
  nil.  The **single definition every matcher shares** (`match-pattern`,
  `matches-hierarchical`, the rete alpha matcher), so the fan cannot drift between
  them: a genl edge invisible from the vantage does not connect a sub-predicate's
  facts to the pattern, exactly as it does not appear in the closure reads."
  [kb f context]
  (first (tax/signed-closure (reasoning/taxonomy kb) :down f context)))

(defn swapped-sub-predicates
  "The predicates `sub-predicates`' fan reads **with arguments 1 and 2 swapped**: those
  below `f` across an odd number of `genlInverse` edges (`tax/signed-closure`).  Empty —
  one map read — on a KB declaring no `genlInverse`."
  [kb f context]
  (second (tax/signed-closure (reasoning/taxonomy kb) :down f context)))

(defn super-predicates
  "The **genl** closure of `f` from the vantage `context`: `sub-predicates` mirrored,
  through every visible edge whatever its strength.  A negative pattern fans over the
  part of it the reader holds at `:monotonic`, `contrapositive-predicates`."
  [kb f context]
  (first (tax/signed-closure (reasoning/taxonomy kb) :up f context)))

(defn swapped-super-predicates
  "`swapped-sub-predicates` mirrored: the predicates above `f` across an odd number of
  `genlInverse` edges, which a negated pattern on `f` reads swapped."
  [kb f context]
  (second (tax/signed-closure (reasoning/taxonomy kb) :up f context)))

(defn- without-unread-mentions
  "Drop the matches of `goal` that read a fact stored under a mention in another argument
  order where the match's reader reads the mention: the arguments of the two differ once
  each is spelled as the goal's functor's, under the mentions that reader believes
  (`supporter-visible?`).  A sub-predicate's row is so read at the goal's positions, a
  row the fan reads swapped (`swapped-sub-predicates`) with its two exchanged.  The reader
  is `view-context`, or the match's own context under a variable one.  Reads nothing
  unless `goal` has `probes`, its `mention-probes` and `fan-mention-probes`."
  [kb view-context goal probes matches]
  (if (empty? probes)
    matches
    (let [tax     (reasoning/taxonomy kb)
          scoped  (and (symbol? view-context) (not (sx/variable? view-context)))
          marks   (memoize (fn [reader]
                             (assoc (store-marks kb) :mention-at?
                                    (fn [f n] (boolean (some #(supporter-visible? kb (:id %) reader)
                                                             (mention-declarations kb tax f n)))))))
          neg?    (sx/negation? goal)
          body    #(if (sx/negation? %) (second %) %)
          swapped (delay ((if neg? swapped-super-predicates swapped-sub-predicates)
                          kb (first (body goal)) (when scoped view-context)))]
      (remove (fn [[_ b stored]]
                (when-not (:antecedent stored)
                  (let [m     (marks (if scoped view-context (:context stored)))
                        g     (body (substitute goal b))
                        args  (fn [xs] (let [lit (apply list (first g) xs)]
                                         (rest (body (sx/normalize-literal
                                                      (if neg? (list sx/not-functor lit) lit) m)))))
                        stord (rest (body (:sentence stored)))]
                    (not (or (= (args (rest g)) (args stord))
                             (and (= 2 (count stord)) (contains? @swapped (first (body (:sentence stored))))
                                  (= (args (rest g)) (args (reverse stord)))))))))
              matches))))

(def ^:private slot-cut-min
  "The fewest members a fan holds before `slot-cut` reads the slot predicate sets to cut it.  A
  smaller fan is read whole: its member reads are few, and the slot-set reads would be most
  of what the cut costs."
  64)

(def ^:dynamic *cut-every-fan?*
  "True to cut a fan of any size by the slot predicate sets (`slot-cut`), not only one of
  `slot-cut-min` members or more.  For a walk that asks one literal of each of many terms,
  few of which any member holds, where the member reads are the walk's cost
  (`inherit/fact-reach`).  A fan holding a comparison is read whole all the same: a
  comparison is stored under its sibling's functor or as a longer chain
  (`sx/comparison-siblings`, `sx/chained-comparisons`), which the slot sets of the
  probe's functor and positions do not name."
  false)

(def ^:private comparison-functors
  "The functors a fan may hold whose stored spelling has another functor or another
  length than the probe's: `*cut-every-fan?*` reads a fan holding one whole."
  (into sx/chained-comparisons cat sx/comparison-siblings))

(defn- cut-fan?
  "Does `fanned-match` cut the fan `fan` with `swapped` by the slot predicate sets?"
  [fan swapped]
  (or (<= slot-cut-min (+ (count fan) (count swapped)))
      (and *cut-every-fan?*
           (not-any? #(or (contains? fan %) (contains? swapped %)) comparison-functors))))

(defn- slot-cut
  "The predicates holding a stored fact that names every indexable ground argument of
  `body` at some position, read off the slot predicate sets
  (`reads/as-stored-predicates-at-arg`), or nil when `body` has no such argument.  The set
  over-approximates and never drops a match.  See docs/inference.md, Resolution reads."
  [kb body]
  (let [idx   (:index kb)
        n     (dec (count body))
        held  (fn [a] (into #{} (mapcat #(reads/as-stored-predicates-at-arg idx % a)) (range 1 (inc n))))
        terms (filterv sx/indexable-term? (rest body))]
    (when (seq terms)
      (reduce (fn [acc a]
                (if (empty? acc)
                  (reduced acc)
                  (let [h (held a)]
                    (if (< (count h) (count acc)) (into #{} (filter acc) h) (into #{} (filter h) acc)))))
              (held (first terms)) (rest terms)))))

(defn- within
  "The members of `members` in the set `cut`, iterating the smaller of the two."
  [members cut]
  (if (< (count cut) (count members))
    (into #{} (filter members) cut)
    (into #{} (filter cut) members)))

(defn fanned-match
  "The fan-out shared by every matcher: decompose `sentence` into the functor that fans and
  the rebuild that puts it back, take the functor's closure from `vantage`, and run `raw`
  (the caller's as-written retrieval) over each member with `mapcat-fn`.  A variable or
  absent functor fans not at all.  A negation fans its body's functor upward
  (`contrapositive-predicates`, `:monotonic` edges) and rebuilds the `not` per member.  A
  singleton closure is `f` itself.  A `genlInverse` member is read swapped
  (`tax/signed-closure`, docs/inference.md).  `indexed?` cuts a wide fan with `slot-cut`."
  ([kb sentence vantage raw mapcat-fn] (fanned-match kb sentence vantage raw mapcat-fn false))
  ([kb sentence vantage raw mapcat-fn indexed?]
   (let [neg? (sx/negation? sentence)
         body (if neg? (second sentence) sentence)
         f    (when (sequential? body) (first body))]
     (if (and (symbol? f) (not (sx/variable? f)))
       (let [[fan swapped] (fan-closure kb (if neg? :up :down) f vantage)
             ;; a `genlInverse` reading swaps arguments 1 and 2, so only a binary
             ;; literal takes one
             swapped (if (= 3 (count body)) swapped #{})
             cut     (when (and indexed? (cut-fan? fan swapped))
                       (slot-cut kb body))
             [fan swapped] (if cut [(within fan cut) (within swapped cut)] [fan swapped])]
         (cond
           (and (empty? fan) (empty? swapped))
           ()

           (and (= 1 (count fan)) (contains? fan f) (empty? swapped))
           (raw sentence)

           (empty? swapped)
           (let [rebuild (if neg?
                           (fn [f'] (list sx/not-functor (cons f' (rest body))))
                           (fn [f'] (cons f' (rest body))))]
             (mapcat-fn (fn [f'] (raw (rebuild f'))) fan))

           :else
           ;; each member of the fan is read as written, and each swapped member with its
           ;; two arguments exchanged, so a stored `(P a b)` under `(genlInverse P Q)`
           ;; binds the pattern `(Q ?x ?y)` as `?x = b`, `?y = a`
           (let [[_ x y] body
                 rebuild (fn [[f' swap?]]
                           (let [b (if swap? (list f' y x) (cons f' (rest body)))]
                             (if neg? (list sx/not-functor b) b)))]
             (mapcat-fn (fn [m] (raw (rebuild m)))
                        (concat (map #(vector % false) (nm/sort-by-content-key nm/print-key compare fan))
                                (map #(vector % true) (nm/sort-by-content-key nm/print-key compare swapped)))))))
       (raw sentence)))))

(defn match-pattern
  "Seq of [handle bindings] for stored sentexes matching `sentence` within `context`
  (default the wildcard ?ctx).  The functor fans out over its sub-predicate closure, so
  `(animal ?x)` is met by `(dog Muffet)`; a negation fans over `contrapositive-predicates`.
  The fan is scoped to the genl edges visible from `vantage`: by default the literal
  context, the global closure for a `?ctx` match.  The four-arity serves `matches-visible*`,
  which stands at the view context throughout so the set-algebra twin agrees."
  ([kb sentence] (match-pattern kb sentence '?ctx))
  ([kb sentence context] (match-pattern kb sentence context context))
  ([kb sentence context vantage]
   (fanned-match kb sentence vantage
                 (fn [s] (raw-match kb s context))
                 lazy-mapcat
                 true)))

(defn matches-visible*
  "The reference nested fan-out: `|context-up| × |specs|` trie walks.  `matches-visible`
  dispatches to this or to `matches-hierarchical`; the latter also falls back here for
  a shape it does not handle, so this must not re-dispatch (it is the fixed point that
  breaks the cycle)."
  [kb sentence view-context]
  (let [sentence (probe-spelling kb sentence)]
    (if (sx/variable? view-context)
      (match-pattern kb sentence '?ctx)
      (lazy-mapcat (fn [c] (match-pattern kb sentence c view-context))
                   (tax/context-up (reasoning/taxonomy kb) view-context)))))

;; ---- hierarchical (set-algebra) retrieval -------------------------------
;; Scoped to a plain positive literal with a concrete functor; everything else falls back to
;; `matches-visible`, the oracle's reference. Mechanism: docs/indexing.md, "Hierarchical retrieval".

(def ^:dynamic *hierarchical-retrieval*
  "Answer a context-scoped `(p a ?x)` query with the set-algebra retrieval
  (`matches-hierarchical`) rather than the nested `|context-up| × |specs|` fan-out.  On by
  default: a pure cost decision that never changes the answer set.  Bound false, it runs
  the reference fan-out `matches_hierarchical_test` compares against.  See docs/indexing.md,
  Hierarchical retrieval."
  true)

(defn- hierarchical-literal?
  "A plain positive literal the set-algebra path handles: a concrete predicate symbol, or a
  variable functor with something indexable to lead with, `(?type Muffet)`.  A negation, a
  dotted pattern and an unleadable variable functor fall back to `matches-visible`."
  [sentence]
  (and (sequential? sentence) (seq sentence)
       (symbol? (first sentence))
       (not= 'not (first sentence))
       (not-any? #(= '. %) sentence)
       (or (not (sx/variable? (first sentence)))
           (some sx/indexable-term? (rest sentence)))))

(defn- folded-spec?
  "Is one of `specs` a comparison `sx/sentex` stores folded onto its sibling with the
  arguments reversed (`sx/comparison-siblings`)?  A match of such a spec carries the
  sibling's functor and the reversed arguments, which `matches-hierarchical`'s predicate
  filter and argument order do not read.  Driven from the folding predicates, a handful,
  against the spec closure `matches-hierarchical` already holds, so it reads nothing."
  [specs]
  (boolean (some #(contains? specs %) (keys sx/comparison-siblings))))

(defn lead-literal?
  "A literal `matches-hierarchical` answers from an **argument lead** — a plain positive
  literal (`hierarchical-literal?`) with an indexable argument to read the argument
  roots by.  For such a literal the set-algebra path costs one slot read (or one scoped
  read per spec, whichever is smaller — `*lead-side*`) where the nested fan-out costs a
  trie walk per sub-predicate, and the two return the identical set.  The forward join
  asks this of a substituted antecedent (`chain/join-antecedent`) to route a bound type
  test past the `|specs|` fan."
  [sentence]
  (and (hierarchical-literal? sentence)
       (boolean (some sx/indexable-term? (rest sentence)))))

(def ^:dynamic *arg-intersect*
  "How `lead-candidates` narrows a non-symmetric literal with 2 or more indexable ground
  arguments: `:two` (default), `:all`, `:above-floor` or `:off`.  Every choice is a pure
  cost decision: the result is a subset of the single leading column and a superset of the
  matches.  See docs/inference.md, Resolution reads."
  :two)

(def ^:dynamic *arg-intersect-floor*
  "The `:above-floor` strategy's floor: skip the intersection when the leading (tightest)
  column already returns no more than this many handles, where feeding that short
  superset straight to `unify` costs less than allocating an intersection set."
  16)

(defn- multi-cols
  "The ≥2 ground columns `lead-candidates` intersects (each `[pos term]`), or **nil** to
  lead with the single tightest column — chosen by `*arg-intersect*`.  `sorted` is
  `[[count [pos term]] …]`, smallest agnostic count first, so its head is the column the
  single-column lead would have picked."
  [sorted]
  (case *arg-intersect*
    :off nil
    :all (mapv second sorted)
    :above-floor (when (> (long (ffirst sorted)) *arg-intersect-floor*)
                   (mapv second (take 2 sorted)))
    ;; :two — the default; bounded at two reads and one intersection
    (mapv second (take 2 sorted))))

(def ^:dynamic *lead-side*
  "For a non-symmetric literal with a spec closure, which side `lead-candidates` leads
  from.  `:scoped`: one predicate-scoped node per sub-predicate (O(|specs|) probes, the
  reference `matches_hierarchical_test` forces).  `:agnostic`: the slot predicate set
  (`[:argument-slot pos term]`) kept to `specs`, then each kept functor's node.  `:auto`
  (default): `:agnostic` when the term holds no more postings at this position than there
  are specs, else `:scoped`; the choice is content-derived (`count-with-arg` against a
  realised `count`).  A pure cost decision.  `checks/membership-handles` reads it too."
  :auto)

(defn- lead-agnostic?
  "Does `lead-candidates` read the predicate-agnostic bucket (small side) rather than one
  scoped bucket per spec — the choice `*lead-side*` decides?  `:auto` reads the count only
  here, where the branch is actually taken."
  [ix pos term specs]
  (case *lead-side*
    :scoped   false
    :agnostic true
    ;; :auto — read whichever side is smaller
    (<= (long (reads/stored-count-with-arg-global ix pos term)) (count specs))))

(defn- trie-prefix?
  "Is a non-permuting literal of `args` a ground prefix, which `lead-candidates` leads by
  the trie walk under the prefix or by the argument roots (`arg-lead`)?  True when the
  arguments are a run of ground atoms holding two or more indexable terms, then only
  variables, and `*arg-intersect*` is not `:off`."
  [args]
  (let [[pre post] (split-with #(not (or (sequential? %) (sx/variable? %))) args)]
    (and (not= :off *arg-intersect*)
         (every? sx/variable? post)
         (< 1 (count (filter sx/indexable-term? pre))))))

(def ^:private arg-lead-ratio
  "`arg-lead`'s crossover: the argument roots lead a ground prefix when a bound argument
  holds fewer than this many facts per tuple under the prefix, in the contexts the reader
  sees, or in every context for a variable context.  docs/indexing.md §2 gives the
  measurement."
  4)

(defn- arg-lead
  "The bound arguments `ground` in the order to intersect sub-predicate `pd`'s argument
  roots in, when its ground-prefix pattern at trie `path` reads them instead of walking
  the trie under the prefix, or nil when the walk leads.  With the prefix's trie count c,
  the roots lead when some bound argument holds fewer than `arg-lead-ratio` × c facts in
  the contexts the intersection probes, and c exceeds the number of those contexts: |up|,
  or for a variable context (`up` nil) that argument's own contexts, in which case that
  argument leads the intersection.  docs/indexing.md §2."
  [ix pd path ground up]
  (let [c     (long (reads/stored-count-at
                     ix (into [] (take-while (complement sx/variable?)) path)))
        limit (* (long arg-lead-ratio) c)]
    (if up
      (when (and (< (count up) c)
                 (some (fn [[pos term]]
                         (< (long (reads/stored-count-with-arg-in ix pd pos term up)) limit))
                       ground))
        ground)
      ;; every bound argument holds the c tuples, so c > k ≥ 1 needs c ≥ 2
      (when (< 1 c)
        (when-some [[_ g] (first
                           (sort-by first
                                    (keep (fn [[pos term :as g]]
                                            (let [[n k] (reads/stored-census-with-arg-global
                                                         ix pd pos term)]
                                              (when (and (< (long n) limit) (< (long k) c))
                                                [k g])))
                                          ground)))]
          ;; `sentexes-with-args` fans over its first argument's contexts and probes the
          ;; rest, so the argument stated in the fewest contexts goes first
          (cons g (remove #{g} ground)))))))

(defn- lead-candidates
  "A lazy superset of the matching handles, led by the tightest bound argument.  Argument
  roots are scoped by predicate and end in the context, so each sub-predicate's own node
  at the position is read, restricted to the contexts in `up` (nil for a variable
  context).  `*lead-side*` may read the slot predicate set first.  A variable functor
  reads the predicate-agnostic union; with no bound argument, the sub-predicates'
  extents; a ground prefix walks the trie unless `arg-lead` reads its roots.  When any
  sub-predicate permutes the position, every position it reaches is taken, so a handle may
  repeat and `matches-hierarchical`'s `seen` set dedups."
  [kb specs args alts up]
  (let [ix     (:index kb)
        ;; `alts` is nil when nothing permutes, else a fn from a position to the other positions a match may
        ;; be stored at. A superset is safe: `unify` filters every candidate.
        alt    (fn [pos] (when alts (seq (alts pos))))
        ground (keep-indexed (fn [i a] (when (sx/indexable-term? a) [(inc i) a])) args)]
    (cond
      ;; One trie walk per spec, its last level (the context) kept to `up`, or that
      ;; spec's argument roots where `arg-lead` finds them smaller.  A spec that
      ;; `kb-sentex` respells loses the prefix, so that spec reads its roots.
      (and (nil? alts) (seq specs) (trie-prefix? args))
      (lazy-mapcat (fn [pd]
                     (let [pat  (kb-sentex kb (cons pd args) '?ctx)
                           path (sx/path pat)]
                       (if (= (sx/body pat) (cons pd args))
                         (if-some [g (arg-lead ix pd path ground up)]
                           (p/sentexes-with-args ix pd g up)
                           (p/lookup ix path up))
                         (p/sentexes-with-args ix pd ground up))))
                   specs)

      (seq ground)
      (let [cnt (fn [[pos term]]
                  (reduce (fn [n pz] (+ n (reads/stored-count-with-arg-global ix pz term)))
                          (reads/stored-count-with-arg-global ix pos term)
                          (alt pos)))
            ;; A lone ground column needs no count. With 2+ columns, count each and sort smallest first (stable,
            ;; so ties go leftmost).
            sorted (when (next ground)
                     (sort-by first (mapv (fn [g] [(long (cnt g)) g]) ground)))
            [pos term] (if sorted (second (first sorted)) (first ground))
            ;; Argument roots are scoped by predicate, so read each sub-predicate's bucket: the predicate-agnostic
            ;; read returns derived facts no rule reads back. `lazy-mapcat` keeps an existence check to one bucket.
            scoped (fn [pd pz] (p/sentexes-with-args ix pd {pz term} up))
            ;; Multi-column narrowing: with 2+ indexable ground columns on a non-symmetric literal, intersect them
            ;; at the probe (`*arg-intersect*`). `nil` keeps the single leading column (the settle diet and every
            ;; symmetric literal).
            cols   (when (and (nil? alts) sorted) (multi-cols sorted))]
        (cond
          (seq cols)
          (let [pt (into {} cols)]                     ; {pos term} — positions are unique
            (if (seq specs)
              (lazy-mapcat (fn [pd] (p/sentexes-with-args ix pd pt up)) specs)
              ;; a variable functor has no scope: intersect the predicate-agnostic columns
              (p/sentexes-with-args ix nil pt up)))

          (seq specs)
          (if-let [azs (alt pos)]
            (lazy-mapcat (fn [pd]
                           (reduce (fn [acc pz] (concat acc (scoped pd pz)))
                                   (scoped pd pos) azs))
                         specs)
            ;; One bucket per spec is O(|hierarchy|) for a broad functor. `*lead-side*` picks the slot predicate
            ;; set instead: read it once, keep the predicates in `specs`, read each kept node.
            (lazy-mapcat (fn [pd] (scoped pd pos))
                         (or (when (lead-agnostic? ix pos term specs)
                               (some->> (reads/as-stored-predicates-at-arg ix pos term)
                                        (filter #(contains? specs %))))
                             specs)))

          ;; A variable functor names no predicate: the predicate-agnostic root is the candidate set, `unify`
          ;; binds the functor, and nothing permutes.
          :else
          (p/sentexes-with-args ix nil {pos term} up)))

      ;; no indexable argument: each spec's predicate extent, in the contexts the reader sees
      :else
      (lazy-mapcat #(p/sentexes-with-args ix % [] up) specs))))

(defn- matches-hierarchical-over
  "`matches-hierarchical` over `specs`, the functor's spec closure (nil for a variable
  functor or a shape it does not handle).

  The marks are read unscoped: the fold decides the stored key, and
  `without-unbelieved-spellings` hides the spelling a reader's belief rules out."
  [kb sentence view-context specs]
  (if (or (not (hierarchical-literal? sentence)) (folded-spec? specs))
    (matches-visible* kb sentence view-context)
    (let [tax   (reasoning/taxonomy kb)
          ;; A variable functor has no spec closure: `lead-candidates` gets `specs` nil and takes its
          ;; predicate-agnostic branch.
          var-fn? (sx/variable? (first sentence))
          args  (rest sentence)
          up?   (not (sx/variable? view-context))
          up    (when up? (tax/context-up tax view-context))
          ;; Is any sub-predicate symmetric? Only a binary literal has a mirror. Driven from the declared
          ;; symmetric predicates, tested for membership in `specs`: scanning a broad functor's closure costs more
          ;; than the retrieval. A variable functor is never symmetric (`sx/symmetric-literal?`). `sym?` only
          ;; widens `lead-candidates`' bucket selection; whether a candidate matches mirrored is its own
          ;; functor's question (`sym-preds` at the probe).
          sym?  (and (not var-fn?)
                     (= 2 (count args))
                     (boolean (some #(contains? specs %) (tax/props tax :symmetric))))
          sym-preds (when sym? (tax/props tax :symmetric))
          ;; The same question for the commutativity marks, driven the same way.
          comm-preds (when-not var-fn? (tax/commuting-predicates-among tax specs))
          ;; The positions one argument may also be stored at, unioned over the permuting sub-predicates; nil
          ;; when nothing permutes.
          alts  (let [comps (concat (when sym? [[1 2]])
                                    (mapcat #(sx/commuting-components
                                              (tax/commuting-groups tax %) (count args))
                                            comm-preds))
                      m (reduce (fn [m c]
                                  (reduce (fn [m pos] (update m pos (fnil into #{})
                                                              (remove #{pos} c)))
                                          m c))
                                {} comps)]
                  (when (seq m) m))
          ;; the argument lists a candidate of functor `f` may be probed under, `args`
          ;; first — the generalization of the symmetric mirror, memoized per functor so
          ;; a posting of one functor over many contexts builds them once.
          ;; the argument lists the compounds below the literal are probed in
          ;; (`nested-probes`), `args` first; nil when no compound holding a variable
          ;; permutes
          nested (let [ns (nested-probes kb sentence)]
                   (when (next ns) (mapv #(vec (rest %)) ns)))
          alt-args (volatile! {})
          args-for (fn [f]
                     (or (get @alt-args f)
                         (let [base (or nested [(vec args)])
                               v    (if (and f (or (contains? sym-preds f)
                                                   (contains? comm-preds f)))
                                      (into [] (comp (mapcat
                                                      (fn [as]
                                                        (if (contains? sym-preds f)
                                                          [(cons f as) (cons f (reverse as))]
                                                          (sx/commuting-arrangements
                                                           (cons f as)
                                                           (fn [g _] (tax/commuting-groups tax g))))))
                                                     (map #(vec (rest %)))
                                                     (distinct))
                                            base)
                                      base)]
                           (vswap! alt-args assoc f v)
                           v)))
          seen  (volatile! #{})
          ;; The unify-attempt tally: candidates that clear the cheap filters and reach `unify`. `prof?` is
          ;; captured once so the off path costs a `false` test and one call records or declines a literal
          ;; consistently.
          prof? (prof/profiling?)
          unifs (volatile! 0)
          ;; The pattern sentex depends on the candidate's functor and context only, and building one
          ;; canonicalizes a sentence, so it is memoized per call. `rev?` is in the key because `args` and its
          ;; mirror are the only argument lists in play.
          pats  (volatile! {})
          ;; A concrete functor is replaced by the candidate's (subsumption is already established); a variable
          ;; functor is kept so the caller's binding survives.
          pat-functor (if var-fn? (constantly (first sentence)) identity)
          ;; `i` indexes `args-for`'s arrangement vector; -1 is `args` as written, the row a reader that does
          ;; not believe the candidate functor's mark reads (`as-written-probe`).
          pat-for (fn [f' pctx i]
                    (let [pf (pat-functor f')
                          k  [pf pctx i]]
                      (if-some [p (get @pats k)]
                        p
                        (let [p (if (neg? i)
                                  (binding [*spelled-by* [pf pctx #{}]]
                                    (kb-sentex kb (cons pf args) pctx))
                                  (kb-sentex kb (cons pf (nth (args-for f') i)) pctx))]
                          (vswap! pats assoc k p)
                          p))))
          split? (memoize (fn [f] (let [e (mark-entries tax f)]
                                    (boolean (and (seq e) (not (uniform-marks? kb e)))))))]
      ;; the second retrieval decision in this namespace, and the one `candidate-handles`
      ;; never sees: `lead-candidates` picks its source from the same three facts, so the
      ;; label is computed from them here rather than plumbed back out of it.
      (let [path (cond
                   (not (some sx/indexable-term? args)) :hier-functor-extent
                   (and (nil? alts) (seq specs) (trie-prefix? args)) :hier-trie-prefix
                   (seq specs)                          :hier-scoped-roots
                   :else                                :hier-agnostic-roots)
            _    (when prof? (prof/record-literal sentence path))
            cands (hinting kb (lead-candidates kb specs args alts up))
            ;; A candidate that can answer: live and fetched. The leads read only `up` contexts' nodes, so no
            ;; predicate or context filter runs. An exceptWhen meta-sentex is skipped, as in `match-one`.
            blind? (belief-blind?)
            admit (fn [h]
                    (when (or blind? (jtms/in? (reasoning/tms kb) h))
                      (when-let [stored (p/get-sentex (:records kb) h)]
                        (when-not (sx/exceptWhen-meta? (:sentence stored))
                          stored))))
            ;; the unify attempt in one argument order.  Concrete view context: bind no ?ctx
            ;; (match at the fact's own context, which is in the up-closure); variable
            ;; view context: bind ?ctx, exactly as match-one does.
            order (fn [stored i]
                    (let [pat (pat-for (some-> (sx/body stored) first)
                                       (if up? (:context stored) '?ctx)
                                       i)]
                      (when (= (sx/negative? pat) (sx/negative? stored))
                        (unify (:context pat) (:context stored)
                               (unify (:sentence pat) (:sentence stored))))))
            out
            (if-not (or sym? comm-preds nested)
              ;; Nothing under this functor is symmetric, so a candidate answers at most once and the handle is the
              ;; dedup key; a `keep` and a handle-keyed guard skip the record fetch for a repeated candidate.
              (keep (fn [h]
                      (when-not (contains? @seen h)
                        (when-let [stored (admit h)]
                          (when prof? (vswap! unifs inc))
                          (when-let [b (order stored 0)]
                            (vswap! seen conj h)
                            [h b stored]))))
                    cands)
              ;; A permuting sub-predicate: one candidate can answer more than once (an all-variable pattern binds
              ;; `(sibOf Rex Tib)` both ways), so dedup keys on `[handle bindings]` (`raw-match` says why).
              (lazy-mapcat
               (fn [h]
                 (when-let [stored (admit h)]
                   (when prof? (vswap! unifs inc))
                   (let [;; every arrangement, not the first that answers: a pattern with
                         ;; Two variable arguments bind one stored fact twice and differently; `distinct` collapses a
                         ;; palindrome arrangement to one.
                         f' (some-> (sx/body stored) first)
                         n  (count (args-for f'))
                         bs (into [] (comp (keep #(order stored %)) (distinct))
                                  (cond->> (range n) (and up? (split? f')) (cons -1)))]
                     (into []
                           (comp (remove #(contains? @seen [h %]))
                                 (map (fn [b]
                                        (vswap! seen conj [h b])
                                        [h b stored])))
                           bs))))
               cands))]
        ;; Returned-vs-matched, opt-in: realizing `out` walks the candidate seq, so it runs only while the
        ;; instrument is on (`vaelii.impl.profile/record-sift`).
        (if prof?
          (let [v (vec out)]
            (prof/record-sift sentence path (count cands) (count v) @unifs)
            v)
          out)))))

(defn matches-hierarchical
  "The set-algebra twin of `matches-visible` for a positive literal: the identical
  `[handle bindings stored]` set, but reached by context-scoped index reads of the
  sub-predicates' own nodes instead of the `|specs| × |context-up|` product of trie
  walks.  Falls back to `matches-visible` for any shape it does not handle, and for a
  literal with a spec stored under another functor (`folded-spec?`) or read swapped
  (`swapped-sub-predicates`)."
  [kb sentence view-context]
  (if (and (hierarchical-literal? sentence) (not (sx/variable? (first sentence)))
           (= 3 (count sentence))
           (seq (swapped-sub-predicates kb (first sentence) view-context)))
    ;; a `genlInverse` spec is stored with its arguments the other way round, which the
    ;; argument-root reads below do not exchange: the reference fan-out reads it
    (matches-visible* kb sentence view-context)
    (matches-hierarchical-over
     kb (probe-spelling kb sentence) view-context
     (when (and (hierarchical-literal? sentence) (not (sx/variable? (first sentence))))
       (sub-predicates kb (first sentence) view-context)))))

(defn retired-for?
  "Does `sentence` name a term the reader has retired, so that it is not in that reader's
  normal form?  `visible` is the caller's **delay** over the supporter memo and `merged?`
  its partition snapshot (`tax/merged-term-pred`), so an unmerged sentence answers false on
  one `merged?` walk and never forces `visible`.  A positive equation is never retired
  (`equation?`).  A sentence with a mention position, an equality relation's arguments
  included, is confirmed against the mention-aware walk before it is called retired.
  Public for `qcn-kb/refuted-pairs`, whose `[handle a b]` rows `without-retired` cannot
  take."
  [kb visible merged? sentence]
  (let [marks (tax/mention-marks (reasoning/taxonomy kb))]
    (cond
      (equation? sentence)
      false

      (not (sx/some-symbol? (fn [t]
                              (and (merged? t) (not (sx/variable? t))
                                   (not= t (representative-in kb @visible t))))
                            sentence))
      false

      (any-mention-position? marks sentence)
      (not= (representative-term-mention kb @visible marks sentence false) sentence)

      :else
      (or (not (names-equality-relation? sentence))
          (not= (representative-term-plain kb @visible sentence) sentence)))))

(defn without-retired
  "Drop the `matches` whose stored spelling `view-context` has **retired**: the
  reader-scoped half of supersession (docs/equality.md, \"The reader is not the fact's own
  context\").  Filters nothing when the closure is empty, one deref, or when
  `view-context` is nil or a variable, the unscoped read."
  [kb view-context matches]
  (let [merged? (tax/merged-term-pred (reasoning/taxonomy kb))]
    (if-not (and merged? (symbol? view-context) (not (sx/variable? view-context)))
      matches
      (let [visible (delay (visible-supporter-fn kb view-context))]
        (remove (fn [m] (retired-for? kb visible merged? (sx/sentence-of (nth m 2)))) matches)))))

(defn- with-open-functor-supers
  "A positive open-functor pattern's matches, each also answering the functor variable
  with every super-predicate of the one it matched (`super-predicates`, from
  `view-context`), on the same stored fact: `(?c Muffet)` answers `dog` and `animal`.  A
  functor variable that also stands as an argument keeps the functor as stored; so does a
  negative pattern."
  [kb sentence view-context matches]
  (let [fv (when (and (seq? sentence) (sx/variable? (first sentence))) (first sentence))]
    (if (or (nil? fv) (some #(= fv %) (tree-seq sequential? seq (rest sentence))))
      matches
      (mapcat (fn [[h b stored :as m]]
                (let [f (get b fv)]
                  (if (symbol? f)
                    (cons m (for [g (nm/sort-by-content-key nm/print-key compare
                                                            (disj (super-predicates kb f view-context) f))]
                              [h (assoc b fv g) stored]))
                    [m])))
              matches))))

;; ---- the value a corresponding fact names -----------------------------------
;; docs/nat.md, The corresponding predicate.

(defn minted-expression
  "The expression the believed CxUniverse `natFormula` rows map the reified object
  constant `k` to, the content-least where several do, or nil."
  [kb k]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> (reads/as-stored-with-args (:index kb) 'natFormula {1 k})
         (keep #(p/get-sentex recs %))
         (keep (fn [{s :sentence c :context h :id}]
                 (when (and (= sx/root-context c) (= k (second s)) (seq? (nth s 2 nil))
                            (jtms/in? tms h))
                   (nth s 2))))
         (nm/min-by-content-key identity))))

(defn- values-of
  "`{value [fact-handle …]}` for the ground NAT expression `E` read from `context`: the
  value each corresponding fact `match` answers names, spelled under `context`'s merges,
  with the facts naming it.  Empty when the declarations `context` sees give `E`'s
  function no single correspondence.  `match` is `matches-visible`'s retrieval."
  [kb E context match]
  (let [args (rest E)]
    (if-let [[pr pos] (correspondence-of kb (first E) (count args) context)]
      (let [visible? (visible-supporter-fn kb context)]
        (reduce (fn [acc [h b]]
                  (let [v (get b '?v)]
                    (if (or (nil? v) (sequential? v))
                      acc
                      (update acc (normal-form kb v visible?) (fnil conj []) h))))
                {}
                (match kb (goal-normal-form kb (apply list pr (insert-at args pos '?v)) context) context)))
      {})))

(defn- names-object-constant?
  "Does `form` name a reified object constant (`nat/`), at any nesting?"
  [form]
  (if (symbol? form)
    (and (nm/reified-constant? form) (= "nat" (namespace form)))
    (and (sequential? form) (boolean (some names-object-constant? form)))))

(defn- copied-values
  "`{k v}` for each reified object constant `k` that the goal `sentence` names and whose
  corresponding facts visible from `context` name exactly one value `v` outside `k`'s
  class, `v` not itself a reified constant: the spelling a goal naming `k` reads beside
  its own (docs/nat.md, The corresponding predicate).  Nil for a variable context and
  behind one functor count."
  [kb sentence context match]
  (when (and (symbol? context) (not (sx/variable? context))
             (names-object-constant? sentence) (any-corresponding-predicates? kb))
    (let [visible? (visible-supporter-fn kb context)]
      (not-empty
       (into {}
             (keep (fn [k]
                     (when-let [E (minted-expression kb k)]
                       (let [vs (disj (set (keys (values-of kb E context match))) (normal-form kb k visible?))]
                         (when (and (= 1 (count vs)) (not (nm/reified-constant? (first vs))))
                           [k (first vs)])))))
             (distinct (filter #(and (symbol? %) (names-object-constant? %))
                               (tree-seq sequential? seq sentence))))))))

(defn- without-edge-read-matches
  "`matches` of the positive unary `sentence` `(q …)` less each match of a membership
  `(s x)` the `genl` fan read where an edge reading of `(q x)` rests on it
  (`exc/edge-read-functors`) and `view-context` sees no path from `s` to `q` held at
  `:monotonic`: the stored reading answers for `x` there.  One presence check
  (`reads/stores-opposed-with-functor?`) while no body of `q` is stored in both
  polarities.  See docs/inference.md, \"An edge's reading\"."
  [kb view-context sentence matches]
  (let [q (when (and (sequential? sentence) (= 2 (count sentence))) (first sentence))]
    (if (and (seq matches) (sx/plain-symbol? q) (not= sx/not-functor q)
             (symbol? view-context) (not (sx/variable? view-context))
             (reads/stores-opposed-with-functor? (:index kb) q))
      (let [recs    (:records kb)
            idx     (:index kb)
            tax     (reasoning/taxonomy kb)
            holding (delay (holding-class kb))
            strict? (fn [s] (when-let [hs (tax/reach-support tax :genl s q view-context @holding [:monotonic])]
                              (every? #(= :monotonic (@holding (first %))) hs)))]
        (remove (fn [[h]]
                  (let [s (:sentence (p/get-sentex recs h))]
                    (and (seq? s) (= 2 (count s)) (not= q (first s))
                         (reads/stored-opposed? idx (list q (second s)))
                         (contains? (exc/edge-read-functors kb h) q)
                         (not (strict? (first s))))))
                matches))
      matches)))

(defn without-hidden-matches
  "`matches` of `sentence` less what `view-context` cannot read: the handles an `except`
  hides (`exc/without-excepted`), the fan matches an edge reading answers for
  (`without-edge-read-matches`), the spellings an equality merge retired
  (`without-retired`), the spellings its marks do not license
  (`without-unbelieved-spellings`) and the orders of a mention it reads
  (`without-unread-mentions`), in that order.  `probes` is `sentence`'s `mention-probes`
  when the caller holds them."
  ([kb view-context sentence matches]
   (without-hidden-matches kb view-context sentence (mention-probes kb sentence) matches))
  ([kb view-context sentence probes matches]
   (->> matches
        (exc/without-excepted kb view-context)
        (without-edge-read-matches kb view-context sentence)
        (without-retired kb view-context)
        (without-unbelieved-spellings kb view-context sentence)
        (without-unread-mentions kb view-context sentence probes))))

(defn- visible-matches
  "The retrieval both of `matches-visible`'s arities perform: the chosen path over
  `sentence`, its `mention-probes` and its `fan-mention-probes`, then the visibility
  filters, then an open functor's super-predicates (`with-open-functor-supers`), then the
  matches of the spelling that reads each copied value in place of its constant
  (`copied-values`).  One definition, so a cached and an uncached read cannot come to
  answer differently."
  [kb sentence view-context]
  (let [read  #(if *hierarchical-retrieval*
                 (matches-hierarchical kb % view-context)
                 (matches-visible* kb % view-context))
        extra (into [] (distinct) (concat (mention-probes kb sentence)
                                          (fan-mention-probes kb sentence view-context)))
        own   (->> (if (seq extra)
                     (nm/distinct-by (fn [[h b]] [h b]) (mapcat read (cons sentence extra)))
                     (read sentence))
                   (without-hidden-matches kb view-context sentence extra)
                   (with-open-functor-supers kb sentence view-context))]
    (if-let [kv (copied-values kb sentence view-context visible-matches)]
      (distinct (concat own (visible-matches kb (walk/postwalk-replace kv sentence) view-context)))
      own)))

(defn matches-visible
  "Type-aware matches of `sentence` visible from `view-context`.  A variable context means
  any context; a concrete one sees a fact iff the fact's context is in its genlCx
  up-closure.  A positive literal is answered by `matches-hierarchical` unless
  `*hierarchical-retrieval*` is false.  A sentex an `except` hides from `view-context` is
  filtered out.  Answers are cached per KB by the alpha-renamed literal and the change
  clock (`vaelii.impl.literal-cache`), keyed also on every var that selects a path.
  `cached?` false neither consults nor fills the cache.  docs/inference.md, Resolution reads."
  ([kb sentence view-context] (matches-visible kb sentence view-context true))
  ([kb sentence view-context cached?]
   (let [sentence (probe-spelling kb sentence)]
     (if-not (and cached? lc/*enabled*)
       (visible-matches kb sentence view-context)
       (let [[canonical rename] (lc/canonicalize sentence)]
         (lc/rename-matches
          unify rename
          (lc/lookup (reasoning/matches kb)
                     [canonical view-context
                      *hierarchical-retrieval* *arg-root-retrieval* *structural-index*
                      *belief-blind* exc/*unscoped-own* tax/*search* tax/*network-belief*]
                     #(visible-matches kb canonical view-context))))))))

(defn corresponding-values
  "`{value [fact-handle …]}` for the ground NAT expression `E` read from `context`
  (CxUniverse when nil): the value each visible corresponding fact names, spelled under
  `context`'s merges, with the believed facts naming it.  Empty when the declarations
  `context` sees give `E`'s function no single correspondence; a variable `context`
  reads every declaration and every context."
  [kb E context]
  (values-of kb E (or context sx/root-context) matches-visible))

;; ---- whose declarations bind a tuple ------------------------------------

(defn type-memberships
  "The membership sentexes `(T x)` of term `x` that `kb/types-of` reads its types off, as
  records: believed, asserted in a context `context` sees, and not hidden from it by an
  `except` (default: any context).  The same three filters `matches-visible` applies.  A
  negative membership is excluded by the argument test: a `(not (T x))` sentex has `not`
  as its functor."
  ([kb x] (type-memberships kb x '?ctx))
  ([kb x context]
   (let [recs     (:records kb)
         tms      (reasoning/tms kb)
         visible? (if (sx/variable? context)
                    (constantly true)
                    (let [up (tax/context-up (reasoning/taxonomy kb) context)] #(contains? up %)))
         ;; a read with no reader reads each membership at its own context
         hidden?  (or (if (sx/variable? context) (exc/own-hidden-fn kb) (exc/hidden-fn kb context))
                      (constantly false))]
     ;; The unary predicate set goes straight to the sentexes holding x as their lone argument
     ;; (`reads/as-stored-unary-with-arg-global`), a superset the arity and argument tests narrow. The
     ;; filters are one lazy `keep`: the postings are short and a `filter`/`map` chain allocates per stage.
     (->> (reads/as-stored-unary-with-arg-global (:index kb) x)
          (keep (fn [h]
                  (when-not (hidden? h)
                    (when-let [s (p/get-sentex recs h)]
                      (when (and (jtms/in? tms (:id s))      ; believed memberships only
                                 (visible? (:context s)))
                        (let [sen (:sentence s)]
                          (when (and (= 1 (nm/arity sen)) (= x (first (nm/args sen))))
                            s)))))))))))

(def ^:dynamic *membership-memo*
  "A volatile `{[x context] memberships}` the separation's denial reads a term's
  memberships through while bound (`checks/cover-problem` binds it over one write's
  covers, where nothing is stored), or nil to read `type-memberships` afresh."
  nil)

(defn- memberships-for
  "`type-memberships` of `x` at `context`, through `*membership-memo*` when it is bound."
  [kb x context]
  (if-let [memo *membership-memo*]
    (let [k [x context]]
      (caches/get-or! memo k #(vec (type-memberships kb x context))))
    (type-memberships kb x context)))

(defn- separation-denial-witnesses
  "`separation-denials`' witnesses, lazily and in the order the memberships and routes
  are read.  The routes are read off the closure cache (`tax/separation-routes-held`), and
  a pair no declaration separates is skipped on the held test (`tax/pair-separated?`)."
  [kb t x context]
  (let [tax (reasoning/taxonomy kb)]
    (when (and (symbol? t) (tax/separable? tax t))
      (let [cls (holding-class kb)
            ctx (when-not (sx/variable? context) context)]
        (for [m     (memberships-for kb x context)
              :let  [s (nm/functor (:sentence m))]
              :when (and (not= s t) (symbol? s) (tax/pair-separated? tax s t))
              r     (tax/separation-routes-held tax s t)
              :let  [wit (tax/monotonic-route-witness tax r ctx cls)]
              :when wit]
          {:membership (:id m) :sentence (:sentence m) :context (:context m) :route wit})))))

(defn separation-denials
  "The witnesses of `(not (t x))` a reader at `context` reads off a separation, in content
  order: one per believed, visible, unexcepted membership `(s x)` (`type-memberships`) and
  per route a declaration separates `s` from `t` through (`tax/separation-routes`) that
  meets `tax/monotonic-route-witness`.  Each witness is `{:membership h :sentence (s x)
  :context c :route {:keys :pair :supports :edges}}`.  Empty when no separation reaches
  `t` (`tax/separable?`).  `provers/DisjointnessNegationProver` and `checks/cover-problem`
  read it (docs/taxonomy.md, A separation answers a denial)."
  [kb t x context]
  (nm/sort-by-content-key
   #(nm/print-key [(:sentence %) (:context %) (:keys (:route %)) (:pair (:route %))])
   compare
   (separation-denial-witnesses kb t x context)))

(defn separation-denied?
  "Does a reader at `context` read `(not (t x))` off a separation: is
  `separation-denials` non-empty?  Reads the witnesses lazily and stops at the first,
  for a caller that asks whether the denial holds and names no member
  (`provers/DisjointnessNegationProver`)."
  [kb t x context]
  (some? (first (separation-denial-witnesses kb t x context))))

(defn constraining-predicates
  "The predicates whose argument declarations of kind `kind` bind a `pred` tuple: `pred`
  itself first, then every super-predicate of it `context` can see that some sentence
  declares `kind` of, sorted.  `(arg parentOf 1 person)` constrains every `fatherOf` tuple
  given `(genl fatherOf parentOf)`.  Both readers of a declaration come here
  (`checks/declaration-reader`, `provers/inferred-types`).  Filtered against the global
  `:props` set (`tax/arg-declaration-props`); `[]` when it is empty.  `memos`, a volatile
  map held for one still taxonomy, keeps a `tax/genls-among` memo per `kind`."
  [kb kind pred context & [memos]]
  (let [tax       (reasoning/taxonomy kb)
        ;; A set intersection, not an index probe per ancestor: a type ten deep would pay ten
        ;; argument-root reads per assert, nine of them for types that declare nothing
        ;; (on a minting assert, the mint's own functor among them).  The global `:props` set
        ;; is a superset of what `context` sees; the caller's scoped read of each returned
        ;; predicate decides which of them speak here.
        declaring (tax/props tax (tax/arg-declaration-props kind))
        base      (if (contains? declaring pred) [pred] [])]
    (cond
      (empty? declaring) []
      ;; `identical?`: comparing the set by value would walk all of it per lookup.
      ;; `sort`: the declaration a refusal names, and the order entailments are drawn in,
      ;; follow the vocabulary and not the closure's hash order.
      memos (let [[held memo] (get @memos kind)
                  memo        (if (identical? held declaring)
                                memo
                                (let [m (volatile! {})] (vswap! memos assoc kind [declaring m]) m))]
              (into base (sort (disj (tax/genls-among tax pred context declaring memo) pred))))
      :else (let [supers (tax/genls tax pred context)]
              (if (<= (count supers) 1)
                base
                (into base (sort (disj (set/intersection declaring supers) pred))))))))

;; ---- the argument-constraint chokepoint ---------------------------------
;; Two instance-level constraints are looked up: `arg` (one position) and `argAndRest` (a position and
;; every later one). The other spellings are sugar whose forward rules (core.txt) store them. The
;; type-level (`genlArg`, `argsGenl`, `argAndRestGenl`) and quoted (`quotedArg`) twins come back on the
;; same entries under their own `:kind`.

(def arg-constraint-kinds
  "Per declaration functor, the `:kind` its entries carry and its shape: `:at` types
  position n, `(K P n T)`; `:rest` types n and every later one, `(K P n T)`; `:every`
  types every position, `(K P T)`, read as `:rest` from 1."
  '{arg            [:instance :at]
    argAndRest     [:instance :rest]
    genlArg        [:type :at]
    argAndRestGenl [:type :rest]
    argsGenl       [:type :every]
    quotedArg      [:quoted :at]
    quotedArgAndRest [:quoted :rest]})

(defn- read-arg-constraints
  "`arg-constraints`, read from the store: every visible declaration of each
  `arg-constraint-kinds` functor on `pred` or a super-predicate whose declarations bind its
  tuples (`constraining-predicates`), ordered by the declaration's own sentence."
  [kb pred context]
  (let [type? #(and (symbol? %) (not (sx/variable? %)))
        rows  (for [[k [kind shape]] arg-constraint-kinds
                    q                (constraining-predicates kb k pred context)
                    [_ b s]          (matches-visible kb (if (= :every shape)
                                                           (list k q '?t)
                                                           (list k q '?n '?t))
                                                      context)
                    :let             [n (if (= :every shape) 1 (get b '?n))
                                      t (get b '?t)]
                    :when            (and (integer? n) (pos? n) (type? t))]
                [(:sentence s) {:from n :to (when (= :at shape) n) :type t :kind kind :via q}])]
    (into [] (comp (map second) (distinct))
          (nm/sort-by-content-key first nm/compare-form rows))))

(defn arg-constraints
  "The argument constraints binding `pred`'s tuples as `context` sees them, as entries
  `{:from n :to m :type T :kind K :via P}` in declaration order.  `:to` is nil for a tail
  running to the last argument.  `:kind` is `:instance` (`arg`, `argAndRest`), `:type`
  (`genlArg`, `argAndRestGenl`, `argsGenl`) or `:quoted` (`quotedArg`).  `:via` is the
  predicate the declaration is written on (`constraining-predicates`).  `arg-constraints-at`
  answers for one position.  A malformed declaration is dropped.  Held in the taxonomy's
  closure memo for one stretch of the change clock (`tax/clock-held`)."
  [kb pred context]
  (when (and (symbol? pred) (not (sx/variable? pred)))
    (tax/clock-held (reasoning/taxonomy kb) ::arg-constraints [pred context]
                    #(read-arg-constraints kb pred context))))

(defn arg-constraints-at
  "The `arg-constraints` entries that type position `n` of `pred`'s tuples from
  `context`: each `:at` entry for `n`, and each tail entry starting at or before it."
  [kb pred context n]
  (when (and (integer? n) (pos? n))
    (filterv (fn [{:keys [from to]}] (and (<= from n) (or (nil? to) (<= n to))))
             (arg-constraints kb pred context))))

(defn arg-admits-fn
  "A predicate `(fn [x position] …)`: does every type the instance-level declarations
  `arg-constraints-at` answers for `pred`'s `position` (0-based) from `context` admit term
  `x`?  A type admits a term unless the term holds a believed type `context` sees as
  disjoint from it, so an untyped term is admitted, as `assert` admits it, and nothing is
  concluded from the declaration.  Each term's types are read once per returned fn, and
  only at a position some declaration types: an undeclared position admits every term."
  [kb pred context]
  (let [tax   (reasoning/taxonomy kb)
        types (memoize
               (fn [n]
                 (into #{} (comp (filter #(= :instance (:kind %))) (map :type))
                       (arg-constraints-at kb pred context (inc n)))))
        held  (memoize (fn [x] (into [] (comp (map #(nm/functor (:sentence %))) (distinct))
                                     (type-memberships kb x context))))]
    (fn [x position]
      (let [ts (types position)]
        (or (empty? ts)
            (let [hs (held x)]
              (not-any? (fn [t] (some #(tax/disjoint? tax % t context) hs)) ts)))))))

;; ---- backward chaining --------------------------------------------------
;; goal-key and planned-antecedents are shared by the goal-stack machine here and the node engine
;; (`vaelii.impl.inference`), which differ in execution only and must agree on planning, loop detection
;; and binding threading.

(defn goal-key
  "A goal with all variables collapsed to `?`, for loop detection: two goals that
  differ only in variable names share a key."
  [g]
  (walk/postwalk (fn [x] (if (sx/variable? x) '? x)) g))

(defn term-depth
  "How deeply `form`'s arguments nest compound terms: 0 for a flat literal `(p A)`, 1
  for `(p (SuccFn A))`, 2 for `(p (SuccFn (SuccFn A)))`.  The second half of the loop
  guard (`default-max-term-growth`): a goal key keeps its ground arguments, so a rule
  that wraps a function around a head variable mints a fresh key per expansion and the
  key alone never repeats.  One pass over the arguments; a flat goal reads each once."
  [form]
  (if (sequential? form)
    (reduce (fn [d x] (if (sequential? x) (max (long d) (inc (long (term-depth x)))) d))
            0 (rest form))
    0))

(def default-max-term-growth
  "How many levels of compound nesting a subgoal may add over the deepest term its own
  derivation path has met (`term-depth`) before `prove-from` cuts the branch: the
  `:max-term-growth` bound, where a caller names none.  It catches the recursion the
  per-path `seen` set cannot, a rule nesting a function around a head variable.  The basis
  rises when a leaf match binds a deep stored term (`grown-term-base`) and never when a
  rule expands.  See docs/inference.md, max-term-growth."
  8)

(defn grown-term-base
  "`base` raised to the nesting the extension bindings `b` bring in: the depth a term bound
  to a variable contributes at a goal's top argument position, `1 +` its own
  (`term-depth`).  A leaf match reads what is stored, so a deep value is a fact about the
  KB and not about a rule growing a term."
  [base b]
  (reduce-kv (fn [d _ v] (if (sequential? v) (max (long d) (inc (long (term-depth v)))) d))
             (long (or base 0)) b))

;; ---- rule instances --------------------------------------------------------
;; A second use of a rule on one derivation path meets its first use's bindings; renaming the clash
;; apart gives each instance variables of its own.

(defn- path-names
  "Every variable name in play on `frame`'s path.  That is the frame's `:names`, which
  `prove-from` extends by what each frame it builds adds, so an expansion reads it in O(1).
  A frame built without one gets the names its bindings speak for (bound, and standing
  unbound inside their values) and its goals' variables, a walk of the whole path."
  [{:keys [names bindings goals]}]
  (or names
      (persistent!
       (reduce-kv (fn [acc k v] (reduce conj! (conj! acc k) (sx/form-variables v)))
                  (transient (sx/form-variables goals)) bindings))))

(defn- fresh-var
  "`?v'N`, N the size of `taken`, with a `'` appended for as long as `taken` holds the
  name.  Deterministic: a gensym would give an engine whose contract is order
  independence a different binding map on every run of the same query.  `prove-from`'s
  `taken` gains every name it mints, so N differs at each renaming on one path
  (docs/inference.md, \"Each rule instance gets its own variables\")."
  [v taken]
  (loop [s (str v "'" (count taken))]
    (let [c (sx/intern-sym (symbol s))]
      (if (contains? taken c) (recur (str s "'")) c))))

(defn freshen-rule
  "`rule` with every variable `taken` already speaks for renamed apart.  Without it,
  `(anc ?x ?z) :- (parentOf ?x ?y) (anc ?y ?z)` expanded twice on one path unifies `?x` with
  both the grandchild and the child and answers only at distance one.  Nothing is renamed
  when nothing clashes.  The `exceptWhen` guard reads the rule's own variable names from a
  completed binding map, so a renamed rule's guard is wrapped to bind those names to this
  instance's variables."
  [{:keys [antecedents consequent guard] :as rule} taken]
  (let [clash (when (seq taken)
                (into [] (filter taken) (sx/form-variables (cons consequent antecedents))))]
    (if (empty? clash)
      rule
      (let [m  (first (reduce (fn [[m tk] v]
                                (let [f (fresh-var v tk)]
                                  [(assoc m v f) (conj tk f)]))
                              [{} taken] clash))
            rn (fn [f] (walk/postwalk (fn [x] (if (sx/variable? x) (get m x x) x)) f))]
        (assoc rule
               :antecedents (mapv rn antecedents)
               :consequent  (rn consequent)
               :guard       (when guard
                              (fn [sol]
                                (guard (reduce-kv (fn [s orig fresh]
                                                    (assoc s orig (substitute fresh s)))
                                                  sol m)))))))))

(defn planned-antecedents
  "A rule's antecedents in the order they should be solved, given the bindings the head
  match produced.  Stored order is canonical (`sentex/canonicalize-rule`) and bears no
  relation to cost.  Reordering changes cost, never the answer set;
  `vaelii.impl.plan` fixes the evaluables and the recursive literal in place.  Antecedents
  are substituted before planning so the planner costs them against real values.
  `est-override` is passed through to `plan/order` (`provers/est-goal`)."
  ([kb antecedents consequent context bindings]
   (planned-antecedents kb antecedents consequent context bindings nil))
  ([kb antecedents consequent context bindings est-override]
   (plan/order kb
               (mapv #(substitute % bindings) antecedents)
               context
               (cond-> {:consequent-pred (when (sequential? consequent) (first consequent))}
                 est-override (assoc :est-override est-override)))))

;; ---- deferred antecedents (computed, not matched or expanded) -----------
;; A deferred literal (`sentex/deferred-predicates`) is computed by a prover from the other
;; antecedents' bindings, through the registry (`chain/solve-deferred`). This namespace sits below the
;; registry, so it reaches `provers/solve-goal` through `vaelii.impl.wiring`.

(defn solve-deferred
  "Extension binding-maps for a deferred antecedent `g` (already substituted, so its inputs
  are ground), computed by the prover registry through `wiring/solve-goal`.  Nothing when
  the literal is inapplicable (unbound inputs, a false test): the branch is pruned, the
  evaluable contract `vaelii.impl.plan` documents.  See docs/naf.md."
  [kb g context]
  (wiring/solve-goal kb g context))

;; ---- guard markers on the goal stack ------------------------------------
;; A rule's `exceptWhen` guard is pushed behind its antecedents, so the check runs once the argument
;; is complete.

(defn- ->guard-marker [guard] [::guard guard])
(defn- guard-marker? [g] (and (vector? g) (= ::guard (first g))))
(defn- marker-guard  [g] (second g))

;; ---- scope markers on the goal stack -------------------------------------
;; The loop guard belongs to a goal's derivation path, not its frame: a marker behind the antecedents
;; restores the `:seen` scope where the subtree ends, so a later conjunct repeating the goal-key is
;; not refused (`[(anc Tom ?y) (anc Tom ?z)]`).

(defn- ->scope-marker [seen] [::scope seen])
(defn- scope-marker? [g] (and (vector? g) (= ::scope (first g))))
(defn- marker-seen   [g] (second g))

;; ---- defeat markers on the goal stack ------------------------------------
;; A marker behind the antecedents checks the answer where it becomes ground. It sits behind the guard
;; and inside the scope, and is pushed only for a goal `defeatable-goal?` claims.

(defn- ->defeat-marker [goal] [::defeat goal])
(defn- defeat-marker? [g] (and (vector? g) (= ::defeat (first g))))
(defn- marker-goal    [g] (second g))

;; ---- answers belief has already decided against -------------------------
;; The proving levels agree with belief: a conclusion the JTMS holds defeated is not re-derived through
;; a rule, including a defeated premise reached by another route. Only `defeated`; `blocked` is swept and
;; `superseded` is rewritten before any prover runs. The stored-fact leaf is already filtered by
;; `matches-visible`. See docs/inference.md, "Answers belief has already decided against".

(defn defeated-index
  "What the backward chainers filter a rule-expanded answer against: `{:standing
  {sentence #{handle}} :functors #{functor}}` over the targets of the placed defeats
  (`reads/as-stored-named-global`) and, while an `except` is stored, the members of the
  placed `(contradicts …)`.  Nil when the walk reads nothing (`exc/placed-reads?`), the
  common case.  `:functors` keeps the cost off a KB with a defeat on another predicate.
  Built once per query, since a query writes nothing.  `defeated-answer?` asks the query's
  reader whether it takes a member OUT (docs/nmtms.md, A defeat is scoped to its vantage)."
  [kb]
  (when (exc/placed-reads? kb)
    (let [recs    (:records kb)
          members (when (reads/stores-any? (:index kb) sx/except-functor)
                    (into [] (comp (keep #(:sentence (p/get-sentex recs %)))
                                   (filter #(and (seq? %) (= 'contradicts (first %))))
                                   (mapcat rest)
                                   (keep sx/handle-id))
                          (p/sentexes-with-functor (:index kb) 'contradicts)))]
      (reduce (fn [idx h]
                (if-let [sx (p/get-sentex recs h)]
                  (-> idx
                      (update-in [:standing (sx/sentence-of sx)] (fnil conj #{}) h)
                      (update :functors conj (nm/functor (sx/sentence-of sx))))
                  idx))
              {:standing {} :functors #{}}
              (into (reads/as-stored-named-global (:index kb) sx/defeat-functor) members)))))

(defn defeatable-goal?
  "Could an answer to `goal` be one belief has already defeated — is its functor one some
  defeated datum carries?  False for every goal when `idx` is nil.

  This is the push-time presence check: a chainer that answers false here adds no check to
  the goal at all,
  so a KB with no defeat on that predicate runs the search it always ran."
  [idx goal]
  (boolean (and idx (contains? (:functors idx) (nm/functor goal)))))

(defn defeated-answer?
  "Is `sentence`, an answer a rule expansion produced, a stored member of a nogood
  (`defeated-index`) that a defeat in force, or a placed conflict, removes at the query's
  reader (`exc/defeats-of`): `context` for a concrete one, the member's own context for an
  unscoped read?  A guard defeat covers one firing and removes no answer.  Canonicalized
  against the KB (`kb-sentex`) before the lookup."
  [kb idx sentence context]
  (boolean
   (when idx
     (when-let [hs (get (:standing idx) (sx/sentence-of (kb-sentex kb sentence context)))]
       (let [own? (or (nil? context) (sx/variable? context))]
         (some #(seq (exc/defeats-of kb % (if own? (:context (p/get-sentex (:records kb) %)) context)))
               hs))))))

(defn believed-at?
  "Is `handle` believed as `context` reads it: IN in the network, and not hidden from
  `context` by a placed `defeat` in force there, or by resting only on a handle one hides
  (`exc/belief-hidden-fn`)?  The stored excepts are not applied, since an `except` is
  visibility and this is belief.

  The reader for a caller holding a sentex and no reader is the sentex's own context.  A
  sentex resting only on a member every reader of it hides is IN in the network and
  hidden from every context that can read it, and this answers false for it."
  [kb handle context]
  (boolean (and (jtms/in? (reasoning/tms kb) handle)
                (not (when-let [hid (exc/belief-hidden-fn kb context)] (hid handle))))))

;; ---- dead ends -----------------------------------------------------------

(def ^:dynamic *dead-end*
  "An optional observer of the DFS's dead ends, `(fn [goal depth])`, or nil (default).  A
  dead end is a subgoal, substituted under the frame's bindings, that no visible believed
  fact and no rule consequent unified with.  A branch cut short (loop guard, `:max-depth`,
  term-growth ceiling) is not reported.  The return value is ignored.  Only `prove`'s
  loop reports.  docs/abduction.md, The dead end."
  nil)

(defn- leaf-solutions
  "Extension bindings for `g` without expanding any rule: the chainer's leaf.  nil
  `leaf-solver` reads the stored facts (`matches-visible`).  `vaelii.core/prove` and
  `vaelii.core/query` pass the registry, so an antecedent can be answered by any prover
  (transitivity, an evaluable, an inferred argument type)."
  [kb g context leaf-solver]
  (if leaf-solver
    (leaf-solver kb g context)
    (map (fn [m] (nth m 1)) (matches-visible kb g context))))

(defn initial-prove-stack
  "The one-frame DFS stack `prove` starts from: the cost-ordered conjunction, no bindings,
  an empty loop guard, depth 0, the answer variables and the query's term depth
  (`term-depth`), the basis the term-growth cut starts from (`grown-term-base`).  They
  ride the stack because the stack is the continuation.  `prove-within` seeds a bounded
  run with it and hands the unfinished stack to `resume`.  `est-override` costs the top
  conjunction as in `planned-antecedents`."
  ([kb goals context] (initial-prove-stack kb goals context nil))
  ([kb goals context est-override]
   [{:goals       (plan/order kb goals context {:est-override est-override})
     :bindings    no-bindings
     :seen        #{}
     :depth       0
     :answer-vars (sx/form-variables (vec goals))
     :names       (sx/form-variables (vec goals))
     :term-base   (reduce (fn [d g] (max (long d) (long (term-depth g)))) 0 goals)}]))

(defn prove-from
  "The resumable core of `prove`: run the DFS from an explicit `stack` (and the
  `solutions` so far) under `bounds`, a map of optional caps:
    :deadline `System/nanoTime` instant   :max-results   :max-depth   :max-term-growth
    :leaf-solver (see `leaf-solutions`)   :est-override (see `planned-antecedents`)
  Returns `{:solutions <vector> :status <kw> :stack <frames>}`; `:status` is `:complete`
  (`:stack` empty), else `:timeout` or `:capped` with a non-empty `:stack` to resume from.
  A leaf the deadline stops inside goes back on the stack marked `:unbounded-leaf?`.
  With `bounds` nil it runs to completion."
  [kb rules-fn context
   {:keys [deadline max-results max-depth max-term-growth leaf-solver est-override]}
   stack solutions]
  ;; One search scope per segment (`observe/with-search-scope`); the loop is eager, as the macro needs.
  ;; `prove-seq` opens a scope per call, which is sound because a query writes nothing. The defeated set is
  ;; read once per segment, in a `delay` so a run that expands no rule never touches the TMS.
  (let [defeated (delay (defeated-index kb))]
    (observe/with-search-scope
      (loop [stack stack, solutions solutions]
        (cond
          ;; Exhaustion is checked first, so `:complete` means the space was genuinely
          ;; emptied — never "we hit the cap on the last element".
          (empty? stack)
          {:solutions solutions :status :complete :stack stack}

          (and max-results (>= (count solutions) max-results))
          {:solutions solutions :status :capped :stack stack}

          (and deadline (>= (System/nanoTime) deadline))
          {:solutions solutions :status :timeout :stack stack}

          :else
          (let [frame (peek stack)
                {:keys [goals bindings seen depth answer-vars term-base]} frame
                ;; every variable name in play on this path (`path-names`), carried down
                names (path-names frame)
                stack (pop stack)
                ;; The ceiling on a subgoal's nesting: the deepest term met on the path plus the growth allowance.
                ;; Stacks carry the base and bounds the allowance, so a `resume` measures from the same base.
                ceiling (+ (long (or term-base 0))
                           (long (or max-term-growth default-max-term-growth)))]
            (cond
              (empty? goals)
              (recur stack (conj solutions (project-answer bindings answer-vars)))

              ;; A guard marker: the antecedents ahead of it are solved, so the `exceptWhen` exception is asked of the
              ;; completed binding. A marker is a vector and a goal never is (`quasiquote/prepare-conjunction-for-read`).
              (guard-marker? (first goals))
              (recur (cond-> stack
                       ((marker-guard (first goals)) bindings)
                       (conj {:goals (rest goals) :bindings bindings :seen seen :depth depth
                              :answer-vars answer-vars :names names :term-base term-base}))
                     solutions)

              ;; the rule expansion behind this marker has produced an answer for the goal
              ;; it was opened for, and belief may already have decided against that answer
              (defeat-marker? (first goals))
              (recur (cond-> stack
                       (not (defeated-answer? kb @defeated
                              (substitute (marker-goal (first goals)) bindings)
                              context))
                       (conj {:goals (rest goals) :bindings bindings :seen seen :depth depth
                              :answer-vars answer-vars :names names :term-base term-base}))
                     solutions)

              ;; the expanded goal's subtree ends here: the conjuncts still queued behind
              ;; it are siblings, not descendants, and answer under the scope it started in
              (scope-marker? (first goals))
              (recur (conj stack {:goals (rest goals) :bindings bindings
                                  :seen (marker-seen (first goals)) :depth depth
                                  :answer-vars answer-vars :names names :term-base term-base})
                     solutions)

              ;; A deferred goal (`different` / `evaluate` / `unknown`) is *computed* by the
              ;; registry, not matched or expanded: push one continuation frame per extension
              ;; binding, and no rule frames (see `solve-deferred` above).
              (sx/deferred-literal? (substitute (first goals) bindings))
              (let [g          (substitute (first goals) bindings)
                    rest-goals (rest goals)
                    frames     (for [b (solve-deferred kb g context)]
                                 {:goals rest-goals :bindings (merge bindings b)
                                  :seen seen :depth depth :answer-vars answer-vars
                                  :names (into names (sx/form-variables (vec (vals b))))
                                  :term-base term-base})]
                (recur (into stack frames) solutions))

              :else
              (let [g     (substitute (first goals) bindings)
                    solve #(vec (leaf-solutions kb g context leaf-solver))
                    ;; The leaf runs walks longer than one step, so the deadline reaches inside; a stopped walk leaves this
                    ;; frame on the stack, marked to run unbounded on resume.
                    leaf  (if (or deadline (:unbounded-leaf? frame))
                            (budget/interruptible (when-not (:unbounded-leaf? frame) deadline)
                                                  solve)
                            (solve))]
                (if (identical? ::budget/interrupted leaf)
                  {:solutions solutions :status :timeout
                   :stack     (conj stack (assoc frame :unbounded-leaf? true))}
                  (let [rest-goals (rest goals)
                        k          (goal-key g)
                        ;; A leaf match may bind a deep stored term that is not rule growth, so the basis rises with it
                        ;; (`grown-term-base`).
                        fact-frames (for [b leaf]
                                      {:goals rest-goals :bindings (merge bindings b) :seen seen
                                       :depth depth :answer-vars answer-vars
                                       :names (into names (sx/form-variables (vec (vals b))))
                                       :term-base (grown-term-base term-base b)})
                        ;; Expansion cut short, not exhausted: the goal re-enters its path, the depth bound bit, or the term
                        ;; ceiling was passed (`default-max-term-growth`); see `*dead-end*`. Facts are still read.
                        cut?        (or (contains? seen k)
                                        (boolean (and max-depth (>= depth max-depth)))
                                        (> (long (term-depth g)) ceiling))
                        ;; asked once per expanded goal rather than once per rule: whether an
                        ;; answer to this goal *could* be one belief has defeated is a property
                        ;; of the goal, and it is false for every goal on a KB with no defeats
                        defeatable? (and (not cut?) (defeatable-goal? @defeated g))
                        rule-frames (when-not cut?
                                      (for [rule (rules-fn g)
                                            :let [{:keys [antecedents consequent guard]}
                                                  (freshen-rule rule names)
                                                  b (subsuming-unify kb g consequent bindings context)]
                                            :when b]
                                        ;; pushed onto the front of `rest-goals` in reverse, so a step costs this rule's goals only
                                        {:goals    (into rest-goals
                                                         (rseq
                                                          (-> (planned-antecedents
                                                               kb antecedents consequent context b
                                                               est-override)
                                                              (cond-> guard (conj (->guard-marker guard)))
                                                              ;; behind the guard, so an excepted
                                                              ;; firing is refused before belief
                                                              ;; is asked about its answer
                                                              (cond-> defeatable?
                                                                (conj (->defeat-marker g)))
                                                              ;; behind both: the scope is
                                                              ;; restored once this rule's own
                                                              ;; subtree is finished with it
                                                              (conj (->scope-marker seen)))))
                                         :bindings b
                                         :seen     (conj seen k)
                                         :depth    (inc depth)
                                         :answer-vars answer-vars
                                         :names    (into names (sx/form-variables
                                                                (cons consequent antecedents)))
                                         :term-base term-base}))]
                    (when (and *dead-end* (not cut?)
                               (empty? fact-frames) (empty? rule-frames))
                      (*dead-end* g depth))
                    (recur (into stack (concat fact-frames rule-frames)) solutions)))))))))))

(defn prove
  "A depth-first backward chainer over an explicit goal stack.  Returns a vector of
  resolved solution binding maps proving the conjunction `goals` in `context`.  A per-path
  `:seen` set of goal-keys and the term-growth ceiling (`default-max-term-growth`) make
  every search terminate on the data.  Prefer right-recursive rules: a left-recursive rule is
  pruned after its first expansion.  `rules-fn` maps a subgoal to candidate rules.  The 5-arg arity takes `prove-from`'s `bounds` (the
  keys of `prove-seq` plus `:max-results`), e.g. a registry leaf
  `{:leaf-solver provers/solve-goal :est-override (provers/registry-est-override kb ctx)}`;
  the 4-arg keeps the stored-fact leaf."
  ([kb rules-fn goals context] (prove kb rules-fn goals context nil))
  ([kb rules-fn goals context bounds]
   (:solutions (prove-from kb rules-fn context bounds
                           (initial-prove-stack kb goals context (:est-override bounds)) []))))

(defn prove-seq
  "The same search as `prove`, lazily: a seq of solution binding maps costing one solution
  per pull.  Runs `prove-from` capped at one result and resumes from the `:stack` it left;
  `:capped` is the only status that continues.  `bounds` takes `prove-from`'s keys except
  `:max-results`.  Each segment opens its own search scope, which is sound because a query
  mutates no belief.  See docs/inference.md, Resolution reads."
  ([kb rules-fn goals context] (prove-seq kb rules-fn goals context nil))
  ([kb rules-fn goals context bounds]
   (let [bounds (assoc bounds :max-results 1)]
     (letfn [(step [stack]
               (lazy-seq
                (let [{:keys [solutions status stack]}
                      (prove-from kb rules-fn context bounds stack [])]
                  (concat solutions (when (= :capped status) (step stack))))))]
       (step (initial-prove-stack kb goals context (:est-override bounds)))))))
