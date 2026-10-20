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
            [vaelii.impl.capabilities :as cap]
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
  rest pattern `(head ... . ?rest)` is spliced: the substituted tail is concatenated
  in, so `(?pred . ?args)` with `?args=(Tom Bob)` becomes `(parentOf Tom Bob)`.  A
  `(Quote X)` form comes back whole: a variable inside it is part of the quoted
  expression, which `unify` never binds.

  **Eager, and a `PersistentList`.**  This is the innermost function on every join, every
  rule expansion and every proof hop, and what it builds goes straight into
  `sentex/canon`, which flattens any sequential to a `PersistentList` anyway.  Answering
  with `map`'s lazy seq would allocate a `LazySeq` *and* a `Cons` per element — each with
  a lock the realizing thread takes — for a sequence three to five elements long that is
  walked again a microsecond later.  `mapv` fills one transient vector and
  `PersistentList/create` conses it up in reverse, so a substituted literal costs two
  eager passes and no lazy machinery at all."
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
  "A finished derivation's bindings, resolved and cut down to the variables the *query*
  asked about.  `nil` `answer-vars` projects nothing, for a caller driving the chainer
  from a stack it built itself.

  **A derivation path accumulates one flat binding map**, and every rule instance it
  expands contributes its own variables to it — a stored rule is spelled `?var0 ?var1 …`
  and each instance is renamed apart again (`freshen-rule`), so a six-rule proof of a
  two-variable query resolves fourteen names.  Those are scratch: they are how the search
  got there, not what it was asked.  Projecting is what makes a solution a map over the
  question rather than over the proof, and it is what lets two engines that reach the
  same answer by different derivations return the same value.

  Note the projection is by name, not by provenance.  A query that itself writes `?var0`
  is asking about `?var0`, and gets it — the canonical rule spelling is a spelling, and a
  variable belongs to whoever wrote it."
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
  "Whether `match-one` may retrieve its candidate handles from a **secondary argument
  root** instead of always walking the trie.

  The trie narrows strictly left to right, so a pattern whose *first* argument is a
  variable but a later argument is a ground term — `(parentOf ?x Tom)`, the second
  half of a grandparent join — cannot be answered by a prefix: the trie fans out over
  every first-argument value (one lookup per node) only to keep the few
  that match the later token.  The argument-root node `[pred pos term]` indexes exactly
  that later position under the pattern's own predicate, so it answers the same pattern
  with one read per context the node lists (one, for a ground pattern context).

  When several arguments are known, `candidate-handles` intersects the pattern's
  scoped argument roots (`sentexes-with-args` — the scoping means a named functor
  needs no predicate-extent intersection), so knowing more of the sentence narrows on all
  of it at once instead of one column.
  The set it returns is a **superset** of the trie's hits — `match-one`'s existing
  `unify` filters it to the identical result (the trie's own hit set *is* the
  unifiable set, and the roots' intersection ⊇ that).  So this changes only *how* the
  candidates are fetched, never *which* sentexes match.  Binding it false forces the
  trie, which is what `arg_root_retrieval_test` compares against.  True by default — a
  strict improvement on the after-a-variable case and a no-op everywhere else."
  true)

(def ^:dynamic *structural-index*
  "Whether `candidate-handles` may use the **structural trie** to narrow a positive
  pattern with a nested compound argument — `(mass ?o (QuantityFn ?n Kilogram))`.

  A positive fact's key linearizes its compound arguments into the trie path (see
  `vaelii.impl.sentex`), so `QuantityFn` and `Kilogram` sit at their own trie levels
  and `p/lookup` narrows on them even when the top-level argument is a
  partially-variable compound — the one case the argument roots (top-level only) and
  the flat trie both leave to a full functor-extent fan.  On (default), that pattern
  is answered by the structural trie; off, by the **functor extent** — a correct
  superset the existing `unify` filters to the identical set, and the conservative
  baseline the structural selectivity is measured against (`structural_index_test`,
  modeled on `arg_root_retrieval_test`).

  The structural key is written unconditionally, so the direct `p/lookup` paths
  (`find-sentex-handle`, the level-0 raw lookup) always walk it; `query` and the
  matching levels go through `candidate-handles`, so this switch decides *their* candidate
  source too — never correctness: on and off return the same matches, on returns fewer
  candidates.  Negative and flat patterns are untouched — a `:false` key keeps its body
  whole, so it has no deep positions to narrow on.

  On by default: the oracle (`structural_index_test`) proves on == off over the
  corpus, and the structural retrieval is a strict candidate-set win on a
  compound-argument pattern (2 candidates vs the functor extent), so there is no
  reason to prefer the looser fallback."
  true)

(defn- ctx-scope
  "The contexts an argument-root read of pattern sentex `pat` is restricted to: its own
  context when that is ground, every context (nil) when it is a variable."
  [pat]
  (let [c (:context pat)] (when-not (sx/variable? c) #{c})))

(defn- candidate-handles
  "The stored handles to unify `pat` against — always a superset of the positional
  trie hits (so `match-one`'s `unify` filters it to the identical set), chosen to
  minimize index lookups.

  The trie narrows only left to right, so it is at its best when the *ground*
  arguments form a left prefix — `(parentOf Tom ?y)`, `(parentOf Tom Bob)` — and at
  its worst when a ground argument sits **after** a variable, `(parentOf ?x Tom)` or
  `(rel A ?y C)`, which it can reach only by fanning out over the intervening
  variable (a round trip per value).  For exactly that case the secondary roots are a
  *different* index order that binds the stuck position directly, and — the point of
  this refinement — intersecting **every** ground argument's predicate-scoped root
  narrows on all the known terms at once (`sentexes-with-args`: one hash lookup when a
  single argument is bound, an intersection when several are) rather than picking one
  column and deferring the rest to a per-record filter.  So knowing more of the
  sentence buys a tighter candidate set, not just the same one.

  **The functor is a position too.**  `(?type Muffet)` — what types does Muffet hold —
  is the same shape at level 0: the variable is the *first* path token, so every
  ground argument sits behind it and the trie can only fan out over the whole root
  child set, i.e. every functor in the KB.  That fan is linear in the vocabulary,
  which is the largest thing in a broad ontology.  The predicate-agnostic read spans
  every functor by construction — a union of the scoped roots over the slot predicate set —
  so one `sentexes-with-arg` read of position 1, `Muffet` answers it flat; with no
  predicate to scope by, `sentexes-with-args` takes a `nil` `pred` and intersects
  those predicate-agnostic reads.

  A positive pattern with a **nested compound argument** is the third source: its
  selective information sits *inside* the compound (`QuantityFn`, `Kilogram`), which
  neither a left prefix nor a top-level argument root reaches.  The structural trie
  narrows on it (`*structural-index*`); off, it falls back to the functor extent — a
  correct superset, and the baseline to measure the structural narrowing against.

  **The context is a position too, and the trie's last.**  `(parentOf Tom ?y)` in a
  ground context `C` has a left prefix, but the trie walk fans over every stored `?y`
  under `[parentOf Tom]`, in every context, before it reaches the context level.  The
  argument roots end in the context, so a pattern whose arguments are variables and
  indexable terms, at least one of each, reads the nodes' leaves in `C` alone
  (`ctx-scope`): its candidates are the matches stored in `C`, not those stored
  anywhere.  A pattern whose arguments are all variables reads the predicate extent's
  leaf in `C` (`:context-extent`), for the same reason.

  Everything else keeps the trie: a fully-ground test (its leaf is exact), a pattern
  whose ground arguments are a left prefix under a variable context, and a pattern whose
  only after-a-variable selectivity is a **non-indexable** token (a number/string the
  roots do not key), where the trie's own token narrowing beats a predicate-extent scan.
  Zero-regression by construction — the diverted cases are the ones the trie answers
  with a fan-out.

  **The decision is named before it is taken.**  The `cond` below yields one of seven
  keywords and the `case` under it does the read, so the access path a shape chose is a
  value: `vaelii.impl.profile` tallies it, and a reader has a word for each branch rather
  than a position in a `cond`."
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
            ;; something is still open and a ground root sits past it — the functor
            ;; being open (`(?type Muffet)`) puts *every* argument behind it, and with
            ;; nothing indexable to lead with there is no root to read, so the trie
            ;; keeps that case
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
              ;; **A negative key holds its whole body as one token**, so the trie can match
              ;; a negative only *exactly* — `[:false (dog ?0) c]` is a different key from
              ;; `[:false (dog Tom) c]`, and no amount of the body being ground narrows it,
              ;; because none of it is a level.  So `p/lookup` answers `#{}` for every open
              ;; negative, and this is correctness rather than cost: the matches are not
              ;; merely reached slowly, they are not reached at all.
              ;;
              ;; The secondary indexes are the only ones that see inside a negative: the
              ;; predicate extent spans both polarities (a negative roots under its positive
              ;; body's functor) and so do the argument roots.  With neither bound — an
              ;; open functor over open arguments — the `:false` node's own children are
              ;; the negative analogue of the root child fan a fully-open positive gets,
              ;; and they are exactly the distinct negative bodies stored.
              ;;
              ;; Unconditional, unlike the cost refinements below: `*arg-root-retrieval*`
              ;; false is meant to give the trie as a *reference*, and for this shape the
              ;; trie has no answer to be a reference for.
              (and (sx/negative? pat) (not (sx/ground-term? body)))
              (if (or pred (seq ground)) :negative-roots :negative-fan)

              ;; A ground argument sitting **after** a variable, which the trie can reach
              ;; only by fanning out over the intervening variable.  This wins over the
              ;; structural walk below even when the stuck argument is a compound: the
              ;; argument root keys the compound *whole*, so it binds in one read what the
              ;; linearized trie key still has to fan out to reach.  A ground context
              ;; behind an open argument is the same shape at the trie's last level.
              (and *arg-root-retrieval* (or stuck? scoped?)) :arg-roots

              ;; Every argument open in a ground context: the trie fans over every stored
              ;; argument under the functor before it reaches the context level, and the
              ;; predicate extent ends in the context, so its leaf there is the whole
              ;; candidate set.
              (and *arg-root-retrieval* extent?) :context-extent

              ;; a positive pattern with a nested compound argument — the structural case.
              ;; The trie key linearizes the compound, so `p/lookup` narrows on its interior;
              ;; off, the functor extent is the correct fallback superset.  A variable functor
              ;; roots nothing, so it always takes the trie.
              (and (not (sx/negative? pat)) (some sequential? args))
              (if (or *structural-index* (nil? pred)) :structural :functor-extent)

              ;; trie: left-prefix, test, or number-only
              :else :trie)]
        (prof/record-goal pat path)
        (case path
          ;; a ground context is matched exactly (`match-one` unifies it), so the argument
          ;; roots read that context's leaves alone
          :negative-roots (p/sentexes-with-args ix pred ground (ctx-scope pat))
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
  was written at.  A forced-monotonic literal goes OUT only by retraction (docs/nmtms.md, \"The
  forced-monotonic set\"), so a declaration and the part edges a `covering` installs
  hold for every term as a `:monotonic` edge does."
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
  "Unify a single antecedent pattern against a ground fact sentence, honoring
  **predicate specificity**: a fact whose functor is a *spec* (sub-predicate, via the
  genl closure) of the antecedent's functor satisfies it, with the arguments unified.

  For a unary type antecedent this is the ordinary subtype rule — `(animal ?x)` is met
  by `(dog Muffet)`.  Generalized to n-ary predicates, `(parentOf ?x ?y)` is met by
  `(fatherOf Tom Bob)` once `(genl fatherOf parentOf)` holds — the same subsumption the
  type hierarchy gives, applied to the predicate hierarchy.  When the functors are
  equal (the common case) or the antecedent's functor has no sub-predicates, this is a
  plain unify, so nothing changes for a KB without predicate-genl edges.

  **Under a negation the fan reverses**, because a `genl` edge carries the other way
  through one: `dog ⊑ animal` makes `(dog Muffet)` satisfy `(animal ?x)` and makes
  `(not (animal Muffet))` satisfy `(not (dog ?x))` — the contrapositive, so a negated
  antecedent is met by a negative fact on a **genl** of its body's predicate.  The two
  directions are exclusive: `(not (dog Muffet))` does not satisfy `(not (animal ?x))`,
  which is the reading a fan in the positive direction would give it.  Both sides must
  be negations for this to apply; a negation matched against a positive fact fails on
  polarity as it does anywhere else.  The negated fan climbs only the edges the reader
  holds at `:monotonic` (`contrapositive-predicates`): a `:default` edge does not
  contrapose.

  **The subsumption is scoped when a `context` is given**: the predicate-genl closure is
  walked only through the edges that context can see, so a match reached through a `genl`
  edge stated in a context the reader cannot see is not a match for it — a watcher in one
  context stops answering through another's edge (`core/watch-match`), agreeing with what
  `ask` from that context would say.  The two-arity is unscoped, for the callers that fix
  visibility elsewhere: the forward trigger match (`chain/fire-rules-for`) is a candidate
  filter whose placement re-derives the genlCx supporters the firing then rests on, so a
  subsumption invisible to the placement context drops out at placement, not here."
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
  "Unify a query `goal` against a rule's `consequent`, honoring **predicate
  specificity**: a consequent whose functor is a *spec* (sub-predicate/subtype, via
  the genl closure) of the goal's functor still answers the goal, so its argument
  lists unify and the goal variable binds to the more specific instance.  This is the
  backward dual of `match1` — where a subtype *fact* satisfies a supertype antecedent,
  here a subtype *conclusion* satisfies a supertype goal.

  Equal functors (the common case), a variable goal functor, or a functor with no
  sub-predicates all fall through to a plain `unify` over the whole sentences, so
  nothing changes for a KB without predicate-genl edges, and a rule concluding a
  *supertype* or an unrelated predicate is correctly rejected (the functors do not
  unify).

  **Under a negation the fan reverses**, exactly as it does in `match1`: a rule
  concluding `(not (animal ?x))` answers the goal `(not (dog Tom))`, because `dog ⊑
  animal` entails `¬animal ⊑ ¬dog`, through the edges the reader holds at `:monotonic`
  only (`contrapositive-predicates`).  Both sides must be negations; a negated goal
  against a positive consequent falls through to the plain `unify`, which rejects it on
  the functor.

  **Scoped in lockstep with `match1`** (its forward twin): with a `context`, the
  predicate-genl closure is walked only through the edges that context can see.  The
  backward callers already scope the *candidate rule set* upstream
  (`concluding-rule-handles … context`, via `provers/candidate-rules`), which reads the
  same scoped closure — so passing the context here changes no answer today, and keeps
  a future caller that skips that filter from subsuming through an invisible edge.  The
  arities without a context are unscoped, for a caller with no vantage in hand."
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
  "Handles of rules whose consequent predicate is `pred` **or a spec of it** — a rule
  concluding a subtype answers a supertype goal, the backward dual of `fire-rules-for`
  fanning a new fact over its supertypes.  Computed as the intersection `specs(pred) ∩
  rules-by-consequent`: iterate the spec closure and probe the consequent index.  A
  non-symbol `pred` cannot be a type, so it degrades to the plain lookup.

  **Plus the variable-consequent catch-all.**  A rule concluding `(?p ?y ?x)` files its
  consequent under `p/var-consequent-key` rather than under any concrete predicate (see
  `rules/consequent-index-pred`), and could conclude *any* predicate once `?p` binds — so
  its bucket is unioned into every answer.  Without it a goal on `likes` never discovers
  a rule concluding `(?p …)`, and backward chaining is blind to exactly the rules the
  consequent-var-pred feature exists to make reachable.

  **A variable `pred` is the dual**: the goal `(?p Tom ?y)` names no consequent bucket
  and any rule may conclude it, `subsuming-unify` binding `?p` to the consequent's
  functor.  So it answers **every** rule stated where `visible` reaches, read off the
  rule extent (`reads/as-stored-rules-in`).  Paid only for a variable functor, which
  fact matching already answers through the argument roots; without it the open functor
  reached stored facts and silently no rule.

  **The answer is bounded by the concluding rules; the cost is bounded by the taxonomy.**
  One index probe per spec, so a goal on a type with 364 subtypes takes 364 probes to
  discover that no rule concludes any of them — and `provers/shadowing-channels` asks
  this once per goal, on the path `sole-prover` takes.  Cheap per probe and never a
  record fetch, but it is the spec closure that sizes it, not the rule count.

  With a `context`, the spec fan walks only the genl edges visible from it — a rule
  concluding a subtype answers a supertype goal exactly where the subtype edge is
  visible, mirroring the matching fan-out.  With `visible` as well, a context set, every
  index read returns only the rules stated in one of those contexts: both rule indexes
  end in the context, so a rule stated where the reader cannot see is never read."
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
  "Is `concluding-rule-handles` non-empty, asked in every context — the same buckets,
  read until the first one holding a rule.

  `provers/shadowing-channels` asks only this, once per goal.  Built as the whole set, the
  answer cost a probe per spec of the goal's predicate whatever the first probe found: a
  ground `(different A B)` under 3,054 sub-predicates and 3,050 swapped ones took 12 ms,
  and a forward join tests one per row.  The variable-consequent catch-all is read first,
  since a rule filed there concludes every predicate, so a KB holding one answers in one
  read.

  It reads every context, past the reader's ancestor set, because the answer only decides
  whether a computed prover may answer alone: a rule the reader cannot see sends the goal
  down the union path, which costs time and never an answer."
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
  "May a rule stored in `rule-ctx` answer a goal asked from `context`?

  A rule is a sentex, so it is inherited like any other: a context reasons with the
  rules its `genlCx` ancestor set holds and no others.  This is the backward dual of
  forward chaining refusing to place a conclusion in a context that cannot see the
  rule — without it a context proves `(ancestorOf Tom Bob)` from a rule some
  sibling theory wrote, while the *forward* firing of that same rule correctly
  evaporates for want of a placement, and the two chainers disagree about one KB.

  An open `?ctx` (or nil) is the unscoped path: such a query asks about the KB rather
  than from a vantage, exactly as the closure reads read it."
  [kb context rule-ctx]
  (or (not (and (symbol? context) (not (sx/variable? context))))
      (tax/sees? (reasoning/taxonomy kb) context rule-ctx)))

(def ^:dynamic *belief-blind*
  "Read the store as **stored** rather than as believed — `CxEverything`, and nothing
  else.

  This is a named opt-out of the fourth invariant (\"a stored sentex is not a believed
  one\", README.md), which is why it is a dynamic var scoped to one read by the entry point that
  resolves the symbol, and not an option any caller can set.  It gives a
  *syntactic* query: unification against the store with no JTMS read at all, which is both
  the cheapest question the engine can be asked and the only one that can see a defeated
  default.

  What it does **not** license is a belief claim.  An answer taken under this flag is not
  a justification and must not reach `why` or read as one — `provable?` under
  `CxEverything` says a derivation is *spelled* in the store, not that the KB holds it."
  false)

(defn belief-blind?
  "`*belief-blind*`, read **once** by a retrieval path rather than once per candidate.

  The distinction is the whole reason this is a function and not a bare deref at each
  filter.  A `^:dynamic` deref is a thread-bound check on every read, and the belief filter
  sits in the innermost loop retrieval has — once per *candidate handle*, of which a broad
  literal has thousands.  Read into a local at the top of the path and the per-candidate
  cost is an `or` against a boolean that short-circuits; read at the filter and it is a
  var deref per handle, which `negation-arbitration` is close enough to its bound to see.

  Correct to hoist because the value cannot change under a path: the entry point binds it around
  the whole read and `blind-seq` re-establishes it per realization step, so whichever of
  those constructed this seq had it bound already."
  []
  *belief-blind*)

(defn blind-seq
  "`s`, realized under `*belief-blind*` — one element at a time, with the binding
  re-established for each.

  A plain `(binding [*belief-blind* true] (read …))` is **wrong here and silently so**,
  which is the whole reason this exists.  Every read entry point answers with a lazy seq, so the
  binding frame is popped the moment the entry point returns and long before the first element is
  computed: the belief filter then runs unbound, the read answers exactly what an ordinary
  belief-following one would, and nothing anywhere reports that the flag did not take.
  Wrapping the seq puts the binding back on the stack for each realization step — the
  `seq` call and the `first` below both force inside it, chunk and all — so laziness
  survives and so does the flag."
  [s]
  (lazy-seq
   (binding [*belief-blind* true]
     (when-let [c (seq s)]
       (cons (first c) (blind-seq (rest c)))))))

(defn rule-believed?
  "May the rule at `handle` chain — is it believed?

  A rule is a sentex, so the fourth invariant holds of it as it holds of a fact: a
  *stored* rule is not a *believed* one.  Both chainers reach a rule through the rule
  index, which posts on storage and knows nothing of belief, so without this a rule
  whose support has gone on holding conclusions the KB no longer has grounds for — and
  a **derived** rule (one a generator generated, docs/generators.md) would never come
  back out of the KB at all, since retracting what licensed it is the only way it can
  leave.

  A sentex the TMS holds no node for is available, not disbelieved: answering \"not
  believed\" of an absence would be reading it as a verdict, where what it says is that
  the network was never asked.  For a **rule** that arm is defence rather than a live
  case — `core/assert-inert` refuses a rule (`:not-indexable`), so a stored rule has
  been through an entry point that premised it — and it is worth keeping only because a wrong
  answer here is a rule that silently stops firing.

  An **inert rule** is a different thing and is *not* what this arm is about: it is
  believed like any other rule and kept from firing by its `:engines` alone
  (`rules/forward-sentex?` / `backward-sentex?`), which is what makes it documentation
  rather than an absence (docs/inference.md)."
  [kb handle]
  (let [tms (reasoning/tms kb)]
    (or *belief-blind*
        (not (jtms/known-datum? tms handle))
        (jtms/in? tms handle))))

(defn supporter-believed?
  "Is stored supporter `handle` believed from `context` — IN in the network, and not
  hidden there by a believed `except` or a placed `defeat` in force at `context`, or by
  resting only on a hidden handle (`exc/excepted?`, the read walk)?  `defeats?` false
  reads the excepts alone (`exc/excepted-in-network?`).

  The taxonomy's `visible?` callback (`kb/attach-visibility!`), so it decides whether a
  closure walk may cross an edge.  Both kinds of hiding apply: a context that
  disbelieves a `genl` edge must stop reaching over it, or `believed?` of the edge and
  `genl?` / `isa?` / `ask?` over it answer differently about one KB from one context.

  **What the callback may ask, and why the recursion does not close.**  Every ancestor-set
  read inside `exc/excepted?` goes through `tax/context-up-global` — `exc/except-hidden-fn`,
  `exc/visible-exception-index` and the read walk's `exc/reader-state` each take it by name — so asking it from
  inside a scoped walk reads the *unfiltered* genlCx closure and never re-enters the
  filtered one.  That holds for a `:genlCx` read as much as for a `:genl` one, and it is
  the same reason exception evaluation reads that closure rather than `context-up`.  The
  read walk runs `jtms/region-in`, which reads justifications alone and requires no
  taxonomy.

  Assertion-context inheritance is still not answered here: taxonomy's scoped edge/cache
  readers already apply it, and genlCx declarations are forced universal."
  ([kb handle context] (supporter-believed? kb handle context true))
  ([kb handle context defeats?]
   (boolean
    (and (jtms/in? (reasoning/tms kb) handle)
         ;; The context-sensitive cascade walk runs only when an except or a defeat is
         ;; stored: only a KB that can hide something runs it.  `placed-reads?` comes first
         ;; because it is two count reads on the index where
         ;; `exc/closure-excepted-anywhere?` is an `exc/excepted?` per context holding an
         ;; except.
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
  maximal contexts among the common descendants that see every handle with no except
  hiding it (`supporter-visible?` with no `defeat` read).  An except can hide a
  supporter at its own context while a meta-exception restores it in only one descendant
  ancestor set, so assertion contexts alone do not decide that case.
  `exc/closure-excepted-anywhere?` is the coarse presence check, so the ordinary placement
  path takes no ancestor set walk when no except reaches the supporters.  A firing's
  conclusion, a placed nogood, a guard defeat and an inherited clash's askers read it."
  [kb handles contexts]
  (let [tax (reasoning/taxonomy kb)]
    (if (some #(exc/closure-excepted-anywhere? kb %) handles)
      (let [common  (tax/common-descendants tax contexts)
            visible (filter (fn [ctx]
                              (every? #(supporter-visible? kb % ctx false) handles))
                            common)]
        (tax/maximal-contexts tax visible))
      (tax/maximal-common-descendant-contexts tax contexts))))

(defn visible-supporter-fn
  "`handle -> boolean`, memoized: is the sentex `handle` believed, inherited by
  `context`, and not hidden there by a visibility exception?  nil when `context` is nil
  or a `?var`, the unscoped read, which every caller reads as *no filter*.  The predicate
  a context-scoped equality read takes: the partition records its supporters as handles."
  [kb context]
  (when (and (symbol? context) (not (sx/variable? context)))
    (memoize #(supporter-visible? kb % context))))

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
  answer."
  [kb a b context]
  (let [visible? (visible-supporter-fn kb context)]
    (= (representative-in kb visible? a)
       (representative-in kb visible? b))))

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
  "The mention-aware walk.  Inside a **quoted position** — a quoting function's arguments,
  or the proposition a `modal_predicate` attributes to its agent — symbols are rewritten by
  spelling (`rewriteOf`) only, so a quoted term does not fold onto a `sameAs` / `equals`
  referent.  `spelling?` turns on there and stays on all the way down: the whole quoted
  expression is syntax.

  Two positions stay transparent and are the point of the distinction.  The **operator's
  own head** is rewritten normally, since opacity is about what it mentions rather than
  about the operator.  So is an attitude's **agent**, which the asker refers with — merge
  `Oedipus` with `KingOfThebes` and it is one agent under two names, where merging
  `Jocasta` with `MotherOfOedipus` is precisely what he does *not* believe."
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
  (`representative-in`) at any depth: ground congruence, so `(QuantityFn 5 Kilogram)` and
  `(QuantityFn 5 Kg)` meet under `(sameAs Kilogram Kg)`.

  A mention position, the arguments of a quoting function (`sx/quoting-functors`) and the
  proposition of a `modal_predicate`, is rewritten by `rewriteOf` spelling only (docs/belief.md,
  \"Opacity: the proposition is a mention\"); the operator and an attitude's agent stay
  transparent.  The marks are read once, unscoped (`tax/mention-marks`).  The schematic
  rewriting `kb/rewrite-term*` applies afterwards reads no mention mark, except an
  equality relation's arguments."
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

(def ^:dynamic *spelled-by*
  "nil, or `[pred context entries]`: while bound, `kb-sentex` sorts a literal on `pred` in
  `context` by the permuting marks `entries` lists (`mark-entries`' keys) and no others,
  so `chain/respell-rows!` stores, and `core/handle-of` looks up, the spelling a reader
  that believes those marks reads (`spelling-planner`)."
  nil)

(defn- spelling-opts
  "`sx/sentex`'s canonicalization reads restricted to the permuting-mark `entries`.

  The groups are read unscoped: the fold decides the stored key, which every reader
  shares."
  [tax entries]
  {:symmetric? #(contains? entries [:prop :symmetric %])
   :groups-of  (fn [f _arity] (into #{} (filter #(contains? entries [:commuting f %]))
                                    (tax/commuting-groups tax f)))})

;; ---- an open application read through its corresponding predicate ----------
;; docs/nat.md, The corresponding predicate.  `kb-sentex` respells a rule here, below
;; `nat`, because every store and lookup builds its sentex through it.

(def nat-quoting-predicates
  "Predicates whose expression argument is a verbatim NAT payload, neither reified nor
  type-checked as a term."
  '#{natFormula rewriteOf})

(def correspondence-predicate
  "The declaration relating a NAT function to the predicate stating the same thing."
  'functionCorrespondingPredicate)

(defn any-corresponding-predicates?
  "Does the KB declare any `functionCorrespondingPredicate`?  One O(1) functor count."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) correspondence-predicate)))

(defn believed-correspondences
  "Believed correspondence declarations as `[function predicate position-or-nil]`
  triples, kept where `match?` holds of the triple.  Read off the predicate extent and
  filtered in memory: the declarations are few, while an argument root holds every fact
  about the predicate.  `reads/believed-with-args` reads both arities in one probe."
  [kb match?]
  (when (any-corresponding-predicates? kb)
    (->> (reads/believed-with-args kb correspondence-predicate {})
         (keep #(p/get-sentex (:records kb) %))
         (map :sentence)
         (filter #(<= 3 (count %) 4))
         (map (fn [[_ f pr n]] [f pr (when (integer? n) n)]))
         distinct
         (filter match?))))

(defn correspondence-of
  "The `[predicate position]` declared for function `f` applied to `m` arguments, or
  nil.  `position` defaults to `m + 1`, the value last.  Nil when the KB believes more
  than one declaration for `f` (docs/nat.md, The corresponding predicate)."
  [kb f m]
  (let [ds (believed-correspondences kb #(= f (first %)))]
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
  "Believed correspondence declarations as `[function predicate position-or-nil handle]`
  rows, in content order of the declaration."
  [kb]
  (when (any-corresponding-predicates? kb)
    (->> (reads/believed-with-args kb correspondence-predicate {})
         (keep #(p/get-sentex (:records kb) %))
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

(defn- applications-in
  "The applications `app?` accepts in `form`, at any nesting, outermost first.  A quoting
  function's arguments and a quoting predicate's payload are mentions and are not read."
  [app? form]
  (when (and (sequential? form) (seq form)
             (not (sx/quoting-functor? (first form)))
             (not (contains? nat-quoting-predicates (first form))))
    (cond->> (mapcat #(applications-in app? %) (if (seq? form) (rest form) form))
      (app? form) (cons form))))

(defn open-applications
  "The open applications of a function `reifiable?` accepts in `form`, at any nesting,
  outermost first (`applications-in`)."
  [reifiable? form]
  (applications-in #(application-of? reifiable? %) form))

(defn names-variable-application?
  "Does `form` hold a variable-functor application, `(?fn AppleTree)`, at any nesting
  outside a mention?"
  [form]
  (boolean (seq (applications-in variable-application? form))))

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

(defn- respell-walk
  "The tests a respell in `kb` reads: `fixed?`, an open application of a
  `reifiable_function` (the mark read unscoped); `app?`, that or a variable-functor
  application; `formula?`, `formula-position?` memoized for one respell."
  [kb]
  (let [tax    (reasoning/taxonomy kb)
        fixed? (fn [t] (application-of? #(tax/has-prop? tax :reifiable %) t))]
    {:fixed?   fixed?
     :app?     #(or (variable-application? %) (fixed? %))
     :formula? (memoize #(formula-position? kb %1 %2))}))

(defn- arg-app?
  "The application test for argument `a`, at 0-based index `i` of a literal on `pred`:
  `fixed?` where a variable-functor compound is a sentence pattern (a construct's
  argument, or a `formula-position?`), `app?` elsewhere."
  [{:keys [app? fixed? formula?]} pred i a]
  (if (and (seq (applications-in variable-application? a))
           (or (contains? application-constructs pred) (formula? pred (inc i))))
    fixed?
    app?))

(defn rule-form?
  "Is `l` a rule, its wrappers peeled: a generator's consequent, whose applications the
  rule it generates reads when it is stored?"
  [l]
  (sx/implies? (peek (sx/peel-rule-wrapper l))))

(defn holds-variable-application?
  "Does literal `l` hold a variable-functor application outside a sentence position
  (`arg-app?`): one a stored rule leaves as written?  A rule `l` is not read
  (`rule-form?`)."
  [kb l]
  (let [walk (delay (respell-walk kb))]
    (letfn [(holds? [l]
              (cond
                (not (and (seq? l) (seq l)))                  false
                (rule-form? l)                                false
                (contains? nat-quoting-predicates (first l))  false
                (and (= 'not (first l)) (= 2 (count l)))      (holds? (second l))
                :else (boolean (some (fn [[i a]]
                                       (and (seq (applications-in variable-application? a))
                                            (= (:app? @walk) (arg-app? @walk (first l) i a))))
                                     (map-indexed vector (rest l))))))]
      (holds? l))))

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
  one where `f` has exactly one, and otherwise one `{:functor :n :pos}` per distinct
  declaration shape among `f`'s believed declarations (every function's, for a variable
  `f`), read through a predicate variable."
  [decls f m]
  (let [direct (rule-readings decls f m)]
    (if (= 1 (count direct))
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
  (`take-reading!`).  Nil when an application has no reading."
  [app? readings state t]
  (if (and (seq? t) (seq t) (not (sx/quoting-functor? (first t))))
    (let [args (doall (map #(respell-term app? readings state %) (rest t)))]
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
  reading's own literals with `x` the value.  A rule `l` is returned as it is
  (`rule-form?`)."
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
          a?s (vec (map-indexed #(arg-app? walk pr %1 %2) as))
          app (:app? walk)]
      (cond
        (not (some seq (map applications-in a?s as))) [l]
        (contains? application-constructs pr) nil
        (and (= 'equals pr) (= 2 (count as)) (not= (boolean (app (as 0))) (boolean (app (as 1)))))
        (let [[a x] (if (app (as 0)) as (rseq as))
              args  (doall (map #(respell-term app readings state %) (rest a)))
              x'    (respell-term app readings state x)]
          (when (and x' (every? some? args))
            (take-reading! readings state (apply list (first a) args) args x')))
        :else (let [args (doall (map #(respell-term %1 readings state %2) a?s as))]
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

(defn- respell-rule
  "The `implies` form `r` with every open application respelled under `state`'s choice,
  the literals stating the values added to its antecedents; `r` itself when nothing
  changed, nil when one cannot be respelled."
  [walk readings state r]
  (let [antes0 (vec (sx/rule-antecedents r))
        conseq (sx/rule-consequent r)
        antes  (mapv #(respell-literal walk readings state %) antes0)
        c      (respell-literal walk readings state conseq)]
    (when (and (every? some? antes) (= 1 (count c)))
      (let [antes' (into (into [] cat antes) (:hoisted @state))]
        (if (and (= antes' antes0) (= (first c) conseq))
          r
          (sx/rule-sentence antes' (first c)))))))

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
      :else (apply list (first l) (map-indexed #(sub (arg-app? walk (first l) %1 %2) %2) (rest l))))))

(defn goal-alternatives
  "Conjunction `goals` read through the believed correspondences, as the vector of
  conjunctions whose answers the reader merges (docs/nat.md, The corresponding
  predicate).  An open application of a `reifiable_function` with one believed
  correspondence reads its predicate; one with several, and a variable-functor
  application outside a sentence position (`arg-app?`), reads `functionCorrespondingPredicate`
  and a predicate variable, one conjunction per distinct declaration shape.  An `and` goal
  is read as its conjuncts.  The literals
  stating each value come first, innermost application first.  Where an application has
  no reading, each is replaced by `unmatched`, a term no stored sentex names, so the one
  conjunction answers nothing.  The declarations and the reifiable mark are read
  unscoped, so a goal is respelled exactly as the stored rules it reaches are."
  [kb goals unmatched]
  (let [walk (respell-walk kb)
        app  (:app? walk)]
    (if (not-any? #(and (seq? %) (some (fn [a] (seq (applications-in app a))) (rest %))) goals)
      [goals]
      (let [goals (into [] (mapcat (fn conjuncts [g] (if (and (seq? g) (= 'and (first g)))
                                                       (mapcat conjuncts (rest g))
                                                       [g])))
                        goals)
            decls (delay (correspondence-declarations kb))
            rs    (readings-of (sx/form-variables goals)
                               (fn [state]
                                 (let [gs (mapv #(respell-literal walk (fn [f m] (goal-readings @decls f m))
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
  "Every spelling of rule `sentence` its open applications of a `reifiable_function` read
  through the believed correspondences, as `[[spelling handle-sets] …]`: one per
  combination of each application's correspondences, `handle-sets` the sets of
  declarations it reads.  The first takes each function's content-least correspondence
  and is the one `kb-sentex` stores; `chain/sync-rule-respellings!` stores the rest.  Nil
  when `sentence` is no rule, holds no open application, or names a function with no
  believed correspondence or a variable-functor application (docs/nat.md, The
  corresponding predicate).  The mark and the declarations are read unscoped: the stored
  rule is one row every reader shares."
  [kb sentence]
  (when (and (not *as-written*) (seq? sentence)
             (seq (tax/props (reasoning/taxonomy kb) :reifiable)))
    (let [inner (volatile! nil)]
      (map-inner-rule #(vreset! inner %) sentence)
      (when-let [r @inner]
        (let [walk (respell-walk kb)]
          (when (seq (applications-in (:fixed? walk) r))
            (let [decls (delay (correspondence-declarations kb))]
              (some->> (readings-of (sx/form-variables r)
                                    #(respell-rule walk (fn [f m] (rule-readings @decls f m)) % r))
                       (mapv (fn [[r' ds]]
                               [(map-inner-rule (constantly r') sentence) (justification-sets ds)]))))))))))

(defn respell-applications
  "Rule `sentence` as `kb-sentex` stores it: the first of `rule-respellings`, or
  `sentence` unchanged when that is nil."
  [kb sentence]
  (or (ffirst (rule-respellings kb sentence)) sentence))

(defn kb-sentex
  "Build a sentex canonicalized against this KB's taxonomy: a symmetric predicate's
  arguments are sorted, so `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)` become the
  same sentex.  Every construction that stores or looks one up must go through this —
  otherwise an asserted form and a queried form could key differently.

  The commutativity marks generalize the same sorting to a declared set of positions at
  any arity, and are read here the same way: `tax/commuting-groups` off the literal's own
  functor, one map read that misses for every predicate declaring nothing.

  The property read is global: the store keys a fact by the sort every stored mark gives
  it, so an asserted form and a probe meet at one key.  While `*spelled-by*` names this sentence's predicate and context, the sort reads only
  the marks it lists, so a spelling a reader reads can be stored and looked up
  (`spelling-planner`).  A rule's open applications are read through their corresponding
  predicates first (`respell-applications`)."
  [kb sentence context]
  (let [tax (reasoning/taxonomy kb)
        [p ctx entries] *spelled-by*]
    (sx/sentex (respell-applications kb sentence) context
               (if (and p (= ctx context) (= p (permuted-functor sentence)))
                 (spelling-opts tax entries)
                 {:symmetric? #(tax/has-prop? tax :symmetric %)
                  :groups-of  (fn [f _arity] (tax/commuting-groups tax f))}))))

;; ---- a permuting mark read per reader --------------------------------------
;;
;; A `symmetric` or commuting mark sorts a fact's arguments at the store.  A reader that
;; does not believe the mark reads the fact as written, so where the readers of a fact
;; disagree the store keeps the written spelling as the premise's row; each other
;; spelling some reader reads is stored in its own row, justified `respell` by that row
;; and the marks (`chain/respell-rows!`).  These are the reads that decide it.  See
;; docs/canonicalization.md, "A mark a reader does not believe".

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
          (into {} (map (fn [e] [(sx/sentence-of (sx/sentex sentence context (spelling-opts tax e))) e]))
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
  "Candidate handles per **prefetch hint** a retrieval path gives its record store, or
  `false` to give it none.  `false` is the default, and it is the code that was here
  before: no chunking, no hint, one `get-sentex` per candidate that survives the belief
  filter.

  Turned on, a walk takes its candidates a chunk at a time and tells the store which
  handles the chunk is about to ask for, so a store that can answer many at one cost
  (`protocols/Prefetching`) may do that instead of being asked one at a time.  Nothing
  about the result moves: the hint returns nothing and every record still arrives through
  `get-sentex`, so this is a cost setting and never a semantic one.

  **It is off because it is only ever worth it over a fetch that is not local.**  On the
  RAM and disk record stores no store implements the capability, so the hint would have
  nobody to give it to; over a networked store it is worth it exactly when the candidates
  are not already cached, which the store itself checks — so turning this on hands the
  decision to the party that can make it, rather than making it here.  The evidence that
  says to turn it on is a `:fetches` tally (`vaelii.impl.profile`) large against a query's
  wall clock on a corpus whose working set does not fit that store's cache.

  The chunk is the unit of over-fetch: a consumer that takes one solution and stops has
  hinted at most this many handles, so a large chunk amortizes better and wastes more.

  **`false` or a positive integer, and anything else is refused where it is bound** —
  `true` above all, which is what a var with an off-value of `false` invites and which is
  truthy enough to reach the chunk arithmetic before it fails."
  false)

;; Refused at the `binding` form, which is the only place the wrong value is legible.
;; `true` is the obvious wrong guess for a var whose documented off-value is `false`, and
;; it is truthy, so it would otherwise pass every check here and reach `(long n)` inside
;; `cap/hinting` — a ClassCastException raised from within a lazy seq several frames into
;; the walk, naming neither the var nor what was bound to it.  A validator runs on
;; `pushThreadBindings`, so the `binding` that set it is the frame that throws.  It throws
;; rather than answering false because a false answer raises "Invalid reference state",
;; which names neither of them either.
(set-validator!
 #'*prefetch-candidates*
 (fn [v]
   (or (false? v)
       (and (integer? v) (pos? v))
       (throw (ex-info (str "*prefetch-candidates* is a positive chunk size, or `false` to "
                            "hint nothing — not " (pr-str v))
                       ;; `:unknown-option`, the same type `vaelii.impl.config` refuses a
                       ;; switch outside its domain with: this is a setting bound to a
                       ;; value it does not read, and a caller discriminating on the one
                       ;; vocabulary should not have to know it came from a var rather
                       ;; than from the environment.
                       {:type     :unknown-option :mismatch :bad-value
                        :setting  'vaelii.impl.resolution/*prefetch-candidates*
                        :value    v
                        :expected "false, or a positive integer (256 is the measured plateau)"})))))

(defn- hinting
  "`cands` unchanged, with a **prefetch hint** issued a chunk ahead of the walk when the
  setting is on and the record store can act on one.

  It yields the same handles in the same order — `mapcat` over `partition-all` is
  identity on the sequence — so a retrieval path wraps its candidates in this and is
  otherwise the code it was: the hint returns nothing, every record still arrives through
  `get-sentex`, and no answer can move.  Lazy at chunk granularity, so a consumer that
  stops at the first solution has hinted one chunk and not the extent.

  The belief filter runs before the hint, so the store is never asked to warm a record the
  walk would skip; the walk tests it again, which is a RAM read and the price of hinting.

  **Both** retrieval paths wrap their candidates here — the set-algebra one that answers a
  positive literal by default and the `match-one` fan-out behind it — because a hint given
  to only one of them is a hint the default query does not get."
  [kb cands]
  (let [pf     (when *prefetch-candidates* (cap/prefetcher (:records kb)))
        tms    (reasoning/tms kb)
        blind? (belief-blind?)]
    (cap/hinting (when pf (fn [chunk] (pf (filterv #(or blind? (jtms/in? tms %)) chunk))))
                 (or *prefetch-candidates* 1)
                 cands)))

(defn- match-one
  "Matches are *belief-sensitive*: a handle that is stored but currently OUT (e.g. a
  default defeated by a contradiction) does not match.  This is what lets a
  disbelieved sentex stay in the store for possible revival without polluting
  reasoning.

  Yields `[handle bindings stored-sentex]`.  The record has already been fetched to
  unify against, so it rides along rather than making a caller that wants the
  matched sentence pay for a second round trip; callers that only want the bindings
  destructure `[_ b]` or take `second` and ignore it.  `keep` keeps this lazy — one
  solution costs one `get-sentex`, not one per candidate handle.  Under
  `*prefetch-candidates*` it costs one *chunk*'s worth of hint instead, which is the
  over-fetch that setting trades for."
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
                    ;; an exceptWhen meta-sentex is internal bookkeeping (a rule's
                    ;; exception), not a domain fact, and it is the one *non-ground*
                    ;; stored Literal — so it is skipped here, keeping the trie and
                    ;; argument-root retrieval paths in agreement and ordinary queries
                    ;; clear of it.  A rule's exceptions are read through
                    ;; `provers/rule-exceptions`.
                    (when (and (not (sx/exceptWhen-meta? (:sentence stored)))
                               ;; match polarity too: a positive pattern like (?p ?x) must
                               ;; not bind ?p to `not` against a stored negation (the
                               ;; wildcard trie lookup can surface a `[:false ..]` key, but
                               ;; the truths differ).
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
  "Match a literal by `probe` — `(probe form)` → a seq of `[handle bindings …]`, one
  literal context — over every argument arrangement the predicate licences: the mirror
  for a **symmetric** predicate, the other arrangements of the commuting component for a
  **commutative** one.  Only fully-ground symmetric and commuting literals are stored
  sorted (see `vaelii.impl.sentex`), so the fan is what makes lookup order-insensitive:
  it retrieves `(siblingOf Ann Carol)` from the pattern `(siblingOf ?x Carol)` or
  `(siblingOf Carol ?x)` alike, and keeps a fact reachable even if it was asserted
  before its `symmetric` declaration.

  **Deduped by handle *and bindings*, not by handle.**  A palindrome — `(sibOf Ann Ann)`,
  or any pattern the mirror binds exactly as the direct probe did — is one answer.  A
  pattern whose arguments are both variables matches one stored fact **twice,
  differently**: `(sibOf ?a ?b)` over a stored `(sibOf Rex Tib)` binds `?a Rex, ?b Tib`
  directly and `?a Tib, ?b Rex` through the mirror, and those are two answers about one
  handle.  A dedup keyed on the handle alone drops the second, so a join led by such a
  literal sees one orientation, and which literal leads is a plan decision.

  Lazy through the fan: each probe filters against what the earlier probes emitted, and
  the set handed to the next is not built until a consumer walks past its own hits, so a
  consumer answered by the direct hits pays for no second probe and no set.

  The one definition of the fan and the dedup: `raw-match` calls it with `match-one`, the
  rete alpha matcher (`vaelii.impl.rete`) with its alpha-memory probe, so the two
  retrieval paths cannot fan differently.

  The `symmetric` mark is read unscoped, as `kb-sentex` reads it;
  `without-unbelieved-spellings` drops the mirror at a reader that does not believe
  the mark."
  [kb probe sentence]
  (let [hits (probe sentence)
        tax  (reasoning/taxonomy kb)
        ;; the global property, as kb-sentex reads it — the mirror probe exists because
        ;; storage sorted the arguments; a reader that does not believe the mark has the
        ;; mirror dropped by `without-unbelieved-spellings`
        others (if (sx/symmetric-literal? sentence #(tax/has-prop? tax :symmetric %))
                 [(sx/mirror-literal sentence)]
                 ;; `commuting-arrangements` returns the literal first and then the other
                 ;; arrangements a stored fact can have, so `rest` is the fan-out.  The
                 ;; declaration read stands in front of it so an unmarked predicate — all
                 ;; but a handful, on a path every literal-context match runs — pays one
                 ;; map lookup and builds neither the closure nor the vector.
                 (let [f (when (sequential? sentence) (first sentence))]
                   (when (and (symbol? f) (seq (tax/commuting-groups tax f)))
                     (rest (sx/commuting-arrangements
                            sentence (fn [g _] (tax/commuting-groups tax g)))))))]
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
                          (when-let [e (some-> (permuted-functor s) at)]
                            (not= s (sx/sentence-of
                                     (sx/sentex (read-spelling goal b s) view-context
                                                (spelling-opts tax e))))))
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

(def ^:private slot-cut-min
  "The fewest members a fan holds before `slot-cut` reads the slot predicate sets to cut it.  A
  smaller fan is read whole: its member reads are few, and the slot-set reads would be most
  of what the cut costs."
  64)

(defn- slot-cut
  "The predicates holding a stored fact that names every indexable ground argument of
  `body` at some position, read off the slot predicate sets (`reads/as-stored-predicates-at-arg`),
  or nil when `body` has no such argument.

  A member read costs a pattern build and an index probe whether or not anything is
  stored under it, so a fan is linear in the closure: `(different A B)` under 3,054
  sub-predicates and 3,050 swapped ones took 54 ms for no match, and a forward join tests
  one per row.  A member's matches unify with the goal under some arrangement of its
  arguments, so each holds every ground argument at some position, and a member outside
  this set has none.  The set over-approximates (a slot predicate set outlives a disbelieved fact) and
  never drops a match, so each member left is read exactly as the uncut fan reads it,
  mirror, arrangements and spellings included.  Read without the fan, so a goal whose
  arguments no fact names costs the slot-set reads alone."
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
  "The fan-out itself, shared by every matcher that does one: decompose `sentence` into
  the functor that fans and the rebuild that puts it back, take that functor's closure
  from `vantage`, and run `raw` over each member — `raw` being the caller's own
  as-written retrieval, and `mapcat-fn` its choice of `lazy-mapcat` or `mapcat`.

  **Shared for the reason `sub-predicates` and `super-predicates` are, one level up.**
  Those two keep the matchers from disagreeing about *which* predicates are in the fan;
  this keeps them from disagreeing about what to do with the fan once they have it, which
  is where the drift actually landed — the reference matcher counted the closure and its
  rete twin rebuilt `#{f}` per call to compare against, the same reading written twice
  and optimized once.  A matcher joins by passing its own `raw`, so a new one cannot
  quietly fan a negation the wrong way or skip the singleton short-circuit.

  Four things it decides, once:

  * **A variable or absent functor binds nothing** and fans not at all — one raw match on
    the sentence as written.
  * **A negation fans its body's functor upward** (`contrapositive-predicates`), the
    direction a `genl` edge carries through a negation, over the edges the reader holds at
    `:monotonic`, and rebuilds the `not` around each member.
  * **A singleton closure is `f` itself**, since both closures are reflexive, so there is
    nothing to fan and the as-written retrieval is the whole answer.  Counted rather than
    compared against a freshly built `#{f}`; the same reading `chain/fanning-functor?`
    takes of the same set.
  * **A `genlInverse` member is read swapped.**  The closure is `tax/signed-closure`,
    whose odd-parity members a binary literal reads with arguments 1 and 2 exchanged
    (docs/inference.md, \"`genlInverse`: the fan with the arguments swapped\").

  `indexed?` says `raw` reads the KB's index, as `raw-match` does, so the slot predicate sets
  bound what it can return and a wide fan is cut to the members they list (`slot-cut`).
  The rete alpha matcher reads its own memories, so it passes none."
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
             cut     (when (and indexed? (<= slot-cut-min (+ (count fan) (count swapped))))
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
  "Seq of [handle bindings] for stored sentexes matching `sentence` within
  `context` (default the wildcard ?ctx).  The **functor fans out over its sub-predicate
  (genl spec) closure**, so a unary type predicate is met by its subtypes
  (`(animal ?x)` ← `(dog Muffet)`) and — with predicate-genl edges — an n-ary predicate
  by its sub-predicates (`(parentOf a ?x)` ← `(fatherOf a v)`).  A functor with no
  sub-predicates has a singleton closure, so this is a no-op for it (the overwhelming
  common case — one cached set lookup, no fan).

  **A negation fans its body's functor the other way**, over `contrapositive-predicates`:
  `(not (dog ?x))` is answered by `(not (animal Muffet))`, since a `:monotonic` `dog ⊑
  animal` entails `¬animal ⊑ ¬dog`.  The `not` itself heads nothing and has no closure of its own, so
  the fan reads inside it and rebuilds the negation around each member; each rebuilt
  pattern is retrieved by the negative key it names, exactly as the written one is.

  The fan is scoped to the genl edges visible from `vantage` — by default the
  literal context itself, and the global closure for a `?ctx` match.  The four-arity
  exists for `matches-visible*`, which matches at each ancestor context in turn but
  stands at the *view* context throughout: scoping the fan by the ancestor would
  shrink the vantage as the walk ascends, and the set-algebra twin (which filters by
  the view context's ancestor set once) would disagree."
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
  (if (sx/variable? view-context)
    (match-pattern kb sentence '?ctx)
    (lazy-mapcat (fn [c] (match-pattern kb sentence c view-context))
                 (tax/context-up (reasoning/taxonomy kb) view-context))))

;; ---- hierarchical (set-algebra) retrieval -------------------------------
;; `matches-visible` answers `(p a ?x)` visible from `c` by a *product* of lookups:
;; `|context-up(c)|` contexts × `|specs(p)|` sub-predicates, each its own trie walk.
;; But the answer is an **intersection over three hierarchies** — a fact matches iff
;; its predicate is in `specs(p)`, its context in `context-up(c)`, and its arguments
;; unify — and the argument roots index a bound argument across every context at
;; once, scoped by predicate and ending in the context.  So lead with the bound
;; argument's posting lists (one scoped set read per sub-predicate, its context level
;; kept to the cached closure): the predicate and context filters are satisfied by
;; which leaves are read.  The product collapses to one node read per sub-predicate.
;;
;; Scoped to a plain positive literal with a concrete functor; everything else
;; (a negation, a variable or `not` functor, a dotted pattern) falls back to
;; `matches-visible`, which the oracle uses as the reference.

(def ^:dynamic *hierarchical-retrieval*
  "Answer a context-scoped `(p a ?x)` query with the set-algebra retrieval below
  (lead with the argument root, filter the predicate/context hierarchies in memory)
  rather than the nested `|context-up| × |specs|` `matches-visible` fan-out.

  On by default: the set-algebra path is lazy (`lead-candidates`), so it
  short-circuits an existence check like the fan-out does while collapsing the
  fan-out's product to a scoped argument-root lookup per sub-predicate — strictly
  cheaper, and flat where the fan-out is O(context-hierarchy depth).  Like `plan/*enabled*`, this is a pure cost decision that must
  never change the answer *set*; bind it **false** to run the reference fan-out, which
  is what `matches_hierarchical_test` compares against over patterns from the starter's
  own facts."
  true)

(defn- hierarchical-literal?
  "A plain positive literal the set-algebra path handles: a concrete predicate symbol,
  or a **variable functor with something indexable to lead with** (`(?type Muffet)`).
  The two differ only in which dimensions are bound — a variable functor names no
  predicate, so there is no predicate hierarchy to filter by and every candidate's
  functor is admissible, while the argument root and the context ancestor set still narrow
  exactly as they do for a concrete one.

  A negation keys under `not`/its positive body, a dotted pattern is not a stored-fact
  shape, and a variable functor with no indexable argument binds nothing at all; those
  fall back to `matches-visible`."
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
  "How `lead-candidates` narrows a NON-symmetric literal with **≥2 indexable ground
  arguments**: the multi-column argument-root probe.  Rather than lead with the single
  tightest bound column and let `unify` reject every candidate the other bound columns
  disagree with, intersect the columns at the index so only the conjunction reaches
  `unify` — \"fewest unifications\".

  Every choice is a **pure cost decision**, like `*hierarchical-retrieval*`: the result
  is a subset of the single leading column and still a *superset* of the true matches
  (each match holds every bound term at its position), so `unify` and the context filter
  run over fewer candidates and the answer *set* is identical.  A symmetric literal is
  left on the mirror-widened single-column path — intersecting its forward columns would
  drop the mirror-stored matches — as is a literal with fewer than two ground columns
  (the belief-settle diet), so those paths take the single-column lead unchanged.

    :two          intersect the two lowest-`count-with-arg` ground columns (default)
    :all          intersect every indexable ground column
    :above-floor  :two, but only when the leading column is a wasteful superset — its
                  agnostic count exceeds `*arg-intersect-floor*`; below that a single
                  `unify` sweep is cheaper than allocating an intersection set
    :off          the pre-v3 single leading column, no intersection

  Chosen by measurement (`lein bench-argindex join`); bind it to compare."
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
  "For a **non-symmetric** literal with a spec closure in hand, which side of the two
  equivalent argument reads `lead-candidates` leads from — and the last cost decision in
  this namespace to lack a knob.

  A scoped literal's candidates can be read two ways, and each is a *superset*
  `matches-hierarchical`'s `jtms/in?`/`unify` filters reduce to the identical set (like
  `*arg-intersect*`, a pure cost decision that must never change the answer):

    :scoped   one predicate-scoped node per sub-predicate (`[pd pos term]`).  Exactly this literal's predicates, O(|specs|) index probes — the
              pre-v4 lead, and the reference `matches_hierarchical_test` forces to compare.
    :agnostic the slot predicate set (`[:argument-slot pos term]`, every functor holding `term`
              at `pos`), kept to `specs`, then the node of each kept functor.  One
              slot-set probe and one node read per kept functor.
    :auto     (default) `:agnostic` when the term holds no more postings at this position
              than there are specs, else `:scoped` — read whichever side is smaller.  The
              choice is content-derived (`count-with-arg` vs a realised `count`, both
              O(1)), so it is order-independent and free; `≤` ties to the one-probe read.

  `:auto` is the whole of the cold-rebuild clash win: the queried type sits high and its
  subtree spans the KB, while the term holds a handful of memberships, so `:scoped`'s
  O(|hierarchy|) probes collapse to one.  `checks/membership-handles` reads this too —
  `:scoped` runs its `matches-visible` reference, any other value leads from the term."
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
  "A **lazy** superset of the matching handles, led by the tightest bound argument.
  The argument roots are scoped by predicate and end in the context, so with a spec
  closure in hand the read is each sub-predicate's own node at that position, restricted
  to the contexts in `up` (the reader's ancestor set, nil for a variable context) — the
  predicate filter is satisfied by construction, and no leaf stored where the reader
  cannot see is read.  Where `*lead-side*` reads the slot predicate set, that set's predicates
  are kept to `specs` before a node is read, so every source holds only the literal's
  sub-predicates.  A variable functor reads the predicate-agnostic union instead (over
  the slot predicate set), which spans every functor; with no bound argument at all, the
  sub-predicates' predicate extents.  A ground prefix walks the trie under it unless
  `arg-lead` reads its argument roots.  Every source reads only the contexts in `up`.  A
  symmetric sub-predicate may store the term at the mirror position, and a commutative
  one at any position of the term's commuting component, so when any sub-predicate
  permutes that position every position it reaches is taken.

  Lazy so an existence check short-circuits without realizing the whole candidate set:
  each posting set is handed back by reference and the per-spec fan is `lazy-mapcat`,
  so buckets are read one sub-predicate at a time as `matches-hierarchical` consumes
  them.  The permuted multi-position concat can repeat a handle stored at more than one
  of them; `matches-hierarchical`'s `seen` set dedups the emitted matches, so the
  result stays the identical set."
  [kb specs args alts up]
  (let [ix     (:index kb)
        ;; `alts` is nil when nothing about this literal permutes, and otherwise a
        ;; function from a position to the **other** positions a match may be stored at:
        ;; the mirror slot for a symmetric literal, the rest of the commuting component
        ;; for a commutative one.  A superset is safe here — `matches-hierarchical`
        ;; filters every candidate through `unify` — so the components are unioned over
        ;; the sub-predicates rather than asked per candidate.
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
            ;; A lone ground column needs no count: there is nothing to compare it
            ;; against, so pricing it here would be a read the belief-settle diet (`≤1`
            ;; ground column) never spends.  Count only with ≥2 columns — one agnostic
            ;; count read each — sorted smallest first so the head is the tightest column
            ;; to lead and the pair below is the one to intersect; `sort-by` is stable, so
            ;; a tie resolves to the leftmost column.
            sorted (when (next ground)
                     (sort-by first (mapv (fn [g] [(long (cnt g)) g]) ground)))
            [pos term] (if sorted (second (first sorted)) (first ground))
            ;; The argument roots are scoped by predicate, so read each sub-predicate's
            ;; own bucket. That is the whole of the saving: the candidates arriving at
            ;; the filter below are this literal's predicates only, where the
            ;; predicate-agnostic read returns every fact holding `term` at `pos` —
            ;; which, on a materialising join, is dominated by the derived facts no rule
            ;; ever reads back.  `lazy-mapcat`, not `mapcat`: one scoped read per
            ;; sub-predicate as the caller consumes, so an existence check still touches
            ;; one bucket, not `|specs|` of them.
            scoped (fn [pd pz] (p/sentexes-with-args ix pd {pz term} up))
            ;; Multi-column narrowing: with ≥2 indexable ground columns on a non-symmetric
            ;; literal, intersect them at the probe (`sentexes-with-args` folds the scoped
            ;; leaves) so `unify` sees only the conjunction, not one wide column it then
            ;; rejects the others against.  `nil` keeps the single leading column — the
            ;; belief-settle diet (`≤1` ground column) and every symmetric literal, whose
            ;; mirror matches a forward intersection would drop.  The intersection is a
            ;; subset of that leading column and a superset of the matches, so the answer
            ;; set is unchanged (`*arg-intersect*`).
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
            ;; One scoped bucket per sub-predicate is one index probe per spec, which a
            ;; broad functor's spec closure makes O(|hierarchy|) — the dominant cost of a
            ;; cold rebuild's clash retrieval, where the queried type sits high and its
            ;; subtree is huge while the term holds a handful of memberships.  The slot
            ;; predicate set, the predicates holding `term` at `pos`, is then the smaller side:
            ;; read it once, keep the predicates in `specs`, and read each kept one's
            ;; node, so every candidate's functor is in `specs` without a record fetch.
            ;; Which side, and when, is `*lead-side*`; a store keeping no such set reads
            ;; per spec.
            (lazy-mapcat (fn [pd] (scoped pd pos))
                         (or (when (lead-agnostic? ix pos term specs)
                               (some->> (reads/as-stored-predicates-at-arg ix pos term)
                                        (filter #(contains? specs %))))
                             specs)))

          ;; A variable functor names no predicate, so there is no scope to read: the
          ;; predicate-agnostic root (a union over the slot predicate set) is the whole
          ;; candidate set, and `unify` binds the functor per candidate.  It permutes
          ;; nothing either — `alts` is non-nil only with a symmetric or commuting spec —
          ;; so there is no alternate position to read.
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
          ;; a variable functor names no predicate, so there is no spec closure to fan
          ;; over — every candidate's functor is admissible, and `unify` binds
          ;; the variable to it.  `lead-candidates` gets `specs` nil here and takes its
          ;; predicate-agnostic branch: the shape is admitted only with an indexable
          ;; argument, so the slot-set union is its candidate source.
          var-fn? (sx/variable? (first sentence))
          args  (rest sentence)
          up?   (not (sx/variable? view-context))
          up    (when up? (tax/context-up tax view-context))
          ;; is any sub-predicate symmetric — i.e. might a match be stored with its
          ;; arguments in the mirror order?  Only a *binary* literal has a mirror, and
          ;; the question is one of set intersection, so drive it from the **declared
          ;; symmetric predicates** (a handful) and test membership in `specs` rather
          ;; than the other way round: a broad functor's spec closure is the whole type
          ;; hierarchy, and scanning it would cost more than the retrieval it precedes.
          ;; A variable functor is never a symmetric literal (`sx/symmetric-literal?`
          ;; asks the taxonomy about the functor, and a variable has no property), so
          ;; the reference runs no mirror probe for it and neither may this.
          ;; `sym?` is a *candidate filter*, per call: it widens `lead-candidates`' bucket
          ;; selection, where a superset is safe.  Whether a given candidate may match
          ;; mirrored is that candidate's own functor's question (`sym-preds` below,
          ;; at the probe) — the reference asks `sx/symmetric-literal?` per fanned
          ;; sub-predicate, and mirroring every candidate because *some* spec is
          ;; symmetric would admit `(knows Bob Ann)` for `(knows ?x Bob)` whenever a
          ;; symmetric predicate sits anywhere under `knows`.
          sym?  (and (not var-fn?)
                     (= 2 (count args))
                     (boolean (some #(contains? specs %) (tax/props tax :symmetric))))
          sym-preds (when sym? (tax/props tax :symmetric))
          ;; the same question for the commutativity marks, driven the same way round and
          ;; for the same reason: the marked predicates are a handful where a broad
          ;; functor's spec closure is the whole hierarchy.  A variable functor declares
          ;; nothing, so it permutes nothing here either.
          comm-preds (when-not var-fn? (tax/commuting-predicates-among tax specs))
          ;; the positions one argument may also be stored at, unioned over the
          ;; permuting sub-predicates — `lead-candidates`' bucket filter, where a superset
          ;; is safe.  Nil when nothing permutes, which is the shape all but a handful of
          ;; literals have and the one that keeps multi-column narrowing on.
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
          alt-args (volatile! {})
          args-for (fn [f]
                     (or (get @alt-args f)
                         (let [v (if (and f (or (contains? sym-preds f)
                                                (contains? comm-preds f)))
                                   (mapv #(vec (rest %))
                                         (if (contains? sym-preds f)
                                           [(cons f args) (cons f (reverse args))]
                                           (sx/commuting-arrangements
                                            (cons f args)
                                            (fn [g _] (tax/commuting-groups tax g)))))
                                   [(vec args)])]
                           (vswap! alt-args assoc f v)
                           v)))
          seen  (volatile! #{})
          ;; the **unify-attempt** tally: candidates that clear the cheap
          ;; liveness/predicate/context filters and reach `unify`.  `prof?` is captured
          ;; once — the instrument does not toggle inside one call — so when off the
          ;; per-candidate cost is a `false` test, not a deref (zero perturbation on the
          ;; timing path); on, it is what multi-column narrowing moves and `record-sift`
          ;; reports.  Every instrument decision in this fn reads *this* local, so one
          ;; call cannot record a literal it then declines to sift.
          prof? (prof/profiling?)
          unifs (volatile! 0)
          ;; The pattern sentex is a function of the candidate's functor and context
          ;; alone — the argument list is the caller's, fixed for the whole call — and
          ;; building one canonicalizes and interns a whole sentence.  Candidates
          ;; arrive keyed by an argument, so a posting is overwhelmingly one functor
          ;; over a handful of contexts; without this the identical pattern is
          ;; reconstructed once per candidate.
          ;; `args` is the caller's and fixed, so the only argument lists in play are it
          ;; and (for a symmetric predicate) its mirror — hence `rev?` in the key rather
          ;; than the list itself.
          pats  (volatile! {})
          ;; A concrete functor is replaced by the *candidate's* — the spec-closure test
          ;; has already established subsumption, and `unify` would otherwise reject
          ;; `animal` against a stored `dog`.  A variable functor is kept as written:
          ;; substituting it away would unify fine and bind nothing, losing the very
          ;; binding the caller asked for.  So one pattern serves every candidate there.
          pat-functor (if var-fn? (constantly (first sentence)) identity)
          ;; `i` indexes `args-for`'s arrangement vector rather than naming the argument
          ;; list, so the key stays three scalars and a candidate costs no vector hash.
          ;; arrangement -1 is `args` as written, unsorted: the row a reader that does
          ;; not believe the candidate functor's mark reads (`as-written-probe`)
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
            ;; A candidate that can answer at all: live and fetched.  Every lead reads
            ;; only the sub-predicates' nodes in the contexts in `up`, so no predicate or
            ;; context filter runs here.  An
            ;; exceptWhen meta-sentex is internal bookkeeping and skipped, as in
            ;; `match-one` (the one non-ground stored Literal).  Both branches below
            ;; admit a candidate exactly here, and differ only in how many answers one
            ;; admitted record may yield.
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
            (if-not (or sym? comm-preds)
              ;; Nothing under this functor is symmetric, so one candidate answers at
              ;; most once and the handle is the whole dedup key — the shape all but a
              ;; handful of literals have, and the one the closure walks ask for a node
              ;; at a time.  A `keep` over the candidates, so a candidate costs the
              ;; triple it answers with: the mirror branch's answer vector, transducer
              ;; chain and `lazy-mapcat` cell are all for a second answer this shape
              ;; cannot have.  The handle-keyed guard also skips the record fetch for a
              ;; candidate a second bucket names again.
              (keep (fn [h]
                      (when-not (contains? @seen h)
                        (when-let [stored (admit h)]
                          (when prof? (vswap! unifs inc))
                          (when-let [b (order stored 0)]
                            (vswap! seen conj h)
                            [h b stored]))))
                    cands)
              ;; A permuting sub-predicate, so one candidate really can answer more than
              ;; once — an all-variable pattern binds a stored `(sibOf Rex Tib)` both ways
              ;; round, and a commuting component of three binds a stored triple six ways
              ;; — and the dedup keys on `[handle bindings]`, which leaves no
              ;; handle-keyed early exit to skip the fetch with.  That pairing is what
              ;; makes the two retrieval paths return one set (`raw-match` says why the
              ;; pair is the key).
              (lazy-mapcat
               (fn [h]
                 (when-let [stored (admit h)]
                   (when prof? (vswap! unifs inc))
                   (let [;; every arrangement, not the first that answers: a pattern with
                         ;; two variable arguments binds one stored fact twice and
                         ;; differently, and those are two answers about one handle.  A
                         ;; palindrome, or any arrangement binding as an earlier one did,
                         ;; is one — `distinct` is what keeps it one.
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
        ;; returned-vs-matched, opt-in.  Realizing `out` walks the whole candidate seq,
        ;; so `(count cands)` then reads the returned count and `(count v)` the matched;
        ;; both only while the instrument is on, leaving the lazy short-circuit intact for
        ;; a timing run (`vaelii.impl.profile/record-sift`).
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
     kb sentence view-context
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
  "A positive **open-functor** pattern's matches, each also answering the functor
  variable with every super-predicate of the one it matched (`super-predicates`, from
  `view-context`), on the same stored fact.

  A named functor reaches a fact through its own spec closure: `(animal ?x)` matches a
  stored `(dog Muffet)`.  An open one binds the functor the fact was stored under, so
  `(?c Muffet)` answered `dog` and not `animal` though `(animal Muffet)` holds, and a
  conjunction `[(genl ?c animal) (?c Muffet)]` answered `animal` when the `genl` literal
  ran first and not when the open one led.  A functor variable that also stands as an
  argument keeps the functor as stored: a super-predicate there would bind that argument
  as well.  A negative pattern keeps it too."
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

(defn- visible-matches
  "The retrieval both of `matches-visible`'s arities perform: the chosen path, then the
  two visibility filters, then an open functor's super-predicates
  (`with-open-functor-supers`).  One definition, so a cached and an uncached read cannot
  come to answer differently."
  [kb sentence view-context]
  (->> (if *hierarchical-retrieval*
         (matches-hierarchical kb sentence view-context)
         (matches-visible* kb sentence view-context))
       (exc/without-excepted kb view-context)
       (without-retired kb view-context)
       (without-unbelieved-spellings kb view-context sentence)
       (with-open-functor-supers kb sentence view-context)))

(defn matches-visible
  "Type-aware matches of `sentence` *visible from* `view-context`.  A variable
  context means any context; a concrete context sees a fact iff the fact's
  context is in view-context's genlCx up-closure — this is how inference in a
  specific context can use facts asserted in the general contexts it inherits.

  A positive literal is answered by the set-algebra path (`matches-hierarchical`,
  default) instead of the nested fan-out; bind `*hierarchical-retrieval*` false for the
  reference fan-out.

  A sentex an `except` has hidden from `view-context` is filtered out — the read side
  of visibility removal.  Forward chaining holds the same line by a different
  mechanism: its join runs at `'?ctx`, where the hidden set is empty by construction,
  and the block is applied per *placement* (`chain/antecedent-hidden?`,
  `justification-excepted?`), where the context the except scopes to is known.

  Answers are **cached per KB** by the literal they answer, α-renamed so two spellings
  of one question share an entry, and keyed by the change clock so any mutation
  retires them (`vaelii.impl.literal-cache`).  **All three** retrieval-strategy vars are
  part of the key rather than assumed away: the set-algebra and fan-out paths must agree
  on the answer set, and so must the structural-trie and functor-extent candidate
  sources, which is what `retrieval_completeness_test` and `structural_index_test` check
  — a cache that served one path's answers to the other would be checking a result
  against itself.  With `literal-cache/*enabled*` false this is the bare call.

  `*belief-blind*` is in the key for the same reason and a sharper one: a `CxEverything`
  read and an ordinary one ask the *same literal at the same context* and must not answer
  each other.  Left off, the first read of a pair fills the entry and the second is served
  it — so a blind read would hide a defeated default it was asked for, or an ordinary one
  would report a default it must not, whichever happened to run first.

  `tax/*search*` is in the key because a read inside a second-route search reads belief
  alone for a belief read, and can read false off a route question still open above it.
  `tax/*network-belief*` is in the key because a placement in `chain` reads the network
  and the excepts, and no defeat (`exc/hidden-fn`).

  **`cached?` false asks the same question and neither consults the cache nor fills
  it** — for a caller whose repeats that cache cannot serve.  A transitive closure walk
  asks each node's neighbour literal once (`provers/reach` visits a node once), so there
  is no repeat there for a solution cache to catch, while its insertion per node would
  push the cache past its bound and clear it wholesale part-way through, evicting the
  metadata literals a rule-heavy query really does re-ask.  An argument rather than a
  rebinding of `literal-cache/*enabled*`, for two reasons: a `binding` covers every read
  *under* the walk rather than the neighbour probe alone, and it marks the var
  thread-bound for the life of the process — so every later `matches-visible` on every
  thread would take the thread-local path to read a flag nothing had rebound.  The
  repetition a walk does have is held where it is: `provers/cached-reach` for the whole
  closure, `observe/*reach-memo*` for the neighbour sets a join re-walks."
  ([kb sentence view-context] (matches-visible kb sentence view-context true))
  ([kb sentence view-context cached?]
   (if-not (and cached? lc/*enabled*)
     (visible-matches kb sentence view-context)
     (let [[canonical rename] (lc/canonicalize sentence)]
       (lc/rename-matches
        unify rename
        (lc/lookup (reasoning/matches kb)
                   [canonical view-context
                    *hierarchical-retrieval* *arg-root-retrieval* *structural-index*
                    *belief-blind* exc/*unscoped-own* tax/*search* tax/*network-belief*]
                   #(visible-matches kb canonical view-context)))))))

;; ---- whose declarations bind a tuple ------------------------------------

(defn type-memberships
  "The membership sentexes `(T x)` of term `x` that `kb/types-of` reads its types off, as
  records: believed, asserted in a context `context` sees, and not hidden from it by an
  `except` (default: any context, each membership read at its own).  A caller that names
  the membership a type rests on reads this; `kb/types-of` is its functors.

  The same three filters `matches-visible` applies, since this *is* the retrieval
  `isa?` and the disjointness check are built on and the two must not disagree about
  what the KB holds.  A negative membership is excluded by the argument test rather than
  by a truth filter — a `(not (T x))` sentex has `not` for its functor and `(T x)` for
  its lone argument, so it is not a unary sentence *about* `x` at all."
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
     ;; the unary predicate set goes straight to the sentexes holding x as their LONE
     ;; argument, instead of every sentex mentioning x anywhere (any position, any
     ;; nesting) or even every one holding it at argument 1 — this runs on every unary
     ;; assert, via disjoint-problem, and a term at argument 1 of n binary facts cost n
     ;; record fetches here to find the handful of types it holds
     ;; (`reads/as-stored-unary-with-arg-global`).  The read is a superset, so the arity and
     ;; argument tests below decide the answer.
     ;;
     ;; The filters are one `keep` rather than a stack of threaded stages: every
     ;; definitional check bottoms out here, the postings are short, and a chain of
     ;; six `filter`/`map` stages allocates six conses per entry to do a few field
     ;; reads.  Lazy, so a caller looking for one type does not pay for a long posting
     ;; — which is also why this is not a transducer: at these lengths `sequence` spends
     ;; more on building the pipeline than the pipeline saves.
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
  memberships through while bound (`checks/cover-refutations` binds it over one write's
  covers, where nothing is stored), or nil to read `type-memberships` afresh."
  nil)

(defn- memberships-for
  "`type-memberships` of `x` at `context`, through `*membership-memo*` when it is bound."
  [kb x context]
  (if-let [memo *membership-memo*]
    (let [k [x context]]
      (if-let [hit (find @memo k)]
        (val hit)
        (let [ms (vec (type-memberships kb x context))]
          (vswap! memo assoc k ms)
          ms)))
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
  "The witnesses of `(not (t x))` a reader at `context` reads off a separation, in
  content order: one per believed, visible, unexcepted membership `(s x)`
  (`type-memberships`) and per route a declaration separates `s` from `t` through
  (`tax/separation-routes`) that meets the soundness rule (`tax/monotonic-route-witness`):
  each key believed and visible, the separated pair not exempted by a
  `siblingDisjointException` the reader sees, and every `genl` edge climbed on either
  side holding at `:monotonic`.  Each witness is `{:membership h :sentence (s x)
  :context c :route {:keys :pair :supports :edges}}`.  Empty when no separation reaches
  `t` (`tax/separable?`).  The routes are read over the unscoped closures, a superset over
  every reader, and the reader's context scopes each one's keys and edges.

  The one read of a separation's denial.  `provers/DisjointnessNegationProver` answers
  the query from it, and `checks/cover-refutations` names its memberships as the members
  of a refuted cover, so `argue` and the cover family read one denial (docs/taxonomy.md,
  \"A separation answers a denial\")."
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
  "The predicates whose argument declarations of kind `kind` bind a `pred` tuple —
  `pred` itself first, then every super-predicate of it `context` can see that some
  sentence declares `kind` of.

  `(genl fatherOf parentOf)` says every `fatherOf` tuple **is** a `parentOf` tuple, and
  a tuple set only narrows going down, so `(arg parentOf 1 person)` constrains every
  `fatherOf` tuple exactly as it constrains every `parentOf` one.  Reading the
  declarations off the exact functor makes the refusal *entry-point-dependent*: the same
  ill-typed claim is refused under the general spelling, admitted under the specialized
  one, and then answers every general-spelling query through the matcher's own fan —
  which is the one job the constraint exists for.  Both readers of a declaration come
  here, the constraint (`checks/declaration-reader`) and the inference
  (`provers/inferred-types`), so `assert` and `ask` cannot disagree about whose
  declarations speak for a tuple.

  **Scoped to the reader's own vantage.**  The closure is read from `context`, so a
  `genl` edge asserted where the reader cannot see it imports no constraint — the same
  judgement `checks/args-problem` already makes about the memberships it reads.  A cycle
  in predicate `genl` cannot loop the walk, `genls` being a closure read.

  **`pred` and its proper supers are both filtered against the `:props` set** of
  predicates some declaration of `kind` names (`tax/arg-declaration-props`).  A predicate
  the set does not name carries no `(kind predicate …)` declaration in any context, so
  the scoped retrieval its inclusion would admit returns nothing; every consumer reads
  declarations off the predicates handed back, so an undeclared predicate contributes an
  empty retrieval whether it is listed or dropped.  The filter is a set membership rather
  than an index probe, which is what keeps the walk cheap: asked of the index it would be
  one argument-root read per predicate per assert, so a membership of a type ten deep in
  the hierarchy would pay ten of them, and nine of those types declare nothing —
  including, on a minting assert, the mint's own functor (a type name like `animal`,
  which no sentence declares `arg` of).  The `:props` set is global and therefore a
  superset of what any context can see, and the scoped retrieval of each predicate it
  admits decides which of the named predicates actually speak here.  When nothing
  anywhere declares `kind` the set is empty and the walk returns `[]` without reading the
  closure at all.  The intersection walks the smaller of the set and the closure, so a
  membership of a type with thousands of ancestors reads at most the set.

  The supers are sorted, so which declaration a refusal names — and the order the
  entailments are drawn in — is a function of the vocabulary rather than of the closure's
  hash order.

  The `:props` set is read unscoped, a superset: it is intersected with the `genls`
  `context` sees, and the caller reads each declaration from `context`.

  `memos`, a volatile map a caller holds for one still taxonomy, keeps one
  `tax/genls-among` memo per `kind`, for the `:props` set it was filled from, so a pass
  over many predicates reads no closure (`checks/*pass-reads*`).  The set is compared by
  identity: compared by value, each lookup would walk the whole set."
  [kb kind pred context & [memos]]
  (let [tax       (reasoning/taxonomy kb)
        declaring (tax/props tax (tax/arg-declaration-props kind))
        base      (if (contains? declaring pred) [pred] [])]
    (cond
      (empty? declaring) []
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
;; What a predicate's argument positions are declared to hold, read once and in one
;; shape.  Two instance-level constraints are looked up: `arg`, one position, and
;; `argAndRest`, a position and every later one.  The other instance spellings are sugar
;; whose forward rules (core.txt) store the declaration they stand for: `(args P T)` stores
;; `(argAndRest P 1 T)`, and `arg1`..`arg5` store the `arg` they project.  The type-level
;; (`genlArg`, `argsGenl`, `argAndRestGenl`) and quoted (`quotedArg`) twins come back on the
;; same entries under their own `:kind`, so a caller asking whether a position is typed
;; at all reads one list.

(def ^:private arg-constraint-kinds
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
  `{:from n :to m :type T :kind K :via P}` in the order of the declarations' sentences:

  * `:from`/`:to` — the positions typed, `:to` nil for a tail running to the last
    argument.  `(arg P n T)` is `{:from n :to n}` and `(argAndRest P n T)` is
    `{:from n :to nil}`; `(args P T)` arrives as the `(argAndRest P 1 T)` its forward
    rule stores, and `arg1`..`arg5` as the `arg` theirs store.
  * `:kind` — `:instance` (`arg`, `argAndRest`): the filler is a `T`; `:type`
    (`genlArg`, `argAndRestGenl`, `argsGenl`): the filler is a subtype of `T`; `:quoted`
    (`quotedArg`): the filler, taken as written, is a `T`.
  * `:via` — the predicate the declaration is written on: `pred`, or a super-predicate
    whose declaration binds `pred`'s tuples (`constraining-predicates`).

  The one read of what a position is declared to hold, so a caller asking it is answered
  for every spelling and cannot honor one while missing another.  `arg-constraints-at`
  answers for one position.  A declaration whose type is not a ground symbol or whose
  position is not a positive integer is dropped: its own declaration refuses it at the
  entry point, so a stored one is a torn record.

  Held in the taxonomy's closure memo for one stretch of the change clock
  (`tax/clock-held`), so a read-only caller asking per argument or per fact reads the
  store once per predicate and context between writes."
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

;; ---- backward chaining --------------------------------------------------
;; The pieces below — goal-key, planned-antecedents — are the
;; rule-expansion core every backward executor shares.  The goal-stack machine here
;; and the node engine (`vaelii.impl.inference`) differ in *execution* — a stack walked
;; depth-first against a frontier of whole conjunctions ordered by cost — but they must
;; agree on planning, loop detection, and how a conjunction threads bindings, so those
;; parts live here once rather than as a copy each that could drift — a recursion guard
;; present in one executor but missing in the other, say.

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
  derivation path has already met (`term-depth`) before `prove-from` cuts the branch as
  it cuts a repeated goal key — the `:max-term-growth` bound, where a caller names none.

  The per-path `seen` set cuts a goal re-asking *itself*; a rule whose antecedent
  nests a function application around a head variable, `(implies (p (SuccFn ?x)) (p
  ?x))`, never does: `(p A)` asks `(p (SuccFn A))`, which asks `(p (SuccFn (SuccFn
  A)))`, each a goal nobody has asked.  What the ceiling has to refuse is **growth a
  rule invented**, and only that: a term is deep for two quite different reasons, and
  the bound must tell them apart or it cuts derivable answers.  So the basis it
  measures against rises whenever a leaf match binds a deep *stored* term
  (`grown-term-base`) and never when a rule expands, which leaves structural recursion
  that *shrinks* a term — walking a list, counting a numeral down — untouched at any
  depth, and leaves a conjunct that inherits a deep individual from the conjunct before
  it measured from that individual's depth rather than from the query's.  Termination is
  unaffected: the store holds finitely many terms and each has a finite depth, so the
  basis a path can reach is bounded by the deepest thing stored.  Eight levels of growth
  is room for a subgoal to nest an individual several layers deeper than anything it was
  handed without being a term that grows without end."
  8)

(defn grown-term-base
  "`base` raised to the nesting the extension bindings `b` bring in — the depth a term
  bound to a variable contributes when it lands at a goal's top argument position, which
  is `1 +` its own (`term-depth`).

  A leaf match reads what is *stored*, so a deep value here is a fact about the KB and
  not about a rule growing a term; measuring the conjuncts that inherit it against the
  query's own depth is what cut answers a reordering of the same conjunction returned.
  One `sequential?` test per bound value, so a flat KB — every value a symbol — pays a
  scan and nothing else."
  [base b]
  (reduce-kv (fn [d _ v] (if (sequential? v) (max (long d) (inc (long (term-depth v)))) d))
             (long (or base 0)) b))

;; ---- rule instances --------------------------------------------------------
;; A rule's variables belong to the rule, and a chainer that threads one binding map
;; down a derivation path hands that map to every expansion on it.  So the *second* use
;; of a rule on one path meets its own first use's bindings, and the two instances are
;; forced to agree on variables that were never meant to be shared.  Renaming the clash
;; apart is what gives each instance variables of its own.

(defn- spoken-for
  "Every variable `bindings` already speaks for — the ones it binds, and the ones still
  standing unbound inside its values."
  [bindings]
  (persistent!
   (reduce-kv (fn [acc k v] (reduce conj! (conj! acc k) (sx/form-variables v)))
              (transient #{}) bindings)))

(defn- fresh-var
  "The first name in the `?v'`, `?v''`, … series that `taken` does not already speak
  for.  Deterministic: a gensym would give an engine whose contract is order
  independence a different binding map on every run of the same query."
  [v taken]
  (loop [s (str v "'")]
    (let [c (sx/intern-sym (symbol s))]
      (if (contains? taken c) (recur (str s "'")) c))))

(defn freshen-rule
  "`rule` with every variable `taken` already speaks for renamed apart.

  Without this, `(anc ?x ?z) :- (parentOf ?x ?y) (anc ?y ?z)` expanded twice on one path
  asks `unify` to make `?x` both the grandchild and the child.  That fails, the branch
  is lost, and an ancestor query answers only at distance one — a wrong answer, not a
  slow one.

  Nothing is renamed when nothing clashes: the top-level expansion of a query binds
  nothing yet, and a rule used once per path never meets itself.  Those pay one set
  scan and get the rule they passed in.

  The `exceptWhen` guard reads the rule's **own** variable names out of a completed
  binding map (`provers/exception-holds?` substitutes the stored exception query with
  them), so a renamed rule's guard is wrapped to bind those names to whatever this
  instance's variables resolved to.  A guard that fired before renaming fires after it."
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
  "A rule's antecedents in the order they should be *solved*, given the bindings the
  head match already produced.  Stored antecedent order is canonical order — chosen
  so two spellings of one rule dedup to one sentex (`sentex/canonicalize-rule`) — and
  canonical order is structural, so it bears no relation to what is cheap to run.
  Reordering here changes cost, never the answer set: a conjunction is commutative,
  and `vaelii.impl.plan` fixes in place the two literals whose position *is* operational
  (the evaluables and the recursive one).

  Antecedents are substituted **before** planning, not after, so the planner costs
  them against real values — `count-at [parentOf Tom]` is an exact count where
  `parentOf` with a bound but unknown first argument is costed at the whole extent.
  Pushing the substituted literals is equivalent to pushing the originals, because
  every binding map they are later substituted with extends this one.

  `est-override`, when given, is passed through to `plan/order` — the executor
  whose subgoals are answered by the prover registry costs them by the registry
  (`provers/est-goal`) rather than by the index alone."
  ([kb antecedents consequent context bindings]
   (planned-antecedents kb antecedents consequent context bindings nil))
  ([kb antecedents consequent context bindings est-override]
   (plan/order kb
               (mapv #(substitute % bindings) antecedents)
               context
               (cond-> {:consequent-pred (when (sequential? consequent) (first consequent))}
                 est-override (assoc :est-override est-override)))))

;; ---- deferred antecedents (computed, not matched or expanded) -----------
;; A deferred literal — `different` / `evaluate` / `unknown` (`sentex/deferred-
;; predicates`) — is not a stored fact and not a rule head: it is *computed* by a
;; prover from the bindings the other antecedents produced.  The forward chainer routes
;; these through the registry (`chain/solve-deferred`); the two backward chainers here
;; must do the same, or a rule with such an antecedent silently proves nothing.  But this
;; namespace sits *below* the registry (`provers` requires `resolution`), so it cannot name
;; `provers/solve-goal` at compile time — `unknown` runs the registry back over its own
;; argument, which makes negation-as-failure mutually recursive with the chainer asking for
;; it.  So the registry is reached through `vaelii.impl.wiring`, where that call is one of
;; the two the require graph cannot express and the reason is written down.

(defn solve-deferred
  "Extension binding-maps for a deferred antecedent `g` — already substituted, so its
  inputs are ground (canonical order and the planner place it after its binders), computed
  by the prover registry through `wiring/solve-goal`.  Nothing when the literal is
  inapplicable (unbound inputs, a false test): a deferred literal that yields no solution
  simply prunes the branch, the evaluable contract `vaelii.impl.plan` documents.

  This lets this chainer discharge a `different` / `evaluate` / `unknown` antecedent by
  computation; matching or rule expansion alone would silently prove nothing for it,
  where `ask` honours it because the registry holds a prover for each, and forward
  chaining honours it at the antecedent join.  See docs/naf.md."
  [kb g context]
  (wiring/solve-goal kb g context))

;; ---- guard markers on the goal stack ------------------------------------
;; `prove` reduces a rule to subgoals by pushing them, so a rule's `exceptWhen` guard
;; has no natural call site: by the time the antecedents are solved the rule frame is
;; long gone.  Pushing a marker *behind* the antecedents puts the check exactly where
;; the argument becomes complete, and costs one extra stack entry per excepted firing.

(defn- ->guard-marker [guard] [::guard guard])
(defn- guard-marker? [g] (and (vector? g) (= ::guard (first g))))
(defn- marker-guard  [g] (second g))

;; ---- scope markers on the goal stack -------------------------------------
;; The loop guard is a property of a goal's own *derivation path*, not of the frame it
;; happens to ride in.  Expanding a goal pushes its antecedents and the conjuncts still
;; queued behind them into one frame, so a `:seen` grown for the expansion would stay in
;; force for those siblings too: a later conjunct repeating that goal-key would be
;; refused rule expansion and answer nothing, leaving `[(anc Tom ?y) (anc Tom ?z)]` empty
;; where each conjunct alone answers.  A marker behind the antecedents restores the
;; scope the expansion started from, exactly where that subtree ends — the same place,
;; and the same one-stack-entry cost, as the guard marker above.

(defn- ->scope-marker [seen] [::scope seen])
(defn- scope-marker? [g] (and (vector? g) (= ::scope (first g))))
(defn- marker-seen   [g] (second g))

;; ---- defeat markers on the goal stack ------------------------------------
;; The same trick a third time, and for the third version of the same reason: a rule
;; expansion's *answer* is the goal it was opened for, instantiated by the bindings its
;; antecedents finally produce — and by then the frame that opened it is gone.  A marker
;; behind the antecedents puts the check exactly where the answer becomes ground, which is
;; also the only place it can be asked: earlier the goal is still a pattern, and later it
;; has already flowed into the conjuncts queued behind it.
;;
;; Behind the guard and inside the scope, so an excepted firing is refused before this and
;; the check reads the same completed bindings the guard did.  Pushed only for a goal
;; `defeatable-goal?` claims, so a KB with no defeat on that predicate carries no extra
;; stack entry.

(defn- ->defeat-marker [goal] [::defeat goal])
(defn- defeat-marker? [g] (and (vector? g) (= ::defeat (first g))))
(defn- marker-goal    [g] (second g))

;; ---- answers belief has already decided against -------------------------
;; A backward chainer filters *rules* by belief (`rule-believed?`) and *facts* by belief
;; (`matches-visible`), and until an answer is one of those two it filters nothing.  So a
;; conclusion the JTMS holds **defeated** — a `(flies Tweety)` beaten by a monotonic `(not
;; (flies Tweety))` — is re-derivable by opening the rule that concluded it and proving it
;; again, which would answer both sides of a clash belief has settled.
;;
;; The contract is that they do not: **the proving levels agree with belief.**  Belief has
;; decided that datum is OUT under the current state, and a chainer that reads it IN is not
;; answering a harder question, it is answering a stale one.  That holds for a defeated
;; *premise* a rule re-derives from other believed premises too, and deliberately: the
;; defeat is a claim about the datum, not about one derivation of it, so a second route to
;; the same sentence reaches the same OUT.  Retract the defeater and the datum revives, and
;; the chainers answer it again with nothing else having changed.
;;
;; **Only `defeated`.**  The other two non-belief states are handled elsewhere and must not
;; be folded in here: a `blocked` justification is swept, so nothing survives for a chainer
;; to find, and a `superseded` spelling is displaced by an equality merge, which the goal
;; rewrite applies before any prover sees the goal (docs/equality.md).
;;
;; **The stored-fact leaf is not on this path.**  `matches-visible` filters belief already,
;; so a defeated stored fact never matches; what this adds is a check on the answers *rule
;; expansion* produces, one lookup apiece and only for a goal whose functor some defeated
;; datum carries.

(defn defeated-index
  "What the backward chainers filter a rule-expanded answer against: `{:standing
  {sentence #{handle}} :functors #{functor}}` over the targets of the placed defeats
  (`reads/as-stored-named-global`) and, while an `except` is stored, the members of the placed
  `(contradicts …)`, since a reader whose excepts lower a conflict member's class reads it
  defeated — or **nil** when the walk reads nothing (`exc/placed-reads?`).

  Nil is the presence check every caller reads, and it is the common case: a KB with no
  contradiction pays one set deref per query and nothing else.  `:functors` is the second
  check, and the one that keeps the cost off a KB that *has* a defeat somewhere: a goal
  whose functor no target carries can produce no withdrawn answer, so it is never
  checked.  The index reads the standing defeats and placed `contradicts`, and no nogood
  candidate: a candidate that no defeat or placed `contradicts` names is defeated at no
  reader.

  Built once per query rather than asked per answer: a query writes nothing, so the
  index cannot move underneath the search that read it.  `defeated-answer?` asks the
  query's reader whether it takes a member OUT (docs/nmtms.md, \"A defeat is scoped to its
  vantage\")."
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
  "Is `sentence` — an answer a rule expansion produced — a stored member of a nogood
  (`defeated-index`) that a nogood's defeat in force, or a placed conflict, removes at the
  query's reader (`exc/defeats-of`): `context` for a concrete one, and the member's own
  context for an unscoped read, the reading a read with no reader gives?  A guard defeat
  covers one firing and not the sentence, so it removes no answer a rule expansion
  produced.

  Canonicalized against the KB before the lookup (`kb-sentex`), since the answer is built
  from a goal and its bindings while the index holds stored sentences: a symmetric
  literal's arguments are sorted in one and not the other, and comparing them raw would
  miss the very answer being filtered."
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
  "An optional observer of the DFS's **dead ends** — `(fn [goal depth])` — or nil, the
  default.

  A dead end is a subgoal, substituted under the frame's bindings, that no visible
  believed fact and no rule consequent unified with.  A branch **cut short** — by the
  per-path loop guard, `:max-depth` or the term-growth ceiling
  (`default-max-term-growth`) — is not reported.  The return value is ignored, so an
  observed run takes the same path as an unobserved one.  Only `prove`'s loop reports;
  the lazy `backward` does not.  nil costs one var deref per expanded goal.
  docs/abduction.md, \"The dead end\", gives the reasons."
  nil)

(defn- leaf-solutions
  "Extension bindings for `g` without expanding any rule — the chainer's **leaf**.

  nil `leaf-solver` reads the stored facts (`matches-visible`).  `vaelii.core/prove` and
  `vaelii.core/query` pass the registry.

  The separate call exists because a rule's antecedent is not always a fact question.  A caller
  that wants an antecedent answerable by *any* prover — transitivity, an evaluable, an
  inferred argument type — passes the registry here, and gets one chainer doing the rule
  expansion over whatever leaf semantics it was handed.  The alternative is a second
  chainer that differs from this one only in that line, which is what this replaces."
  [kb g context leaf-solver]
  (if leaf-solver
    (leaf-solver kb g context)
    (map (fn [m] (nth m 1)) (matches-visible kb g context))))

(defn initial-prove-stack
  "The one-frame DFS stack `prove` starts from: the (cost-ordered) conjunction, no
  bindings, an empty loop guard, depth 0, the **answer variables** — the query's own,
  which every frame below inherits unchanged — and the query's own **term depth**
  (`term-depth`), the basis the term-growth cut starts measuring a subgoal against.  It
  is a *starting* basis rather than a fixed one: a leaf match that binds a deeper stored
  term raises it for the frames below (`grown-term-base`), so what the ceiling bounds is
  the nesting a rule invented rather than the nesting the KB already held.

  The basis rides the *stack* rather than the bounds map because the stack is the
  continuation: a `resume` picks up frames it did not build, and a projection recomputed
  from a budget could not know what the original question asked for.  The term base
  rides it for the same reason, and for a second: it is per **path**, so a resumed
  segment measures growth from what its own frames had already met rather than from
  whatever subgoal it happened to stop on.

  Exposed so `prove-within` can seed a bounded run and hand its unfinished stack back to
  `resume`.

  `est-override` costs the top conjunction by something other than the index — the same
  shape, and for the same reason, as `planned-antecedents` takes for a rule's antecedents.
  An executor whose leaf is the prover registry passes it, because a `genl` conjunct that
  a cached closure answers costs the closure's size and not the handful of stored edges
  the trie can count."
  ([kb goals context] (initial-prove-stack kb goals context nil))
  ([kb goals context est-override]
   [{:goals       (plan/order kb goals context {:est-override est-override})
     :bindings    no-bindings
     :seen        #{}
     :depth       0
     :answer-vars (sx/form-variables (vec goals))
     :term-base   (reduce (fn [d g] (max (long d) (long (term-depth g)))) 0 goals)}]))

(defn prove-from
  "The resumable core of `prove`: run the DFS from an explicit `stack` (and the
  `solutions` gathered so far) under `bounds`, a map of optional caps —

    :deadline     an absolute `System/nanoTime` instant; stop once reached, checked
                  between steps and, through `budget/*deadline*`, inside a leaf's
                  walk (`budget/interruptible`)
    :max-results  stop once this many solutions are in hand
    :max-depth    do not expand a rule past this rule-expansion depth
    :max-term-growth
                  do not expand a subgoal whose arguments nest compound terms this
                  many levels deeper than the deepest term its own path has already
                  met (`term-depth`, `grown-term-base`); default
                  `default-max-term-growth`.  The half of the loop guard the `seen`
                  set cannot be: a rule nesting a function around a head variable
                  asks a fresh goal per expansion, and only the term's growth repeats
    :leaf-solver  how a goal is answered *without* expanding a rule — see
                  `leaf-solutions`.  nil is the stored facts, which is what `prove`
                  means by a leaf
    :est-override the cost model for a rule's antecedents, when the index model is the
                  wrong one for this executor's leaf — see `planned-antecedents`

  Returns `{:solutions <vector> :status <kw> :stack <frames>}`.  `:status` is
  `:complete` when the search space is exhausted (`:stack` empty), else `:timeout`
  or `:capped` with a **non-empty** `:stack` the caller resumes from.  With `bounds`
  nil this simply runs to completion, which is what an unbounded `prove` is.

  Each frame carries a `:depth` (rule expansions taken to reach it); a fact match
  keeps the depth and a rule expansion increments it, so `:max-depth` bounds
  *transformation* depth — the search's reach through rules — not the goal-stack
  size.  The bound checks sit at the loop top, ahead of the frame work, so a run
  can stop between any two steps and the stack it leaves behind is a faithful
  continuation.  A leaf the deadline stops inside is one step not taken: its frame goes
  back on the stack marked `:unbounded-leaf?`, and the segment that resumes it runs that
  leaf with no deadline, so a resume loop under a fixed budget gets past a walk longer
  than the budget and terminates."
  [kb rules-fn context
   {:keys [deadline max-results max-depth max-term-growth leaf-solver est-override]}
   stack solutions]
  ;; one search scope for this *segment*: the transitive closure walked once per node
  ;; rather than once per join binding, and the resident networks held still for its
  ;; length (`observe/with-search-scope`).  The loop is eager, which is the macro's
  ;; precondition.  A segment, not a query — `prove-seq` drives the same search in
  ;; several calls, and each opens a scope of its own, which is sound because a query
  ;; writes nothing that could move a held value.
  ;;
  ;; What belief has already defeated, read once for the segment and not per answer — a
  ;; `delay` rather than a `let`, so a run that expands no rule at all never touches the
  ;; TMS.  The set is derived state recomputed each settle and a query writes nothing, so
  ;; a resumed segment reading it again reads the same thing.
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
                stack (pop stack)
                ;; the ceiling a subgoal's nesting may reach on this path: the deepest
                ;; term the path has met — the query's own, raised by whatever a leaf
                ;; match bound below it — plus the growth allowance.  Stacks carry the
                ;; base, bounds the allowance, so a `resume` under a different bound
                ;; measures the same path from the same base.
                ceiling (+ (long (or term-base 0))
                           (long (or max-term-growth default-max-term-growth)))]
            (cond
              (empty? goals)
              (recur stack (conj solutions (project-answer bindings answer-vars)))

              ;; A guard marker: the antecedents ahead of it have all been solved, so this
              ;; is where an `exceptWhen` exception is asked of the completed binding.  It
              ;; rides the goal stack rather than being checked at the rule frame because
              ;; this chainer solves antecedents by *pushing* them — there is no other
              ;; moment at which "the argument is now complete" is observable.  A marker is
              ;; a **vector**, and a goal never is (see `quasiquote/prepare-conjunction-for-read`), so the two
              ;; are told apart structurally.
              (guard-marker? (first goals))
              (recur (cond-> stack
                       ((marker-guard (first goals)) bindings)
                       (conj {:goals (rest goals) :bindings bindings :seen seen :depth depth
                              :answer-vars answer-vars :term-base term-base}))
                     solutions)

              ;; the rule expansion behind this marker has produced an answer for the goal
              ;; it was opened for, and belief may already have decided against that answer
              (defeat-marker? (first goals))
              (recur (cond-> stack
                       (not (defeated-answer? kb @defeated
                              (substitute (marker-goal (first goals)) bindings)
                              context))
                       (conj {:goals (rest goals) :bindings bindings :seen seen :depth depth
                              :answer-vars answer-vars :term-base term-base}))
                     solutions)

              ;; the expanded goal's subtree ends here: the conjuncts still queued behind
              ;; it are siblings, not descendants, and answer under the scope it started in
              (scope-marker? (first goals))
              (recur (conj stack {:goals (rest goals) :bindings bindings
                                  :seen (marker-seen (first goals)) :depth depth
                                  :answer-vars answer-vars :term-base term-base})
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
                                  :term-base term-base})]
                (recur (into stack frames) solutions))

              :else
              (let [g     (substitute (first goals) bindings)
                    solve #(vec (leaf-solutions kb g context leaf-solver))
                    ;; the leaf is where a walk longer than one step runs (the
                    ;; argument-preservation prover's claim walk), so the deadline reaches
                    ;; inside it; a walk it stops leaves this frame on the stack, marked
                    ;; so the resumed segment runs that one leaf unbounded
                    leaf  (if (or deadline (:unbounded-leaf? frame))
                            (budget/interruptible (when-not (:unbounded-leaf? frame) deadline)
                                                  solve)
                            (solve))]
                (if (identical? ::budget/interrupted leaf)
                  {:solutions solutions :status :timeout
                   :stack     (conj stack (assoc frame :unbounded-leaf? true))}
                  (let [rest-goals (rest goals)
                        k          (goal-key g)
                        ;; a leaf match may hand the conjuncts behind it a deep *stored* term,
                        ;; and nothing about that is a rule growing one — so the basis rises
                        ;; with it (`grown-term-base`), and only a rule's own nesting is
                        ;; measured against the allowance
                        fact-frames (for [b leaf]
                                      {:goals rest-goals :bindings (merge bindings b) :seen seen
                                       :depth depth :answer-vars answer-vars
                                       :term-base (grown-term-base term-base b)})
                        ;; expansion cut short rather than exhausted: the goal is re-entering
                        ;; its own derivation path, the depth bound bit, or its arguments have
                        ;; grown past the term ceiling (`default-max-term-growth`).  Either way
                        ;; the branch says nothing about what the KB is missing (see
                        ;; `*dead-end*`).  The facts above are still read: a goal at the
                        ;; ceiling may be stored, and only its *expansion* is refused.
                        cut?        (or (contains? seen k)
                                        (boolean (and max-depth (>= depth max-depth)))
                                        (> (long (term-depth g)) ceiling))
                        ;; every name already in play on this path: what the bindings speak
                        ;; for, the goal's own variables, and the conjuncts still queued — the
                        ;; last of which are outer rules' unsolved antecedents, equally
                        ;; capturable by an instance expanded under them
                        taken       (when-not cut?
                                      (-> (spoken-for bindings)
                                          (into (sx/form-variables g))
                                          (into (sx/form-variables rest-goals))))
                        ;; asked once per expanded goal rather than once per rule: whether an
                        ;; answer to this goal *could* be one belief has defeated is a property
                        ;; of the goal, and it is false for every goal on a KB with no defeats
                        defeatable? (and (not cut?) (defeatable-goal? @defeated g))
                        rule-frames (when-not cut?
                                      (for [rule (rules-fn g)
                                            :let [{:keys [antecedents consequent guard]}
                                                  (freshen-rule rule taken)
                                                  b (subsuming-unify kb g consequent bindings context)]
                                            :when b]
                                        {:goals    (into (-> (planned-antecedents
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
                                                             (conj (->scope-marker seen)))
                                                         rest-goals)
                                         :bindings b
                                         :seen     (conj seen k)
                                         :depth    (inc depth)
                                         :answer-vars answer-vars
                                         :term-base term-base}))]
                    (when (and *dead-end* (not cut?)
                               (empty? fact-frames) (empty? rule-frames))
                      (*dead-end* g depth))
                    (recur (into stack (concat fact-frames rule-frames)) solutions)))))))))))

(defn prove
  "A simple depth-first backward chainer using loop/recur over an explicit goal
  stack.  Returns a vector of fully-resolved solution binding maps for proving the
  conjunction `goals` in `context`.  Type-aware (specificity) and context-aware
  (matches-visible); a per-path :seen set of goal-keys blocks a goal from
  re-expanding itself through recursive rules, and a term-growth ceiling
  (`default-max-term-growth`) blocks a subgoal whose arguments nest deeper than
  anything its own path has met, by more than the allowance — the recursion a goal key
  cannot see, since a rule wrapping a function around a head variable asks a fresh goal
  per expansion.
  Together the two make every search terminate on the data.  Prefer right-recursive
  rules — a left-recursive rule is pruned after its first expansion.  `rules-fn`
  maps a subgoal to candidate parsed rules.

  Runs to completion; `prove-from` is the bounded/resumable variant this delegates
  to (`vaelii.core/prove-within` builds the anytime contract on it), and `prove-seq`
  is the same search driven lazily.

  The 5-arg arity takes `prove-from`'s `bounds` map (`prove-seq`'s keys, plus
  `:max-results`), so a caller can run this eager search with a **registry leaf**
  (`{:leaf-solver provers/solve-goal :est-override (provers/registry-est-override kb ctx)}`)
  — an antecedent answered by a prover, an evaluatable or a cached closure rather than only
  a stored fact, the division `vaelii.core/prove` and `vaelii.core/query` run.  The 4-arg
  keeps the stored-fact leaf (`nil` bounds)."
  ([kb rules-fn goals context] (prove kb rules-fn goals context nil))
  ([kb rules-fn goals context bounds]
   (:solutions (prove-from kb rules-fn context bounds
                           (initial-prove-stack kb goals context (:est-override bounds)) []))))

(defn prove-seq
  "The same search as `prove`, **lazily** — a seq of solution binding maps that costs one
  solution per pull rather than the whole space up front.

  `prove-from` is already resumable, so this needs no second engine: run it capped at one
  result, hand back that solution, and resume from the `:stack` it left when the consumer
  asks again.  `:capped` is the only status that means *more, and allowed to continue* —
  `:complete` is exhaustion and `:timeout` is a deadline the caller set, and both end the
  seq.

  `bounds` takes `prove-from`'s keys except `:max-results`, which this drives itself; a
  consumer bounds the result count by taking that many.

  Laziness costs the search **one scope per segment** rather than one per run (see the
  comment in `prove-from`): the transitive-closure memo starts empty on each pull, and
  resident values are re-read rather than held fixed across the whole seq.  For a read
  that is sound — a query mutates no belief, so no write can move a held value.

  It is also, measurably, not paid for: over a 120-answer recursive chain, realizing
  *every* answer through this costs what the eager loop costs (40.3 ms against 40.4 ms),
  while taking one costs about half (19.0 ms against 35.0 ms) — and that chain is the
  unfavourable shape, one whose search dives to its deepest answer before yielding a
  first.  Where answers come early the gap is a multiple, not a fraction.  So `prove`
  remains the call for wanting a vector back, not for wanting it cheaper."
  ([kb rules-fn goals context] (prove-seq kb rules-fn goals context nil))
  ([kb rules-fn goals context bounds]
   (let [bounds (assoc bounds :max-results 1)]
     (letfn [(step [stack]
               (lazy-seq
                (let [{:keys [solutions status stack]}
                      (prove-from kb rules-fn context bounds stack [])]
                  (concat solutions (when (= :capped status) (step stack))))))]
       (step (initial-prove-stack kb goals context (:est-override bounds)))))))
