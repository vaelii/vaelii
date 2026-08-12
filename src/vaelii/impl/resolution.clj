;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.resolution
  "Unification, pattern matching against the indexed store, and backward chaining.

  Matching is *type-aware*: a unary type predicate is matched over the subtype
  closure, so an antecedent `(animal ?x)` is satisfied by a stored `(dog Muffet)`.
  This is how increasing an individual's specificity never loses the reasoning
  that applied to its more general types — we consult the genl closure at match
  time rather than materializing supertype facts."
  (:require [clojure.walk :as walk]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wiring :as wiring]))

;; ---- unification --------------------------------------------------------

(def no-bindings {})

;; unify and unify-var are mutually recursive (a bound variable is chased back
;; through unify), so one forward declaration is genuinely required here.
(declare unify-var)

(defn- dot-tail
  "The remaining sequence a dotted rest-variable binds to, as a canonical list."
  [y] (if (sequential? y) (apply list y) (list y)))

(defn unify
  "Unify x and y under `bindings`, returning an extended binding map or nil.
  Supports dotted rest patterns: a sublist `(. ?rest)` binds `?rest` to the whole
  remaining sequence, so `(?pred . ?args)` unifies with `(parentOf Tom Bob)` giving
  `?pred=parentOf`, `?args=(Tom Bob)`."
  ([x y] (unify x y no-bindings))
  ([x y bindings]
   (cond
     (nil? bindings)  nil
     (= x y)          bindings
     (sx/variable? x) (unify-var x y bindings)
     (sx/variable? y) (unify-var y x bindings)
     (and (sequential? x) (= '. (first x))) (unify-var (second x) (dot-tail y) bindings)
     (and (sequential? y) (= '. (first y))) (unify-var (second y) (dot-tail x) bindings)
     (and (sequential? x) (sequential? y) (seq x) (seq y))
     (unify (rest x) (rest y) (unify (first x) (first y) bindings))
     (and (sequential? x) (sequential? y) (empty? x) (empty? y))
     bindings
     :else            nil)))

(defn- occurs?
  "Does variable `v` occur in `x`, resolving `x`'s variables through `bindings`?  The
  guard `unify-var` needs before binding `v` to `x`: without it, unifying `?x` with
  `(f ?x)` builds the cyclic binding `{?x (f ?x)}`, and `substitute` — which assumes
  acyclic bindings — loops on it.  Resolves each variable inline rather than
  substituting `x` whole first, so it needs no forward reference to `substitute` and
  stops at the first occurrence.  Terminates because every prior binding was itself
  occurs-checked, so `bindings` is acyclic."
  [v x bindings]
  (cond
    (sx/variable? x) (or (= v x)
                         (when-let [b (get bindings x)] (occurs? v b bindings)))
    (sequential? x)  (boolean (some #(occurs? v % bindings) x))
    :else            false))

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
  in, so `(?pred . ?args)` with `?args=(Tom Bob)` becomes `(parentOf Tom Bob)`."
  [pattern bindings]
  (cond
    (sx/variable? pattern) (if-let [b (get bindings pattern)]
                             (substitute b bindings)
                             pattern)
    (and (sequential? pattern) (some #{'.} pattern))
    (let [head (map #(substitute % bindings) (take-while #(not= '. %) pattern))
          tail (substitute (second (drop-while #(not= '. %) pattern)) bindings)]
      (if (sequential? tail)
        (concat head tail)                 ; bound rest-var → splice the tail in
        (concat head (list '. tail))))     ; still unbound → keep the dotted form intact
    (sequential? pattern)  (map #(substitute % bindings) pattern)
    :else                  pattern))

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

(defn- dotted-pattern?
  "Does `form` contain a dotted-rest splice at any nesting depth?"
  [form]
  (boolean (and (sequential? form)
                (some #(= sx/dot-marker %) (tree-seq sequential? seq form)))))

(defn- dotted-candidates
  "Every fact handle a dotted-rest pattern could unify with.

  A dot changes the pattern's arity, so neither the positional trie nor the argument
  roots can represent it: `.` is a splice marker, not an argument token.  A concrete
  functor is bounded by its fact extent.  With an open functor, enumerate the functors
  present at the matching polarity from the trie's own root roster, then union their
  extents.  `match-one` still filters polarity and unifies every candidate, so this is a
  sound superset rather than a second matcher."
  [ix truth pred]
  (if pred
    (p/sentexes-with-functor ix pred)
    (let [functors (if (= :false truth)
                     (into #{}
                           (keep (fn [body]
                                   (when (and (sequential? body) (symbol? (first body)))
                                     (first body))))
                           (p/children ix [:false]))
                     (filter symbol? (p/children ix [])))]
      (lazy-mapcat #(p/sentexes-with-functor ix %) functors))))

(def ^:dynamic *arg-root-retrieval*
  "Whether `match-one` may retrieve its candidate handles from a **secondary argument
  root** instead of always walking the trie.

  The trie narrows strictly left to right, so a pattern whose *first* argument is a
  variable but a later argument is a ground term — `(parentOf ?x Tom)`, the second
  half of a grandparent join — cannot be answered by a prefix: the trie fans out over
  every first-argument value (one lookup per node) only to keep the few
  that match the later token.  The argument root `[:argument-root pred pos term]`
  indexes exactly that later position under the pattern's own predicate, so it answers
  the same pattern with a single set read.

  When several arguments are known, `candidate-handles` intersects the pattern's
  scoped argument roots (`sentexes-with-args` — the scoping means a named functor
  needs no functor-root intersection), so knowing more of the sentence narrows on all
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
  matching levels go through `candidate-handles`, so this gates *their* candidate
  source too — never correctness: on and off return the same matches, on returns fewer
  candidates.  Negative and flat patterns are untouched — a `:false` key keeps its
  body whole, so it has no deep positions to narrow on.

  On by default: the oracle (`structural_index_test`) proves on == off over the
  corpus, and the structural retrieval is a strict candidate-set win on a
  compound-argument pattern (2 candidates vs the functor extent), so there is no
  reason to prefer the looser fallback."
  true)

(defn- candidate-handles
  "The stored handles to unify `pat` against — always a superset of the positional
  trie hits (so `match-one`'s `unify` filters it to the identical set), chosen to
  minimize index lookups.

  The trie narrows only left to right, so it is at its best when the *ground*
  arguments form a left prefix — `(parentOf Tom ?y)`, `(parentOf Tom Bob)` — and at
  its worst when a ground argument sits **after** a variable, `(parentOf ?x Tom)` or
  `(rel A ?y C)`, which it can reach only by fanning out over the intervening
  variable (a round trip per value).  For exactly that case the secondary roots are a
  *different* index order that pins the stuck position directly, and — the point of
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
  every functor by construction — a union of the scoped roots over the slot roster —
  so one `sentexes-with-arg` read of position 1, `Muffet` answers it flat; with no
  predicate to scope by, `sentexes-with-args` takes a `nil` `pred` and intersects
  those predicate-agnostic reads.

  A positive pattern with a **nested compound argument** is the third source: its
  selective information sits *inside* the compound (`QuantityFn`, `Kilogram`), which
  neither a left prefix nor a top-level argument root reaches.  The structural trie
  narrows on it (`*structural-index*`); off, it falls back to the functor extent — a
  correct superset, and the baseline to measure the structural narrowing against.

  A **dotted-rest pattern** cannot use either positional model: its `.` is a splice
  marker rather than a stored argument, and the tail has no fixed arity.  It reads the
  concrete functor's whole extent, or fans over the functor roster when the functor is
  open, then lets `unify` bind and filter the tail.

  Everything else keeps the trie: a fully-ground test (its leaf is exact), a pattern
  whose ground arguments are already a left prefix, and a pattern whose only
  after-a-variable selectivity is a **non-indexable** token (a number/string the
  roots do not key), where the trie's own token narrowing beats a functor-root scan.
  Zero-regression by construction — the diverted case is the one the trie answers
  with a full fan-out.

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
            dotted? (dotted-pattern? body)
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
            path
            (cond
              ;; A dotted tail changes arity.  Looking up `.` as a trie or argument-root
              ;; token quietly returns no candidates because stored facts contain only
              ;; the arguments it stands for.
              dotted? :dotted-extent

              ;; **A negative key holds its whole body as one token**, so the trie can match
              ;; a negative only *exactly* — `[:false (dog ?0) c]` is a different key from
              ;; `[:false (dog Tom) c]`, and no amount of the body being ground narrows it,
              ;; because none of it is a level.  So `p/lookup` answers `#{}` for every open
              ;; negative, and this is correctness rather than cost: the matches are not
              ;; merely reached slowly, they are not reached at all.
              ;;
              ;; The secondary indexes are the only ones that see inside a negative: the
              ;; functor root spans both polarities (a negative roots under its positive
              ;; body's functor) and so do the argument roots.  With neither pinned — an
              ;; open functor over open arguments — the `:false` node's own children are
              ;; the negative analogue of the root child fan a fully-open positive gets,
              ;; and they are exactly the distinct negative bodies stored.
              ;;
              ;; Ungated, unlike the cost refinements below: `*arg-root-retrieval*` false is
              ;; meant to give the trie as a *reference*, and for this shape the trie has no
              ;; answer to be a reference for.
              (and (= :false (:truth pat)) (not (sx/ground-term? body)))
              (if (or pred (seq ground)) :negative-roots :negative-fan)

              ;; A ground argument sitting **after** a variable, which the trie can reach
              ;; only by fanning out over the intervening variable.  This wins over the
              ;; structural walk below even when the stuck argument is a compound: the
              ;; argument root keys the compound *whole*, so it pins in one read what the
              ;; linearized trie key still has to fan out to reach.
              (and *arg-root-retrieval* stuck?) :arg-roots

              ;; a positive pattern with a nested compound argument — the structural case.
              ;; The trie key linearizes the compound, so `p/lookup` narrows on its interior;
              ;; off, the functor extent is the correct fallback superset.  A variable functor
              ;; roots nothing, so it always takes the trie.
              (and (= :true (:truth pat)) (some sequential? args))
              (if (or *structural-index* (nil? pred)) :structural :functor-extent)

              ;; trie: left-prefix, test, or number-only
              :else :trie)]
        (prof/record-goal pat path)
        (case path
          :dotted-extent (dotted-candidates ix (:truth pat) pred)
          :negative-roots (p/sentexes-with-args ix pred ground)
          :negative-fan   (let [pth (sx/path pat)]
                            (into #{} (mapcat #(p/lookup ix (assoc pth 1 %)))
                                  (p/children ix [:false])))
          :arg-roots      (p/sentexes-with-args ix pred ground)  ; intersect the scoped arg roots
          :structural     (p/lookup ix (sx/path pat))
          :functor-extent (p/sentexes-with-functor ix pred)
          :trie           (p/lookup ix (sx/path pat)))))))

(defn match1
  "Unify a single antecedent pattern against a ground fact sentence, honoring
  **predicate specificity**: a fact whose functor is a *spec* (sub-predicate, via the
  genl closure) of the antecedent's functor satisfies it, with the arguments unified.

  For a unary type antecedent this is the ordinary subtype rule — `(animal ?x)` is met
  by `(dog Muffet)`.  Generalized to n-ary predicates, `(parentOf ?x ?y)` is met by
  `(fatherOf Tom Bob)` once `(genl fatherOf parentOf)` holds — the same subsumption the
  type hierarchy gives, applied to the predicate hierarchy.  When the functors are
  equal (the common case) or the antecedent's functor has no sub-predicates, this is a
  plain unify, so nothing changes for a KB without predicate-genl edges."
  [kb antecedent fact]
  (if (and (unary? antecedent) (unary? fact))
    (let [[t a]  antecedent
          [t' x] fact]
      (when (contains? (tax/specs (:taxonomy kb) t) t') (unify a x)))
    (let [af (when (sequential? antecedent) (first antecedent))
          ff (when (sequential? fact) (first fact))]
      (if (and (symbol? af) (not (sx/variable? af)) (symbol? ff) (not= af ff)
               (contains? (tax/specs (:taxonomy kb) af) ff))
        (unify (rest antecedent) (rest fact))        ; sub-predicate: unify the arguments
        (unify antecedent fact)))))

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
  unify)."
  ([kb goal consequent] (subsuming-unify kb goal consequent no-bindings))
  ([kb goal consequent bindings]
   (let [gf (when (sequential? goal) (first goal))
         cf (when (sequential? consequent) (first consequent))]
     (if (and (symbol? gf) (not (sx/variable? gf))
              (symbol? cf) (not (sx/variable? cf))
              (not= gf cf)
              (contains? (tax/specs (:taxonomy kb) gf) cf))
       (unify (rest goal) (rest consequent) bindings)
       (unify goal consequent bindings)))))

(defn concluding-rule-handles
  "Handles of rules whose consequent predicate is `pred` **or a spec of it** — a rule
  concluding a subtype answers a supertype goal, the backward dual of `fire-rules-for`
  fanning a new fact over its supertypes.  Computed as the intersection `specs(pred) ∩
  rules-by-consequent`: iterate the spec closure and probe the consequent index.  A
  variable or non-symbol `pred` cannot be a type, so it degrades to the plain lookup.

  **The answer is bounded by the concluding rules; the cost is bounded by the taxonomy.**
  One index probe per spec, so a goal on a type with 364 subtypes takes 364 probes to
  discover that no rule concludes any of them — and `provers/shadowing-channels` asks
  this once per goal, on the path `sole-prover` takes.  Cheap per probe and never a
  record fetch, but it is the spec closure that sizes it, not the rule count.

  With a `context`, the spec fan walks only the genl edges visible from it — a rule
  concluding a subtype answers a supertype goal exactly where the subtype edge is
  visible, mirroring the matching fan-out."
  ([kb pred] (concluding-rule-handles kb pred nil))
  ([kb pred context]
   (if (and (symbol? pred) (not (sx/variable? pred)))
     (into #{} (mapcat #(p/rules-by-consequent (:index kb) %))
           (tax/specs (:taxonomy kb) pred context))
     (p/rules-by-consequent (:index kb) pred))))

(defn rule-visible-from?
  "May a rule stored in `rule-ctx` answer a goal asked from `context`?

  A rule is a sentex, so it is inherited like any other: a context reasons with the
  rules its `genlCx` up-cone holds and no others.  This is the backward dual of
  forward chaining refusing to place a conclusion in a context that cannot see the
  rule — without it a context proves `(ancestorOf Tom Bob)` from a rule some
  sibling theory wrote, while the *forward* firing of that same rule correctly
  evaporates for want of a placement, and the two chainers disagree about one KB.

  An open `?ctx` (or nil) is the unscoped path: such a query asks about the KB rather
  than from a vantage, exactly as the closure reads read it."
  [kb context rule-ctx]
  (or (not (and (symbol? context) (not (sx/variable? context))))
      (tax/sees? (:taxonomy kb) context rule-ctx)))

(defn rule-believed?
  "May the rule at `handle` chain — is it believed?

  A rule is a sentex, so the fourth invariant holds of it as it holds of a fact: a
  *stored* rule is not a *believed* one.  Both chainers reach a rule through the rule
  index, which posts on storage and knows nothing of belief, so without this a rule
  whose support has gone on holding conclusions the KB no longer has grounds for — and
  a **derived** rule (one a generator stamped out, docs/generators.md) would never come
  back out of the KB at all, since retracting what licensed it is the only way it can
  leave.

  A sentex the TMS holds no node for is available, not disbelieved: answering \"not
  believed\" of an absence would be reading it as a verdict, where what it says is that
  the network was never asked.  For a **rule** that arm is defence rather than a live
  case — `core/assert-inert` refuses a rule (`:not-indexable`), so a stored rule has
  been through a door that premised it — and it is worth keeping only because a wrong
  answer here is a rule that silently stops firing.

  An **inert rule** is a different thing and is *not* what this arm is about: it is
  believed like any other rule and gated by its `:direction` alone
  (`rules/forward-sentex?` / `backward-sentex?`), which is what makes it documentation
  rather than an absence (docs/inference.md)."
  [kb handle]
  (let [tms (:tms kb)]
    (or (not (jtms/known-datum? tms handle))
        (jtms/in? tms handle))))

(defn visible-supporter-fn
  "`handle -> boolean`, memoized: does `context` see the context the sentex `handle`
  was asserted from?  nil when `context` is nil or a `?var` — the unscoped path, which
  every caller reads as *no filter* rather than as *nothing visible*.

  The seam a **context-scoped equality** read hangs on: the equality partition records
  its supporters as handles, and only the record store knows where each was asserted."
  [kb context]
  (when (and (symbol? context) (not (sx/variable? context)))
    (let [tax (:taxonomy kb) recs (:records kb)]
      (memoize (fn [h]
                 (boolean (when-let [sx (p/get-sentex recs h)]
                            (tax/sees? tax context (:context sx)))))))))

(defn representative-in
  "`term`'s equality-class representative as `visible?` sees the merges — the global
  one when nothing has merged `term` (the overwhelming case, one map lookup), when the
  read is unscoped (`visible?` nil), or when the reader can see the term's whole class
  anyway (`tax/class-fully-visible?`), which is every KB stating its merges where the
  reader can see them.  Only a class genuinely split by an invisible edge pays for
  `scoped-class`."
  [kb visible? term]
  (let [tax (:taxonomy kb)]
    (if (and visible? (tax/merged? tax term) (not (tax/class-fully-visible? tax term visible?)))
      (second (tax/scoped-class tax term visible?))
      (tax/representative tax term))))

(defn representative-term
  "`term` with every non-variable symbol replaced by its class representative
  (`representative-in`), **recursively** — so a merged symbol nested inside a compound is
  rewritten at whatever depth it sits.

  `representative-in` alone is a flat lookup: the closure is keyed by symbol, so handing
  it a compound returns that compound unchanged and the caller silently compares
  unnormalized forms.  Every caller that may see a compound wants this one, and the
  difference is congruence — with `(sameAs Kilogram Kg)` believed, `(QuantityFn 5
  Kilogram)` and `(QuantityFn 5 Kg)` normalize to one term here and to two there."
  [kb visible? term]
  (cond
    (sequential? term) (apply list (map #(representative-term kb visible? %) term))
    (symbol? term)     (if (sx/variable? term) term (representative-in kb visible? term))
    :else              term))

(defn kb-sentex
  "Build a sentex canonicalized against this KB's taxonomy: a symmetric predicate's
  arguments are sorted, so `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)` become the
  same sentex.  Every construction that stores or looks one up must go through this —
  otherwise an asserted form and a queried form could key differently.

  The property read is **global on purpose**: a sentex has one key, so whether a
  predicate sorts its arguments cannot vary by who is asking — a reader-scoped read
  here would store one literal under two keys and break dedup, retraction, and the
  mirror probe at once."
  [kb sentence context]
  (sx/sentex sentence context
             {:symmetric? #(tax/has-prop? (:taxonomy kb) :symmetric %)}))

(defn- match-one
  "Matches are *belief-sensitive*: a handle that is stored but currently OUT (e.g. a
  default defeated by a contradiction) does not match.  This is what lets a
  disbelieved sentex stay in the store for possible revival without polluting
  reasoning.

  Yields `[handle bindings stored-sentex]`.  The record has already been fetched to
  unify against, so it rides along rather than making a caller that wants the
  matched sentence pay for a second round trip; callers that only want the bindings
  destructure `[_ b]` or take `second` and ignore it.  `keep` keeps this lazy — one
  solution costs one `get-sentex`, not one per candidate handle."
  [kb sentence context]
  (let [pat (kb-sentex kb sentence context)]
    (keep (fn [h]
            (when (jtms/in? (:tms kb) h)
              (let [stored (p/get-sentex (:records kb) h)]
                ;; an exceptWhen meta-sentex is internal bookkeeping (a rule's
                ;; exception), not a domain fact, and it is the one *non-ground* stored
                ;; Atomic — so it is skipped here, keeping the trie and argument-root
                ;; retrieval paths in agreement and ordinary queries clear of it.  A
                ;; rule's exceptions are read through `provers/rule-exceptions`.
                (when (and (not (sx/exceptWhen-meta? (:sentence stored)))
                           ;; match polarity too: a positive pattern like (?p ?x) must not
                           ;; bind ?p to `not` against a stored negation (the wildcard trie
                           ;; lookup can surface a `[:false ..]` key, but the truths differ).
                           (= (:truth pat) (:truth stored)))
                  (when-let [b (unify (:context pat) (:context stored)
                                      (unify (:sentence pat) (:sentence stored)))]
                    [h b stored])))))
          ;; a superset of the trie hits when an argument root is tighter than a
          ;; leading-variable fan-out; the unify above filters it to the same set
          (candidate-handles kb pat))))

(defn raw-match
  "Match a literal in one **literal** context — no genlCx inheritance, no subtype
  fan-out — trying **both argument orders for a symmetric predicate**.  Only
  fully-ground symmetric literals are stored sorted (see `vaelii.impl.sentex`), so the
  mirrored probe is what makes lookup order-insensitive: it retrieves `(siblingOf
  Ann Carol)` from the pattern `(siblingOf ?x Carol)` or `(siblingOf Carol ?x)`
  alike, and keeps a fact reachable even if it was asserted before its `symmetric`
  declaration.  Results are deduped by handle, so a palindrome matches once.

  Lazy through the mirror: `lazy-cat` defers the second probe *and* the `seen` set
  that dedupes it, so a consumer answered by the direct hits never pays for either."
  [kb sentence context]
  (let [hits (match-one kb sentence context)]
    ;; the global property, matching kb-sentex's key discipline — the mirror probe
    ;; exists because storage sorted the arguments, and storage does not vary by reader
    (if (sx/symmetric-literal? sentence #(tax/has-prop? (:taxonomy kb) :symmetric %))
      (lazy-cat hits
                (let [seen (into #{} (map first) hits)]
                  (remove (comp seen first)
                          (match-one kb (sx/mirror-literal sentence) context))))
      hits)))

(defn sub-predicates
  "The sub-predicate (genl spec) closure the matching fan-out walks for functor `f`,
  from the vantage `context` — the global closure when the vantage is a variable or
  nil.  The **single definition every matcher shares** (`match-pattern`,
  `matches-hierarchical`, the rete alpha matcher), so the fan cannot drift between
  them: a genl edge invisible from the vantage does not connect a sub-predicate's
  facts to the pattern, exactly as it does not appear in the closure reads."
  [kb f context]
  (tax/specs (:taxonomy kb) f context))

(defn match-pattern
  "Seq of [handle bindings] for stored sentexes matching `sentence` within
  `context` (default the wildcard ?ctx).  The **functor fans out over its sub-predicate
  (genl spec) closure**, so a unary type predicate is met by its subtypes
  (`(animal ?x)` ← `(dog Muffet)`) and — with predicate-genl edges — an n-ary predicate
  by its sub-predicates (`(parentOf a ?x)` ← `(fatherOf a v)`).  A functor with no
  sub-predicates has a singleton closure, so this is a no-op for it (the overwhelming
  common case — one cached set lookup, no fan).

  The fan is scoped to the genl edges visible from `vantage` — by default the
  literal context itself, and the global closure for a `?ctx` match.  The four-arity
  exists for `matches-visible*`, which matches at each ancestor context in turn but
  stands at the *view* context throughout: scoping the fan by the ancestor would
  shrink the vantage as the walk ascends, and the set-algebra twin (which filters by
  the view's cone once) would disagree."
  ([kb sentence] (match-pattern kb sentence '?ctx))
  ([kb sentence context] (match-pattern kb sentence context context))
  ([kb sentence context vantage]
   (let [f (when (sequential? sentence) (first sentence))]
     (if (and (symbol? f) (not (sx/variable? f)))
       (let [subs (sub-predicates kb f vantage)]
         (if (= subs #{f})
           (raw-match kb sentence context)                  ; no sub-predicates: as before
           (lazy-mapcat (fn [f'] (raw-match kb (cons f' (rest sentence)) context)) subs)))
       (raw-match kb sentence context)))))

(defn matches-visible*
  "The reference nested fan-out: `|context-up| × |specs|` trie walks.  `matches-visible`
  dispatches to this or to `matches-hierarchical`; the latter also falls back here for
  a shape it does not handle, so this must not re-dispatch (it is the fixed point that
  breaks the cycle)."
  [kb sentence view-context]
  (if (sx/variable? view-context)
    (match-pattern kb sentence '?ctx)
    (lazy-mapcat (fn [c] (match-pattern kb sentence c view-context))
                 (tax/context-up (:taxonomy kb) view-context))))

;; ---- hierarchical (set-algebra) retrieval -------------------------------
;; `matches-visible` answers `(p a ?x)` visible from `c` by a *product* of lookups:
;; `|context-up(c)|` contexts × `|specs(p)|` sub-predicates, each its own trie walk.
;; But the answer is an **intersection over three hierarchies** — a fact matches iff
;; its predicate is in `specs(p)`, its context in `context-up(c)`, and its arguments
;; unify — and the argument roots index a bound argument across every context at
;; once, scoped by predicate.  So lead with the bound argument's posting lists (one
;; scoped set read per sub-predicate) and make the context hierarchy an **in-memory
;; membership filter** over the cached closure, the predicate filter being satisfied
;; by which buckets are read.  The product collapses to a hash lookup per
;; sub-predicate, independent of how deep the context hierarchy is.
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
  The two differ only in which dimensions are pinned — a variable functor names no
  predicate, so there is no predicate hierarchy to filter by and every candidate's
  functor is admissible, while the argument root and the context cone still narrow
  exactly as they do for a concrete one.

  A negation keys under `not`/its positive body, a dotted pattern is not a stored-fact
  shape, and a variable functor with no indexable argument pins nothing at all; those
  fall back to `matches-visible`."
  [sentence]
  (and (sequential? sentence) (seq sentence)
       (symbol? (first sentence))
       (not= 'not (first sentence))
       (not-any? #(= '. %) sentence)
       (or (not (sx/variable? (first sentence)))
           (some sx/indexable-term? (rest sentence)))))

(defn- mirror-pos [pos] (if (= pos 1) 2 1))

(defn- lead-candidates
  "A **lazy** superset of the matching handles, led by the tightest bound argument.
  The argument roots are scoped by predicate (`[:argument-root pred pos term]`), so
  with a spec closure in hand the read is each sub-predicate's own bucket at that
  position — the context hierarchy is filtered afterwards in memory, and the predicate
  filter is satisfied by construction.  A variable functor reads the predicate-agnostic
  union instead (`sentexes-with-arg`, over the slot roster), which spans every functor;
  with no bound argument at all, the sub-predicates' functor extents.  A symmetric
  sub-predicate may store the term at the mirror position, so when any sub-predicate is
  symmetric both positions are taken.

  Lazy so an existence check short-circuits without realizing the whole candidate set:
  each posting set is handed back by reference and the per-spec fan is `lazy-mapcat`,
  so buckets are read one sub-predicate at a time as `matches-hierarchical` consumes
  them.  The symmetric two-position concat can repeat a handle stored at both
  positions; `matches-hierarchical`'s `seen` set dedups the emitted matches, so the
  result stays the identical set."
  [kb specs args sym?]
  (let [ix     (:index kb)
        ground (keep-indexed (fn [i a] (when (sx/indexable-term? a) [(inc i) a])) args)]
    (if (seq ground)
      (let [cnt (fn [[pos term]]
                  (cond-> (p/count-with-arg ix pos term)
                    sym? (+ (p/count-with-arg ix (mirror-pos pos) term))))
            [pos term] (apply min-key cnt ground)
            ;; The argument roots are scoped by predicate, so read each sub-predicate's
            ;; own bucket. That is the whole of the saving: the candidates arriving at
            ;; the filter below are this literal's predicates only, where the
            ;; predicate-agnostic read returns every fact holding `term` at `pos` —
            ;; which, on a materialising join, is dominated by the derived facts no rule
            ;; ever reads back.  `lazy-mapcat`, not `mapcat`: one scoped read per
            ;; sub-predicate as the caller consumes, so an existence check still touches
            ;; one bucket, not `|specs|` of them.
            scoped (fn [pd pz] (p/sentexes-with-args ix pd {pz term}))]
        (if (seq specs)
          (if sym?
            (lazy-mapcat (fn [pd] (concat (scoped pd pos) (scoped pd (mirror-pos pos)))) specs)
            (lazy-mapcat (fn [pd] (scoped pd pos)) specs))
          ;; A variable functor names no predicate, so there is no scope to read: the
          ;; predicate-agnostic root (a union over the slot roster) is the whole
          ;; candidate set, and `unify` binds the functor per candidate.
          (if sym?
            (concat (p/sentexes-with-arg ix pos term)
                    (p/sentexes-with-arg ix (mirror-pos pos) term))
            (p/sentexes-with-arg ix pos term))))
      (mapcat #(p/sentexes-with-functor ix %) specs))))

(defn matches-hierarchical
  "The set-algebra twin of `matches-visible` for a positive literal: the identical
  `[handle bindings stored]` set, but reached by one argument-root lookup plus
  in-memory predicate/context filtering instead of the `|specs| × |context-up|`
  product of trie walks.  Falls back to `matches-visible` for any shape it does not
  handle."
  [kb sentence view-context]
  (if-not (hierarchical-literal? sentence)
    (matches-visible* kb sentence view-context)
    (let [tax   (:taxonomy kb)
          ;; a variable functor names no predicate, so there is no spec closure to fan
          ;; or filter by — every candidate's functor is admissible, and `unify` binds
          ;; the variable to it.  `lead-candidates` gets `specs` nil here and takes its
          ;; predicate-agnostic branch: the shape is admitted only with an indexable
          ;; argument, so the slot-roster union is its candidate source.
          var-fn? (sx/variable? (first sentence))
          specs (when-not var-fn? (sub-predicates kb (first sentence) view-context))
          pred-ok? (if var-fn? (constantly true) #(contains? specs %))
          args  (rest sentence)
          up?   (not (sx/variable? view-context))
          up    (when up? (tax/context-up tax view-context))
          ctx-ok? (if up? #(contains? up %) (constantly true))
          ;; is any sub-predicate symmetric — i.e. might a match be stored with its
          ;; arguments in the mirror order?  Only a *binary* literal has a mirror, and
          ;; the question is one of set intersection, so drive it from the **declared
          ;; symmetric predicates** (a handful) and test membership in `specs` rather
          ;; than the other way round: a broad functor's spec closure is the whole type
          ;; hierarchy, and scanning it would cost more than the retrieval it precedes.
          ;; A variable functor is never a symmetric literal (`sx/symmetric-literal?`
          ;; asks the taxonomy about the functor, and a variable has no property), so
          ;; the reference runs no mirror probe for it and neither may this.
          ;; `sym?` is a *gate*, per call: it widens `lead-candidates`' bucket
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
          seen  (volatile! #{})
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
          pat-for (fn [f' pctx rev?]
                    (let [pf (pat-functor f')
                          k  [pf pctx rev?]]
                      (if-some [p (get @pats k)]
                        p
                        (let [p (kb-sentex kb (cons pf (if rev? (reverse args) args)) pctx)]
                          (vswap! pats assoc k p)
                          p))))]
      ;; the second retrieval decision in this namespace, and the one `candidate-handles`
      ;; never sees: `lead-candidates` picks its source from the same three facts, so the
      ;; label is computed from them here rather than plumbed back out of it.
      (when (prof/profiling?)
        (prof/record-literal sentence
                             (cond
                               (not (some sx/indexable-term? args)) :hier-functor-extent
                               (seq specs)                          :hier-scoped-roots
                               :else                                :hier-agnostic-roots)))
      (keep (fn [h]
              (when (and (not (contains? @seen h)) (jtms/in? (:tms kb) h))
                (when-let [stored (p/get-sentex (:records kb) h)]
                  (let [f' (some-> (sx/body stored) first)]
                    ;; predicate-hierarchy filter (the sub-predicate closure) and
                    ;; context-hierarchy filter (the genlCx up-closure), in memory;
                    ;; an exceptWhen meta-sentex is internal bookkeeping and skipped, as
                    ;; in `match-one` (the one non-ground stored Atomic)
                    (when (and (not (sx/exceptWhen-meta? (:sentence stored)))
                               (pred-ok? f') (ctx-ok? (:context stored)))
                      (let [;; concrete view: bind no ?ctx (match at the fact's own
                            ;; context, which is in the up-closure); variable view:
                            ;; bind ?ctx, exactly as match-one does
                            pctx  (if up? (:context stored) '?ctx)
                            order (fn [rev?]
                                    (let [pat (pat-for f' pctx rev?)]
                                      (when (= (:truth pat) (:truth stored))
                                        (unify (:context pat) (:context stored)
                                               (unify (:sentence pat) (:sentence stored))))))
                            b (or (order false)
                                  (when (and sym? (contains? sym-preds f'))
                                    (order true)))]
                        (when b (vswap! seen conj h) [h b stored])))))))
            (lead-candidates kb specs args sym?)))))

(defn excepted-handles
  "The handles hidden from `view-context` by believed `(except (sentexHandle H))`
  facts: an `except` asserted in a context `view-context` sees (its genlCx
  up-closure) hides its target there and in every descendant.  Empty — the common,
  fast-path case — when nothing is excepted, or when `view-context` is a variable (an
  `except` in some context hides its target *there and below*, not from the more
  general contexts above it, so an any-context read still sees it).

  **Read off the KB's `:excepted` roster, not off the index.**  The roster is
  `{context -> {hidden-handle -> #{except-handle}}}`, maintained at the store and removal
  choke points (`kb/note-excepted!`) exactly as `:opposed` is, so what this does per call
  is a deref, one `contains?` per context *holding* an except, and one `jtms/in?` per
  except in a visible one.  What it no longer does is fetch a record per except in the KB
  and re-derive its target from its sentence — which on a chaining run is per placement
  and per candidate justification, and was 89% of the run's wall clock at 1,000 excepts
  (`lein bench-hotreads`).

  **The O(1) gate is the empty roster**, which is where the functor-root count used to
  be and is both cheaper and tighter: a KB storing only `(not (except H))` roots under
  `except` and counts non-zero, while the roster — which holds only sentences that
  actually hide something — is empty and says so.

  The *iteration* is over the roster rather than over the up-closure because the roster
  is the smaller side by construction: it holds one entry per context that states an
  except, where `context-up` holds every context the reader inherits from.

  Belief stays a read, and has to: an `except` can be defeated or revived without any
  sentex arriving or leaving, so there is no choke point a believed-set could be
  maintained at.  That is the line `:opposed` draws too (blind to belief, filtered by
  whoever reads it), and it is why this is a roster rather than a clock-stamped memo —
  the scope that asks is forward chaining, which writes while it reads, so a stamped
  entry would be retired between one placement and the next.

  **A caller asking about particular handles wants `excepted?`**, which answers the same
  question without materializing this set."
  [kb view-context]
  (let [by-ctx @(:excepted kb)]
    (if (or (empty? by-ctx) (sx/variable? view-context))
      #{}
      (let [up  (tax/context-up (:taxonomy kb) view-context)
            tms (:tms kb)]
        (persistent!
         (reduce-kv (fn [acc ctx entries]
                      (if-not (contains? up ctx)                 ; visible from view-context
                        acc
                        (reduce-kv (fn [a target ehs]
                                     (if (some #(jtms/in? tms %) ehs) (conj! a target) a))
                                   acc entries)))
                    (transient #{})
                    by-ctx))))))

(defn hidden-fn
  "A predicate `(fn [handle]) -> boolean` answering, for **one** `view-context`, what
  `excepted-handles` answers for all of them at once — or **nil** when that vantage hides
  nothing at all.

  Nil rather than `(constantly false)` on purpose: it is the caller's O(1) gate, and one
  that lets it skip its filter outright instead of running a predicate that can only ever
  answer false.  Every caller is on a hot path and almost every KB hides nothing at all,
  so that distinction is the common case rather than an edge of it.

  The gate is **storage**, not belief: a cone holding excepts that are all currently
  defeated still gets a predicate, which then answers false for everything.  Deciding
  otherwise would mean asking `jtms/in?` of every except in the cone to find out whether
  to build a predicate that asks `jtms/in?` of two of them.

  The roster and the `context-up` closure are read **once**, here, and the returned
  predicate does a map lookup per context that states an except plus a `jtms/in?` per
  except naming the handle asked about — usually none.  That is the trade against
  materializing the hidden set: building the set is one pass over every except in the
  reader's cone regardless of how many handles will be asked about, and the callers ask
  about a rule's two or three antecedents, or about matches one at a time.  Since a set
  is only cheaper once the questions outnumber the excepts, and the questions are bounded
  by the answer set while the excepts are not, the predicate is the right default and the
  set is kept for the caller that genuinely wants every hidden handle."
  [kb view-context]
  (let [by-ctx @(:excepted kb)]
    (when-not (or (empty? by-ctx) (sx/variable? view-context))
      (let [up  (tax/context-up (:taxonomy kb) view-context)
            ;; only the contexts that both state an except and are visible from here —
            ;; computed once, so the predicate walks nothing it will always reject
            live (into [] (comp (filter #(contains? up (key %))) (map val)) by-ctx)
            tms  (:tms kb)]
        (when (seq live)
          (fn [handle]
            (boolean (some (fn [entries]
                             (some #(jtms/in? tms %) (get entries handle)))
                           live))))))))

(defn excepted?
  "Is the sentex at `handle` hidden from `view-context` by a believed `except`?  The
  one-shot form of `hidden-fn`, for a caller with a single handle to ask about."
  [kb handle view-context]
  (boolean (when-let [hidden? (hidden-fn kb view-context)] (hidden? handle))))

(defn without-excepted
  "Drop the `[handle …]` matches whose handle is hidden from `view-context` by a
  believed `except` — the visibility-removal filter, and the **identical seq** when the
  reader's cone stores no except at all, which is almost every read of almost every KB."
  [kb view-context matches]
  (if-let [hidden? (hidden-fn kb view-context)]
    (remove #(hidden? (first %)) matches)
    matches))

(defn retired-for?
  "Does `sentence` name a term the reader has retired — i.e. is it *not* in normal form
  for that reader?  Asked term by term rather than by building the rewritten sentence,
  since the answer is a disjunction and the first displaced symbol settles it, and gated
  per symbol on `merged?` (one `contains?` against a snapshot held by the caller) so an
  unmerged sentence never reaches the election.  `visible` is the caller's **delay** over
  the supporter memo, forced only by a symbol that got that far.  Public for the reads
  whose match shape `without-retired` cannot take — `qcn-kb/refuted-pairs` yields
  `[handle a b]` triples with no sentex at index 2, so it filters with this directly."
  [kb visible merged? sentence]
  (sx/some-symbol? (fn [t]
                     (and (merged? t) (not (sx/variable? t))
                          (not= t (representative-in kb @visible t))))
                   sentence))

(defn without-retired
  "Drop the matches whose stored spelling `view-context` has **retired** — the
  reader-scoped half of supersession.

  `jtms/superseded` holds a spelling out of belief once its own context elects another,
  and that is per *datum*: a sentex lives in one context, so one flag answers for one
  context.  Staleness is per *reader*.  A fact stated above a merge is believed where it
  lives — its own context was told nothing — while a context below the merge sees both it
  and the twin migration placed there, and would otherwise report one fact twice, under
  two names it knows denote one thing.  This drops the spelling that reader has retired
  and leaves the one it elected, which is what makes a count over an answer set mean
  something (docs/equality.md).

  **Gated on the closure being non-empty**, so a KB that has merged nothing — every KB
  until somebody states an equality — pays one deref for the whole query, and one that
  has pays a `contains?` per symbol of each match against a snapshot taken once here,
  before anything else runs.  The scoped-supporter memo is built behind a `delay`, since
  most matches in a KB with a handful of merges name none of the merged terms and the
  question never reaches it.  A variable or nil `view-context` is the unscoped read and
  filters nothing: it asks about the KB rather than from a vantage, exactly as the class
  reads do."
  [kb view-context matches]
  (let [merged? (tax/merged-term-pred (:taxonomy kb))]
    (if-not (and merged? (symbol? view-context) (not (sx/variable? view-context)))
      matches
      (let [visible (delay (visible-supporter-fn kb view-context))]
        (remove (fn [m] (retired-for? kb visible merged? (:sentence (nth m 2)))) matches)))))

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
  of one question share an entry, and stamped with the change clock so any mutation
  retires them (`vaelii.impl.literal-cache`).  **All three** retrieval-strategy vars are
  part of the key rather than assumed away: the set-algebra and fan-out paths must agree
  on the answer set, and so must the structural-trie and functor-extent candidate
  sources, which is what `retrieval_completeness_test` and `structural_index_test` check
  — a cache that served one path's answers to the other would be checking a result
  against itself.  With `literal-cache/*enabled*` false this is the bare call."
  [kb sentence view-context]
  (let [compute (fn [s]
                  (->> (if *hierarchical-retrieval*
                         (matches-hierarchical kb s view-context)
                         (matches-visible* kb s view-context))
                       (without-excepted kb view-context)
                       (without-retired kb view-context)))]
    (if-not lc/*enabled*
      (compute sentence)
      (let [[canonical rename] (lc/canonicalize sentence)]
        (lc/rename-matches
         rename
         (lc/lookup (:matches kb)
                    [canonical view-context
                     *hierarchical-retrieval* *arg-root-retrieval* *structural-index*]
                    #(compute canonical)))))))

;; ---- whose declarations bind a tuple ------------------------------------

(defn constraining-predicates
  "The predicates whose argument declarations of kind `kind` bind a `pred` tuple —
  `pred` itself first, then every super-predicate of it `context` can see that some
  sentence declares `kind` of.

  `(genl fatherOf parentOf)` says every `fatherOf` tuple **is** a `parentOf` tuple, and
  a tuple set only narrows going down, so `(argIsa parentOf 1 person)` constrains every
  `fatherOf` tuple exactly as it constrains every `parentOf` one.  Reading the
  declarations off the exact functor makes the refusal *door-dependent*: the same
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

  **`pred` itself is never filtered and the proper supers always are.**  Reading
  `pred`'s own declarations is the retrieval that was being made anyway; a super would
  cost a retrieval that did not exist before, so each is filtered first against the
  roster of predicates some declaration of that kind names
  (`tax/arg-declaration-props`).  That is a set membership rather than an index probe,
  which is what keeps the descension free: asked of the index it would be one
  argument-root read per super per assert, so a membership of a type ten deep in the
  hierarchy would pay ten of them, and nine of those types declare nothing.  The roster
  is global and therefore a superset of what any context can see — a predicate no
  sentence anywhere declares `kind` of cannot carry a declaration this reader would find
  — and the scoped retrieval it gates is what decides which of them actually speak here.

  Sorted, so which declaration a refusal names — and the order the entailments are drawn
  in — is a function of the vocabulary rather than of the closure's hash order."
  [kb kind pred context]
  (let [tax    (:taxonomy kb)
        supers (tax/genls tax pred context)]
    (if (<= (count supers) 1)
      [pred]
      (let [declaring (tax/props tax (tax/arg-declaration-props kind))]
        (if (empty? declaring)
          [pred]
          (into [pred] (comp (remove #(= pred %)) (filter declaring)) (sort supers)))))))

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

;; ---- rule instances --------------------------------------------------------
;; A rule's variables belong to the rule, and a chainer that threads one binding map
;; down a derivation path hands that map to every expansion on it.  So the *second* use
;; of a rule on one path meets its own first use's bindings, and the two instances are
;; forced to agree on variables that were never meant to be shared.  Renaming the clash
;; apart is what gives each instance variables of its own.

(defn form-variables
  "Every variable anywhere in `form`, as a set — `#{}` rather than `sx/symbols-where`'s
  nil, since every caller here folds the answer into something."
  [form]
  (or (sx/symbols-where sx/variable? form) #{}))

(defn- spoken-for
  "Every variable `bindings` already speaks for — the ones it binds, and the ones still
  standing unbound inside its values."
  [bindings]
  (persistent!
   (reduce-kv (fn [acc k v] (reduce conj! (conj! acc k) (form-variables v)))
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
                (into [] (filter taken) (form-variables (cons consequent antecedents))))]
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
  and `vaelii.impl.plan` pins the two literals whose position *is* operational (the
  evaluables and the recursive one).

  Antecedents are substituted **before** planning, not after, so the planner costs
  them against real values — `count-at [parentOf Tom]` is an exact count where
  `parentOf` with an unknown-but-bound first argument is only an average branch.
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

(def ^:dynamic *deferred-solver*
  "An optional **override** for how the backward chainers evaluate a deferred
  antecedent — `(fn [kb goal context] -> seq of extension binding-maps)`.  nil (the
  default) uses the prover registry through `wiring/solve-goal`; a caller may bind this to
  substitute a different evaluator (a test, a restricted registry).  See
  `solve-deferred` and docs/naf.md."
  nil)

(defn solve-deferred
  "Extension binding-maps for a deferred antecedent `g` — already substituted, so its
  inputs are ground (canonical order and the planner pin it after its binders).  Uses
  `*deferred-solver*` if a caller has bound one, else the registry.  Nothing when the
  literal is inapplicable (unbound inputs, a false test): a deferred literal that
  yields no solution simply prunes the branch, the evaluable contract
  `vaelii.impl.plan` documents.

  This lets this chainer discharge a `different` / `evaluate` / `unknown` antecedent by
  computation; matching or rule expansion alone would silently prove nothing for it,
  where `ask` honours it because the registry holds a prover for each, and forward
  chaining honours it at the antecedent join.  See docs/naf.md."
  [kb g context]
  (if-let [solve *deferred-solver*]
    (solve kb g context)
    (wiring/solve-goal kb g context)))

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
;; queued behind them into one frame, so a `:seen` grown for the expansion stayed in
;; force for those siblings too: a later conjunct repeating that goal-key was refused
;; rule expansion and answered nothing, which made `[(anc Tom ?y) (anc Tom ?z)]` empty
;; while each conjunct alone answered.  A marker behind the antecedents restores the
;; scope the expansion started from, exactly where that subtree ends — the same place,
;; and the same one-stack-entry cost, as the guard marker above.

(defn- ->scope-marker [seen] [::scope seen])
(defn- scope-marker? [g] (and (vector? g) (= ::scope (first g))))
(defn- marker-seen   [g] (second g))

;; ---- dead ends -----------------------------------------------------------

(def ^:dynamic *dead-end*
  "An optional observer of the DFS's **dead ends** — `(fn [goal depth])` — or nil, the
  default.

  A dead end is a subgoal the search could neither match nor expand: no visible
  believed fact unified with it, and no rule concluding it unified either.  It is
  reported only when the branch was not merely **cut short** — by the per-path loop
  guard or by `:max-depth` — and that distinction is the whole of what makes the
  callback worth having.  A truncated branch is a search that ran out of *budget*; a
  dead end is a search that ran out of *knowledge*, and only the second names something
  the KB could be told (`vaelii.impl.abduce`, docs/abduction.md).

  The goal handed over is already substituted under the frame's bindings, so what the
  observer sees is the literal that failed.  Its return value is ignored: this is a
  **sink, not a filter**, so an observed run and an unobserved one take byte-identical
  paths and `abduce` gets the very search `prove` runs rather than a variant of it.

  Only the DFS reports.  `backward` is lazy — its dead ends would be discovered
  whenever a consumer happened to realize the seq, and the thread binding would
  already be gone — so abduction rides `prove`, which is a loop.

  nil costs one var deref per exhausted subgoal."
  nil)

(defn- leaf-solutions
  "Extension bindings for `g` without expanding any rule — the chainer's **leaf**.

  nil `leaf-solver` reads the stored facts (`matches-visible`), which is what `prove`
  means by a leaf and the only thing it has ever meant.

  The seam exists because a rule's antecedent is not always a fact question.  A caller
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
  bindings, an empty loop guard, depth 0, and the **answer variables** — the query's own,
  which every frame below inherits unchanged.

  The basis rides the *stack* rather than the bounds map because the stack is the
  continuation: a `resume` picks up frames it did not build, and a projection recomputed
  from a budget could not know what the original question asked for.

  Exposed so `prove-within` can seed a bounded run and hand its unfinished stack back to
  `resume`.

  `est-override` costs the top conjunction by something other than the index — the same
  seam, and for the same reason, as `planned-antecedents` takes for a rule's antecedents.
  An executor whose leaf is the prover registry passes it, because a `genl` conjunct that
  a cached closure answers costs the closure's size and not the handful of stored edges
  the trie can count."
  ([kb goals context] (initial-prove-stack kb goals context nil))
  ([kb goals context est-override]
   [{:goals       (plan/order kb goals context {:est-override est-override})
     :bindings    no-bindings
     :seen        #{}
     :depth       0
     :answer-vars (form-variables (vec goals))}]))

(defn prove-from
  "The resumable core of `prove`: run the DFS from an explicit `stack` (and the
  `solutions` gathered so far) under `bounds`, a map of optional caps —

    :deadline     an absolute `System/nanoTime` instant; stop once reached
    :max-results  stop once this many solutions are in hand
    :max-depth    do not expand a rule past this rule-expansion depth
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
  continuation."
  [kb rules-fn context
   {:keys [deadline max-results max-depth leaf-solver est-override]} stack solutions]
  ;; one search scope for this *segment*: the transitive closure walked once per node
  ;; rather than once per join binding, and the resident networks held still for its
  ;; length (`observe/with-search-scope`).  The loop is eager, which is the macro's
  ;; precondition.  A segment, not a query — `prove-seq` drives the same search in
  ;; several calls, and each opens a scope of its own, which is sound because a query
  ;; writes nothing for the pin to hold still against.
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
        (let [{:keys [goals bindings seen depth answer-vars]} (peek stack)
              stack (pop stack)]
          (cond
            (empty? goals)
            (recur stack (conj solutions (project-answer bindings answer-vars)))

            ;; A guard marker: the antecedents ahead of it have all been solved, so this
            ;; is where an `exceptWhen` exception is asked of the completed binding.  It
            ;; rides the goal stack rather than being checked at the rule frame because
            ;; this chainer solves antecedents by *pushing* them — there is no other
            ;; moment at which "the argument is now complete" is observable.  A marker is
            ;; a **vector**, and a goal never is (see `core/goal-conjunction`), so the two
            ;; are told apart structurally.
            (guard-marker? (first goals))
            (recur (cond-> stack
                     ((marker-guard (first goals)) bindings)
                     (conj {:goals (rest goals) :bindings bindings :seen seen :depth depth
                            :answer-vars answer-vars}))
                   solutions)

            ;; the expanded goal's subtree ends here: the conjuncts still queued behind
            ;; it are siblings, not descendants, and answer under the scope it started in
            (scope-marker? (first goals))
            (recur (conj stack {:goals (rest goals) :bindings bindings
                                :seen (marker-seen (first goals)) :depth depth
                                :answer-vars answer-vars})
                   solutions)

            ;; A deferred goal (`different` / `evaluate` / `unknown`) is *computed* by the
            ;; registry, not matched or expanded: push one continuation frame per extension
            ;; binding, and no rule frames (see the `*deferred-solver*` section above).
            (sx/deferred-literal? (substitute (first goals) bindings))
            (let [g          (substitute (first goals) bindings)
                  rest-goals (rest goals)
                  frames     (for [b (solve-deferred kb g context)]
                               {:goals rest-goals :bindings (merge bindings b)
                                :seen seen :depth depth :answer-vars answer-vars})]
              (recur (into stack frames) solutions))

            :else
            (let [g          (substitute (first goals) bindings)
                  rest-goals (rest goals)
                  k          (goal-key g)
                  fact-frames (for [b (leaf-solutions kb g context leaf-solver)]
                                {:goals rest-goals :bindings (merge bindings b) :seen seen
                                 :depth depth :answer-vars answer-vars})
                  ;; expansion cut short rather than exhausted: the goal is re-entering
                  ;; its own derivation path, or the depth bound bit.  Either way the
                  ;; branch says nothing about what the KB is missing (see `*dead-end*`).
                  cut?        (or (contains? seen k)
                                  (boolean (and max-depth (>= depth max-depth))))
                  ;; every name already in play on this path: what the bindings speak
                  ;; for, the goal's own variables, and the conjuncts still queued — the
                  ;; last of which are outer rules' unsolved antecedents, equally
                  ;; capturable by an instance expanded under them
                  taken       (when-not cut?
                                (-> (spoken-for bindings)
                                    (into (form-variables g))
                                    (into (form-variables rest-goals))))
                  rule-frames (when-not cut?
                                (for [rule (rules-fn g)
                                      :let [{:keys [antecedents consequent guard]}
                                            (freshen-rule rule taken)
                                            b (subsuming-unify kb g consequent bindings)]
                                      :when b]
                                  {:goals    (into (-> (planned-antecedents
                                                        kb antecedents consequent context b
                                                        est-override)
                                                       (cond-> guard (conj (->guard-marker guard)))
                                                       ;; behind the guard: the scope is
                                                       ;; restored once this rule's own
                                                       ;; subtree is finished with it
                                                       (conj (->scope-marker seen)))
                                                   rest-goals)
                                   :bindings b
                                   :seen     (conj seen k)
                                   :depth    (inc depth)
                                   :answer-vars answer-vars}))]
              (when (and *dead-end* (not cut?)
                         (empty? fact-frames) (empty? rule-frames))
                (*dead-end* g depth))
              (recur (into stack (concat fact-frames rule-frames)) solutions))))))))

(defn prove
  "A simple depth-first backward chainer using loop/recur over an explicit goal
  stack.  Returns a vector of fully-resolved solution binding maps for proving the
  conjunction `goals` in `context`.  Type-aware (specificity) and context-aware
  (matches-visible); a per-path :seen set of goal-keys blocks a goal from
  re-expanding itself through recursive rules, so recursion terminates.  Prefer
  right-recursive rules — a left-recursive rule is pruned after its first
  expansion.  `rules-fn` maps a subgoal to candidate parsed rules.

  Runs to completion; `prove-from` is the bounded/resumable variant this delegates
  to (`vaelii.core/prove-within` builds the anytime contract on it), and `prove-seq`
  is the same search driven lazily."
  [kb rules-fn goals context]
  (:solutions (prove-from kb rules-fn context nil
                          (initial-prove-stack kb goals context) [])))

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
  resident values are re-read rather than pinned across the whole seq.  For a read that is
  sound — a query mutates no belief, so there is no write for a pin to hold still against.

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
