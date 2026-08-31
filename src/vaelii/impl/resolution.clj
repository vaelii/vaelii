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
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wiring :as wiring]))

;; ---- unification --------------------------------------------------------

(def no-bindings {})

;; unify and unify-var are mutually recursive (a bound variable is chased back
;; through unify), so one forward declaration is genuinely required here.
(declare unify-var excepted? excepted-anywhere?)

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
  in, so `(?pred . ?args)` with `?args=(Tom Bob)` becomes `(parentOf Tom Bob)`.

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

  Everything else keeps the trie: a fully-ground test (its leaf is exact), a pattern
  whose ground arguments are already a left prefix, and a pattern whose only
  after-a-variable selectivity is a **non-indexable** token (a number/string the
  roots do not key), where the trie's own token narrowing beats a functor-root scan.
  Zero-regression by construction — the diverted case is the one the trie answers
  with a full fan-out.

  **The decision is named before it is taken.**  The `cond` below yields one of six
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
  plain unify, so nothing changes for a KB without predicate-genl edges.

  **Under a negation the fan reverses**, because a `genl` edge carries the other way
  through one: `dog ⊑ animal` makes `(dog Muffet)` satisfy `(animal ?x)` and makes
  `(not (animal Muffet))` satisfy `(not (dog ?x))` — the contrapositive, so a negated
  antecedent is met by a negative fact on a **genl** of its body's predicate.  The two
  directions are exclusive: `(not (dog Muffet))` does not satisfy `(not (animal ?x))`,
  which is the reading a fan in the positive direction would give it.  Both sides must
  be negations for this to apply; a negation matched against a positive fact fails on
  polarity as it does anywhere else.

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
       (if (and (symbol? af) (not (sx/variable? af)) (symbol? ff) (not= af ff)
                (contains? (tax/genls (:taxonomy kb) af context) ff))
         (unify (rest a) (rest f))                    ; genl of the body: unify the arguments
         (unify antecedent fact)))

     (and (unary? antecedent) (unary? fact))
     (let [[t a]  antecedent
           [t' x] fact]
       (if (and (symbol? t) (not (sx/variable? t)))
         (when (contains? (tax/specs (:taxonomy kb) t context) t') (unify a x))
         ;; a variable functor: `specs` is reflexive, so it never holds a concrete `t'` —
         ;; unify the whole literal, functor and argument, the way the n-ary `:else` arm
         ;; already does for its own variable-functor case
         (unify antecedent fact)))

     :else
     (let [af (when (sequential? antecedent) (first antecedent))
           ff (when (sequential? fact) (first fact))]
       (if (and (symbol? af) (not (sx/variable? af)) (symbol? ff) (not= af ff)
                (contains? (tax/specs (:taxonomy kb) af context) ff))
         (unify (rest antecedent) (rest fact))        ; sub-predicate: unify the arguments
         (unify antecedent fact))))))

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
  animal` entails `¬animal ⊑ ¬dog`.  Both sides must be negations; a negated goal
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
         reach (if neg? tax/genls tax/specs)]
     (if (and (symbol? gf) (not (sx/variable? gf))
              (symbol? cf) (not (sx/variable? cf))
              (not= gf cf)
              (contains? (reach (:taxonomy kb) gf context) cf))
       (unify (rest g) (rest c) bindings)
       (unify goal consequent bindings)))))

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
  functor.  So it answers **every** rule — enumerated off the antecedent roster
  (`:rule-antecedents`) through the antecedent index, the `O(rules)` read
  `chain/rule-firing-report` takes, since every rule carries an antecedent and the
  consequent index has no roster of its own.  Paid only for a variable functor, which
  fact matching already answers through the argument roots; without it the open functor
  reached stored facts and silently no rule.

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
   (let [idx        (:index kb)
         var-conseq (set (p/rules-by-consequent idx p/var-consequent-key))]
     (cond
       (sx/variable? pred)
       (into var-conseq
             (mapcat #(p/rules-by-antecedent idx %))
             (keys @(:rule-antecedents kb)))

       (symbol? pred)
       (into var-conseq
             (mapcat #(p/rules-by-consequent idx %))
             (tax/specs (:taxonomy kb) pred context))

       :else
       (into var-conseq (p/rules-by-consequent idx pred))))))

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

(def ^:dynamic *belief-blind*
  "Read the store as **stored** rather than as believed — `CxEverything`, and nothing
  else.

  This is a named opt-out of the fourth invariant (\"a stored sentex is not a believed
  one\", README.md), which is why it is a dynamic var scoped to one read by the door that
  resolves the symbol, and not an option any caller can set.  What it buys is a
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

  Correct to hoist because the value cannot change under a path: the door binds it around
  the whole read and `blind-seq` re-establishes it per realization step, so whichever of
  those constructed this seq had it bound already."
  []
  *belief-blind*)

(defn blind-seq
  "`s`, realized under `*belief-blind*` — one element at a time, with the binding
  re-established for each.

  A plain `(binding [*belief-blind* true] (read …))` is **wrong here and silently so**,
  which is the whole reason this exists.  Every read door answers with a lazy seq, so the
  binding frame is popped the moment the door returns and long before the first element is
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
    (or *belief-blind*
        (not (jtms/known-datum? tms handle))
        (jtms/in? tms handle))))

(defn supporter-believed?
  "Is stored supporter `handle` believed and not excepted from `context`?

  Assertion-context inheritance is deliberately not answered here: taxonomy's scoped
  edge/cache readers already apply it, and genlCx declarations are forced universal.
  Keeping this callback about belief force alone also prevents context reachability
  from recursively asking itself whether its own supporters are reachable."
  [kb handle context]
  (boolean
   (and (jtms/in? (:tms kb) handle)
        ;; The whole-KB roster is the cheap gate. Only a handle targeted somewhere
        ;; pays the context-sensitive cascade walk.
        (or (not (excepted-anywhere? kb handle))
            (not (excepted? kb handle context))))))

(defn supporter-visible?
  "Is stored supporter `handle` believed, inherited, and not excepted from `context`?"
  [kb handle context]
  (boolean
   (and (supporter-believed? kb handle context)
        (when-let [sentex (p/get-sentex (:records kb) handle)]
          (tax/sees? (:taxonomy kb) context (:context sentex))))))

(defn visible-supporter-fn
  "`handle -> boolean`, memoized: is the sentex `handle` believed, inherited by
  `context`, and not hidden there by a visibility exception? nil when `context` is nil
  or a `?var` — the unscoped path, which every caller reads as *no filter* rather than
  as *nothing visible*.

  The seam a **context-scoped equality** read hangs on: the equality partition records
  its supporters as handles, and only the record store knows where each was asserted."
  [kb context]
  (when (and (symbol? context) (not (sx/variable? context)))
    (memoize #(supporter-visible? kb % context))))

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

(defn same-class-in?
  "Do `a` and `b` denote one thing as `context` sees the merges?  The context-scoped
  twin of `tax/same-class?`: two terms are one class here only when the edges that merged
  them are visible up `context`'s `genlCx` cone, so a merge behind a supporter the reader
  cannot see does not put them in one class for it.  A nil or `?var` context is unscoped
  and gives the global answer `tax/same-class?` gives — the reads share `representative-in`,
  which is one map lookup until an *invisible* edge actually splits the class."
  [kb a b context]
  (let [visible? (visible-supporter-fn kb context)]
    (= (representative-in kb visible? a)
       (representative-in kb visible? b))))

(defn- spelling-representative-in
  "`term`'s spelling-only representative as `visible?` sees the rewriteOf renames — used
  inside a quoting function's arguments, where a mention tracks a spelling rename but not
  an identity merge (`tax/spelling-representative`).  Gated by `merged?`, so an unmerged
  symbol is one map miss."
  [kb visible? term]
  (let [tax (:taxonomy kb)]
    (if (tax/merged? tax term)
      (tax/spelling-representative tax term visible?)
      term)))

(def ^:private equality-mention-heads
  "The equality relations whose **argument positions are mentions** — the names the
  sentence relates, not uses of the concept — so a `sameAs` / `equals` identity merge must
  not fold them onto a class representative.  A `rewriteOf` spelling rename still applies,
  since that renames the name itself; the args are treated exactly like a quoted position.

  Without this a stored `(not (sameAs A B))` is congruence-rewritten to the vacuous
  `(not (sameAs A A))` by the very merge it denies — superseding the real denial, so a
  monotonic denial of a default equality is silently lost (docs/equality.md).  `different`
  is not here: it is never stored and `goal-normal-form` exempts it whole at the goal.

  Mirrors `kb/equality-predicates`, which cannot be required here (`kb` requires this
  namespace); `equality_mention_test` pins the two in step."
  '#{rewriteOf sameAs equals})

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
  recursively.  The path every KB with no `quotingFunction` takes.  An equality relation's
  arguments are a mention: rewritten by spelling only, never folded onto a `sameAs`
  referent (`equality-mention-heads`)."
  [kb visible? term]
  (cond
    (sequential? term)
    (if (equality-mention-heads (first term))
      (apply list (first term) (map #(spelling-term-plain kb visible? %) (rest term)))
      (apply list (map #(representative-term-plain kb visible? %) term)))
    (symbol? term)     (if (sx/variable? term) term (representative-in kb visible? term))
    :else              term))

(defn- attitude-application?
  "Is `term` `(P agent proposition)` for a declared `modalPredicate` `P` — the shape
  `BeliefProjectionProver` projects?  Its **third** argument is what the agent holds true,
  and the shape test is the prover's own: arity 2, over a sentence-shaped proposition.  A
  `(believes A Foo)` naming a bare term is not one — that argument refers rather than
  quotes, and stays transparent."
  [modal term]
  (and (= 3 (count term))
       (contains? modal (first term))
       (sequential? (nth term 2))))

(defn- any-mention-position?
  "Does `term` contain a quoted position at all — a `quotingFunction` application, or an
  attitude?  The gate that keeps the flat reads flat: a KB granting `believes` has marks,
  but almost every sentence in it quotes nothing, and this answers that with a structural
  walk and two set lookups per compound head."
  [marks term]
  (boolean
   (when (sequential? term)
     (or (contains? (:quoting marks) (first term))
         (attitude-application? (:modal marks) term)
         (some #(any-mention-position? marks %) term)))))

(defn- representative-term-mention
  "The mention-aware walk.  Inside a **quoted position** — a `quotingFunction`'s arguments,
  or the proposition a `modalPredicate` attributes to its agent — symbols are rewritten by
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
  (`representative-in`), **recursively** — so a merged symbol nested inside a compound is
  rewritten at whatever depth it sits.

  `representative-in` alone is a flat lookup: the closure is keyed by symbol, so handing
  it a compound returns that compound unchanged and the caller silently compares
  unnormalized forms.  Every caller that may see a compound wants this one, and the
  difference is congruence — with `(sameAs Kilogram Kg)` believed, `(QuantityFn 5
  Kilogram)` and `(QuantityFn 5 Kg)` normalize to one term here and to two there.

  **Mention opacity.** Two declarations make a position a *mention* — a term named as
  syntax, rewritten by *spelling* (`rewriteOf`) only and never by a `sameAs` / `equals`
  identity merge, so a quoted term does not fold onto its referent's class.  A
  `quotingFunction` (`Quote`, `Quasiquote`) quotes its arguments; a `modalPredicate`
  (`believes`, and whatever else is granted) quotes the **proposition** it attributes,
  because an attitude is opaque: from *Oedipus believes he married Jocasta* and *Jocasta is
  his mother* it does not follow that he believes he married his mother, and the asker's
  merges are not his.  What the agent's *own* context merges does apply, and applies where
  the projection reads it (`provers/BeliefProjectionProver`).  Gated on `tax/mention-marks`: a
  KB declaring neither takes the plain walk unchanged, two prop reads at entry.

  This covers ground congruence, which is what an identity merge does.  The oriented
  equational rewriting `kb/rewrite-term*` applies after it (`rewrite/normalize-sentence`)
  is a walk over argument terms that does not read these marks, so a schematic `equals`
  normalizes inside a quoted position as it does outside one."
  [kb visible? term]
  (if-let [marks (tax/mention-marks (:taxonomy kb))]
    (representative-term-mention kb visible? marks term false)
    (representative-term-plain kb visible? term)))

(defn- displacements-plain
  "Every non-variable symbol of `sentence` mapped to its class representative when that
  differs — the `{old rep}` a plain congruence rewrite records.  Structure‑aware for one
  reason: an equality relation's arguments are a mention (spelling‑only), so a
  `sameAs`‑merged term inside a `(sameAs …)` is **not** recorded displaced — matching what
  `representative-term-plain` rewrites, so `why-not` and the supersession agree with it."
  [kb visible? sentence]
  (letfn [(walk [term spelling? acc]
            (cond
              (sequential? term)
              (if (and (not spelling?) (equality-mention-heads (first term)))
                (reduce #(walk %2 true %1) (walk (first term) false acc) (rest term))
                (reduce #(walk %2 spelling? %1) acc term))
              (and (symbol? term) (not (sx/variable? term)))
              (let [r (if spelling?
                        (spelling-representative-in kb visible? term)
                        (representative-in kb visible? term))]
                (if (not= r term) (assoc acc term r) acc))
              :else acc))]
    (walk sentence false {})))

(defn- displacements-mention
  "Mention-aware collector, the traversal `representative-term-mention` rewrites by: inside
  a quoted position — a `quotingFunction`'s arguments, or a `modalPredicate`'s proposition —
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
  "The `{old-term representative}` rewrites `sentence` undergoes under `visible?`, computed
  the way `representative-term` actually rewrites it — so a quoted mention held opaque to a
  `sameAs` is not reported displaced by `why-not`.  Gated on `tax/mention-marks`: a KB declaring
  no `quotingFunction` and no `modalPredicate` takes the flat walk unchanged."
  [kb visible? sentence]
  (if-let [marks (tax/mention-marks (:taxonomy kb))]
    (displacements-mention kb visible? marks sentence false {})
    (displacements-plain kb visible? sentence)))

(defn normal-form
  "`term` (a sentence or a term) in the **equality normal form** the KB stores and asks in:
  every symbol to its class representative (`representative-term`), then argument terms
  reduced by the oriented schematic equations visible to the same reader
  (`rewrite/normalize-sentence`).  Migration and query both go through here, so a stored
  term and a goal meet at one form.

  Both halves are belief-following and both are gated: a KB with no merges pays a
  representative lookup per symbol, one with no schematic equations skips normalization
  entirely (`tax/rewrite-rules` is empty).  `visible?` is the supporter predicate already
  built (`visible-supporter-fn`), so a caller normalizing many sentences under one reader
  builds it once; nil is the unscoped read, which asks about the KB rather than from a
  vantage.  `kb/rewrite-term` is the spelling for a caller holding a context instead."
  [kb term visible?]
  (let [sym   (representative-term kb visible? term)
        rules (cond->> (tax/rewrite-rules (:taxonomy kb))
                visible? (filterv #(visible? (:handle %))))]
    (rewrite/normalize-sentence rules sym)))

(defn goal-normal-form
  "`normal-form` for a **goal**, as `context` sees the merges, with `different` exempt —
  rewriting its arguments would map each to its class representative, so a merged pair
  would compare equal and reading class membership is the whole job of `different`.  The
  prover normalizes its own arguments instead.

  A question asked from a context is a question about what that context holds, so a merge
  it does not inherit must not rename what it asked.  `kb/rewrite-goal` is the read doors'
  spelling; `BeliefProjectionProver` calls this one directly, to put a proposition held
  opaque to the asker into the normal form of the **agent** whose belief it is."
  [kb goal context]
  (if (and (sequential? goal) (= 'different (nm/functor goal)))
    goal
    (normal-form kb goal (visible-supporter-fn kb context))))

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
;; it is truthy, so it would otherwise pass every gate here and reach `(long n)` inside
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
                       {:type     :unknown-option
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
        tms    (:tms kb)
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
        tms   (:tms kb)
        recs  (:records kb)
        blind? (belief-blind?)
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
                               (= (:truth pat) (:truth stored)))
                      (when-let [b (unify (:context pat) (:context stored)
                                          (unify (:sentence pat) (:sentence stored)))]
                        [h b stored])))))
        ;; a superset of the trie hits when an argument root is tighter than a
        ;; leading-variable fan-out; the unify above filters it to the same set
        cands (candidate-handles kb pat)]
    (keep match (hinting kb cands))))

(defn raw-match
  "Match a literal in one **literal** context — no genlCx inheritance, no subtype
  fan-out — trying **both argument orders for a symmetric predicate**.  Only
  fully-ground symmetric literals are stored sorted (see `vaelii.impl.sentex`), so the
  mirrored probe is what makes lookup order-insensitive: it retrieves `(siblingOf
  Ann Carol)` from the pattern `(siblingOf ?x Carol)` or `(siblingOf Carol ?x)`
  alike, and keeps a fact reachable even if it was asserted before its `symmetric`
  declaration.

  **Deduped by handle *and bindings*, not by handle.**  A palindrome — `(sibOf Ann
  Ann)`, or any pattern the mirror binds exactly as the direct probe did — is one
  answer, and dropping the second is the whole point.  But a pattern whose arguments
  are both variables matches one stored fact **twice, differently**: `(sibOf ?a ?b)`
  over a stored `(sibOf Rex Tib)` binds `?a Rex, ?b Tib` directly and `?a Tib, ?b Rex`
  through the mirror, and those are two answers about one handle.  Keying the dedup on
  the handle alone dropped the second, so a join led by such a literal saw one
  orientation — order-dependently, since which literal leads is a plan decision — and a
  rule that reached the fact the other way derived nothing.

  Lazy through the mirror: `lazy-cat` defers the second probe *and* the `seen` set
  that dedupes it, so a consumer answered by the direct hits never pays for either."
  [kb sentence context]
  (let [hits (match-one kb sentence context)]
    ;; the global property, matching kb-sentex's key discipline — the mirror probe
    ;; exists because storage sorted the arguments, and storage does not vary by reader
    (if (sx/symmetric-literal? sentence #(tax/has-prop? (:taxonomy kb) :symmetric %))
      (lazy-cat hits
                (let [seen (into #{} (map (fn [[h b]] [h b])) hits)]
                  (remove (fn [[h b]] (contains? seen [h b]))
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

(defn super-predicates
  "The **genl** closure of `f` from the vantage `context`: `sub-predicates` mirrored,
  and what a *negative* pattern fans over.

  A `genl` edge carries the opposite way through a negation — `dog ⊑ animal` puts
  `(dog Muffet)` under the pattern `(animal ?x)` and `(not (animal Muffet))` under the
  pattern `(not (dog ?x))` — so the negative fan walks up where the positive one walks
  down.  The up set is bounded by the hierarchy's depth where the down set is a whole
  subtree, which is why the negative fan is the cheaper of the two on a broad ontology
  and the positive one is the fan the retrieval paths are written around.  Shared by
  `match-pattern` and the rete alpha matcher for the same reason `sub-predicates` is:
  so the two cannot drift."
  [kb f context]
  (tax/genls (:taxonomy kb) f context))

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

  Three things it decides, once:

  * **A variable or absent functor pins nothing** and fans not at all — one raw match on
    the sentence as written.
  * **A negation fans its body's functor upward** (`super-predicates`), the direction a
    `genl` edge carries through a negation, and rebuilds the `not` around each member.
  * **A singleton closure is `f` itself**, since both closures are reflexive, so there is
    nothing to fan and the as-written retrieval is the whole answer.  Counted rather than
    compared against a freshly built `#{f}`; the same reading `chain/fanning-functor?`
    takes of the same set."
  [kb sentence vantage raw mapcat-fn]
  (let [neg? (sx/negation? sentence)
        body (if neg? (second sentence) sentence)
        f    (when (sequential? body) (first body))]
    (if (and (symbol? f) (not (sx/variable? f)))
      (let [fan ((if neg? super-predicates sub-predicates) kb f vantage)]
        (if (= 1 (count fan))
          (raw sentence)
          (let [rebuild (if neg?
                          (fn [f'] (list sx/not-functor (cons f' (rest body))))
                          (fn [f'] (cons f' (rest body))))]
            (mapcat-fn (fn [f'] (raw (rebuild f'))) fan))))
      (raw sentence))))

(defn match-pattern
  "Seq of [handle bindings] for stored sentexes matching `sentence` within
  `context` (default the wildcard ?ctx).  The **functor fans out over its sub-predicate
  (genl spec) closure**, so a unary type predicate is met by its subtypes
  (`(animal ?x)` ← `(dog Muffet)`) and — with predicate-genl edges — an n-ary predicate
  by its sub-predicates (`(parentOf a ?x)` ← `(fatherOf a v)`).  A functor with no
  sub-predicates has a singleton closure, so this is a no-op for it (the overwhelming
  common case — one cached set lookup, no fan).

  **A negation fans its body's functor the other way**, over `super-predicates`:
  `(not (dog ?x))` is answered by `(not (animal Muffet))`, since `dog ⊑ animal` entails
  `¬animal ⊑ ¬dog`.  The `not` itself heads nothing and has no closure of its own, so
  the fan reads inside it and rebuilds the negation around each member; each rebuilt
  pattern is retrieved by the negative key it names, exactly as the written one is.

  The fan is scoped to the genl edges visible from `vantage` — by default the
  literal context itself, and the global closure for a `?ctx` match.  The four-arity
  exists for `matches-visible*`, which matches at each ancestor context in turn but
  stands at the *view* context throughout: scoping the fan by the ancestor would
  shrink the vantage as the walk ascends, and the set-algebra twin (which filters by
  the view's cone once) would disagree."
  ([kb sentence] (match-pattern kb sentence '?ctx))
  ([kb sentence context] (match-pattern kb sentence context context))
  ([kb sentence context vantage]
   (fanned-match kb sentence vantage
                 (fn [s] (raw-match kb s context))
                 lazy-mapcat)))

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

(defn- mirror-pos [pos] (if (= pos 1) 2 1))

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

    :two   intersect the two lowest-`count-with-arg` ground columns (default)
    :all   intersect every indexable ground column
    :gated :two, but only when the leading column is a wasteful superset — its agnostic
           count exceeds `*arg-intersect-floor*`; below that a single `unify` sweep is
           cheaper than allocating an intersection set
    :off   the pre-v3 single leading column, no intersection

  Chosen by measurement (`lein bench-argindex join`); bind it to compare."
  :two)

(def ^:dynamic *arg-intersect-floor*
  "The `:gated` strategy's floor: skip the intersection when the leading (tightest)
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
    :gated (when (> (long (ffirst sorted)) *arg-intersect-floor*)
             (mapv second (take 2 sorted)))
    ;; :two — the default; bounded at two reads and one intersection
    (mapv second (take 2 sorted))))

(def ^:dynamic *lead-side*
  "For a **non-symmetric** literal with a spec closure in hand, which side of the two
  equivalent argument reads `lead-candidates` leads from — and the last cost decision in
  this namespace to lack a knob.

  A scoped literal's candidates can be read two ways, and each is a *superset*
  `matches-hierarchical`'s `pred-ok?`/`ctx-ok?`/`jtms/in?`/`unify` filters reduce to the
  identical set (like `*arg-intersect*`, a pure cost decision that must never change the
  answer):

    :scoped   one predicate-scoped bucket per sub-predicate (`[:argument-root pd pos
              term]`).  Exactly this literal's predicates, O(|specs|) index probes — the
              pre-v4 lead, and the reference `matches_hierarchical_test` forces to compare.
    :agnostic one predicate-agnostic bucket (`[:argument-slot pos term]`, every functor
              holding `term` at `pos`), narrowed to `specs` in memory.  One index probe.
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
  scoped bucket per spec — the choice `*lead-side*` gates.  `:auto` reads the count only
  here, where the branch is actually taken."
  [ix pos term specs]
  (case *lead-side*
    :scoped   false
    :agnostic true
    ;; :auto — read whichever side is smaller
    (<= (long (p/count-with-arg ix pos term)) (count specs))))

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
            scoped (fn [pd pz] (p/sentexes-with-args ix pd {pz term}))
            ;; Multi-column narrowing: with ≥2 indexable ground columns on a non-symmetric
            ;; literal, intersect them at the probe (`sentexes-with-args` folds the scoped
            ;; leaves) so `unify` sees only the conjunction, not one wide column it then
            ;; rejects the others against.  `nil` keeps the single leading column — the
            ;; belief-settle diet (`≤1` ground column) and every symmetric literal, whose
            ;; mirror matches a forward intersection would drop.  The intersection is a
            ;; subset of that leading column and a superset of the matches, so the answer
            ;; set is unchanged (`*arg-intersect*`).
            cols   (when (and (not sym?) sorted) (multi-cols sorted))]
        (cond
          (seq cols)
          (let [pt (into {} cols)]                     ; {pos term} — positions are unique
            (if (seq specs)
              (lazy-mapcat (fn [pd] (p/sentexes-with-args ix pd pt)) specs)
              ;; a variable functor has no scope: intersect the predicate-agnostic columns
              (p/sentexes-with-args ix nil pt)))

          (seq specs)
          (if sym?
            (lazy-mapcat (fn [pd] (concat (scoped pd pos) (scoped pd (mirror-pos pos)))) specs)
            ;; One scoped bucket per sub-predicate is one index probe per spec, which a
            ;; broad functor's spec closure makes O(|hierarchy|) — the dominant cost of a
            ;; cold rebuild's clash retrieval, where the queried type sits high and its
            ;; subtree is huge while the term holds a handful of memberships.  The single
            ;; predicate-agnostic bucket is then the smaller side: read it once and let the
            ;; caller narrow the functor in memory.  `matches-hierarchical` is the sole
            ;; caller and already filters every candidate by `pred-ok?` (`contains? specs`),
            ;; so the agnostic bucket is a superset it reduces to the identical answer set —
            ;; the contract this fn already advertises ("a lazy superset of the matching
            ;; handles").  Which side, and when, is `*lead-side*`.
            (if (lead-agnostic? ix pos term specs)
              (p/sentexes-with-arg ix pos term)
              (lazy-mapcat (fn [pd] (scoped pd pos)) specs)))

          ;; A variable functor names no predicate, so there is no scope to read: the
          ;; predicate-agnostic root (a union over the slot roster) is the whole
          ;; candidate set, and `unify` binds the functor per candidate.
          sym?
          (concat (p/sentexes-with-arg ix pos term)
                  (p/sentexes-with-arg ix (mirror-pos pos) term))
          :else
          (p/sentexes-with-arg ix pos term)))
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
      (let [path (cond
                   (not (some sx/indexable-term? args)) :hier-functor-extent
                   (seq specs)                          :hier-scoped-roots
                   :else                                :hier-agnostic-roots)
            _    (when prof? (prof/record-literal sentence path))
            cands (hinting kb (lead-candidates kb specs args sym?))
            ;; A candidate that can answer at all: live, fetched, and past the
            ;; predicate-hierarchy filter (the sub-predicate closure) and the
            ;; context-hierarchy filter (the genlCx up-closure), in memory.  An
            ;; exceptWhen meta-sentex is internal bookkeeping and skipped, as in
            ;; `match-one` (the one non-ground stored Literal).  Both branches below
            ;; admit a candidate exactly here, and differ only in how many answers one
            ;; admitted record may yield.
            blind? (belief-blind?)
            admit (fn [h]
                    (when (or blind? (jtms/in? (:tms kb) h))
                      (when-let [stored (p/get-sentex (:records kb) h)]
                        (when (and (not (sx/exceptWhen-meta? (:sentence stored)))
                                   (pred-ok? (some-> (sx/body stored) first))
                                   (ctx-ok? (:context stored)))
                          stored))))
            ;; the unify attempt in one argument order.  Concrete view: bind no ?ctx
            ;; (match at the fact's own context, which is in the up-closure); variable
            ;; view: bind ?ctx, exactly as match-one does.
            order (fn [stored rev?]
                    (let [pat (pat-for (some-> (sx/body stored) first)
                                       (if up? (:context stored) '?ctx)
                                       rev?)]
                      (when (= (:truth pat) (:truth stored))
                        (unify (:context pat) (:context stored)
                               (unify (:sentence pat) (:sentence stored))))))
            out
            (if-not sym?
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
                          (when-let [b (order stored false)]
                            (vswap! seen conj h)
                            [h b stored]))))
                    cands)
              ;; A symmetric sub-predicate, so one candidate really can answer twice —
              ;; an all-variable pattern binds a stored `(sibOf Rex Tib)` both ways
              ;; round — and the dedup keys on `[handle bindings]`, which leaves no
              ;; handle-keyed early exit to skip the fetch with.  That pairing is what
              ;; makes the two retrieval paths return one set (`raw-match` says why the
              ;; pair is the honest key).
              (lazy-mapcat
               (fn [h]
                 (when-let [stored (admit h)]
                   (when prof? (vswap! unifs inc))
                   (let [;; both orders, not the first that answers: a pattern with two
                         ;; variable arguments binds one stored fact twice and
                         ;; differently, and those are two answers about one handle.  A
                         ;; palindrome, or any pattern the mirror binds as the direct
                         ;; order did, is one — the `not=` is what keeps it one.
                         b0 (order stored false)
                         b1 (when (contains? sym-preds (some-> (sx/body stored) first))
                              (order stored true))
                         bs (cond-> []
                              b0                     (conj b0)
                              (and b1 (not= b1 b0))  (conj b1))]
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

(defn- except-in-force?
  "Is except-handle `eh` believed **and** not itself hidden by a cascading meta-except?
  Recursive with a `seen` set as cycle guard (unreachable with well-formed input, since
  stratification forbids the cycle, but defensive).

  The cascade semantics: `(except H)` hides H.  `(except E)` where E is the except that
  hides H suppresses E's effect, restoring H.  `(except M)` where M is the meta-except
  suppresses M, restoring E's effect, re-hiding H — and so on, toggling at each depth."
  [tms target->ehs eh seen]
  (and (jtms/in? tms eh)
       (if (contains? seen eh)
         false
         (let [meta-ehs (get target->ehs eh)]
           (if meta-ehs
             ;; eh is itself a target; active only if none of its meta-excepts are active
             (not (some #(except-in-force? tms target->ehs % (conj seen eh)) meta-ehs))
             ;; eh is not a target; it is active
             true)))))

(defn- visible-exception-index
  "The exception roster visible from `view-context`, flattened to
  `{target-handle -> #{except-handle ...}}`, or nil when the ordinary no-exception
  fast path applies.  Both the hot boolean reads and diagnostic exception forest use
  this one index so they cannot disagree about scope."
  [kb view-context]
  (let [by-ctx @(:excepted kb)]
    (when-not (or (empty? by-ctx) (sx/variable? view-context))
      (let [up (tax/context-up-global (:taxonomy kb) view-context)]
        (not-empty
         (reduce-kv
          (fn [m ctx entries]
            (if-not (contains? up ctx)
              m
              (reduce-kv (fn [m2 target ehs]
                           (update m2 target (fnil into #{}) ehs))
                         m entries)))
          {} by-ctx))))))

(defn- exception-states
  "Evaluate the cascade once for every exception reachable from `roots`.

  Returns `{handle {:in? bool :in-force? bool}}`.  Memoization keeps a linear chain
  linear instead of re-walking every suffix while rendering the diagnostic forest.
  `seen` retains the defensive cycle answer; valid graphs are stratified."
  [tms target->ehs roots]
  (let [states (atom {})]
    (letfn [(active? [eh seen]
              (if (contains? seen eh)
                false
                (if-some [state (get @states eh)]
                  (:in-force? state)
                  (let [in? (boolean (jtms/in? tms eh))
                        ;; Eagerly evaluate every child: `not-any?` directly over the
                        ;; recursive calls would short-circuit after one active child,
                        ;; leaving its siblings absent from the diagnostic state map.
                        child-active (mapv #(active? % (conj seen eh))
                                           (get target->ehs eh))
                        active (boolean (and in? (not-any? true? child-active)))]
                    (swap! states assoc eh {:in? in? :in-force? active})
                    active))))]
      (doseq [eh roots] (active? eh #{}))
      @states)))

(defn- exception-node
  "One deterministic diagnostic node in the exception forest.  `seen` is only the
  defensive cycle witness; valid exception graphs are stratified and never take it."
  [records states target->ehs eh seen]
  (if (contains? seen eh)
    {:handle eh :in? (get-in states [eh :in?] false) :in-force? false
     :cycle? true :excepted-by []}
    (let [seen' (conj seen eh)
          {:keys [in? in-force?]} (get states eh)]
      {:handle eh
       :in? in?
       :in-force? in-force?
       :excepted-by (mapv #(exception-node records states target->ehs % seen')
                          (nm/sort-by-content-key
                           (fn [h]
                             (let [s (p/get-sentex records h)]
                               [(:context s) (:sentence s)]))
                           (get target->ehs eh)))})))

(defn exception-status
  "Diagnostic exception forest for `handle` from `view-context`.

  Returns `{:exceptions [...] :excepted? bool}`.  Roots are every visible exception
  directly targeting `handle`, ordered by assertion context and content; nested
  meta-exceptions live under `:excepted-by`."
  [kb handle view-context]
  (if-let [target->ehs (visible-exception-index kb view-context)]
    (let [records (:records kb)
          tms (:tms kb)
          ordered-roots (nm/sort-by-content-key
                         (fn [h]
                           (let [s (p/get-sentex records h)]
                             [(:context s) (:sentence s)]))
                         (get target->ehs handle))
          states (exception-states tms target->ehs ordered-roots)
          roots (mapv #(exception-node records states target->ehs % #{}) ordered-roots)]
      {:exceptions roots
       :excepted? (boolean (some :in-force? roots))})
    {:exceptions [] :excepted? false}))

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
  except in a visible one.  No record is fetched per except in the KB and no target is
  re-derived from a sentence: that read runs per placement and per candidate
  justification on a chaining run, which at 1,000 excepts is 89% of the run's wall clock
  (`lein bench-hotreads`).

  **Meta-exception cascade.**  An except whose handle is itself hidden by another
  believed except does not suppress its target — the cascade is evaluated at read time by
  `except-in-force?`, which walks the roster's own entries rather than the index.
  Most KBs store zero meta-exceptions, so the cascade adds no cost to the common path.

  **The O(1) gate is the empty roster**, which is both cheaper and tighter than a
  functor-root count: a KB storing only `(not (except H))` roots under
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
  (if-let [target->ehs (visible-exception-index kb view-context)]
    (let [tms (:tms kb)
          has-meta? (pos? @(:meta-except-count kb))]
      (persistent!
       (reduce-kv (fn [acc target ehs]
                    (if (if has-meta?
                          (some #(except-in-force? tms target->ehs % #{}) ehs)
                          (some #(jtms/in? tms %) ehs))
                      (conj! acc target)
                      acc))
                  (transient #{})
                  target->ehs)))
    #{}))

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
  set is kept for the caller that genuinely wants every hidden handle.

  A cone that stores a **meta-exception** is the one exception: the cascade resolves an
  except to its own targets anywhere in the cone, so there the predicate flattens the
  visible roster once (`target->ehs`, one pass over every except in the cone).  Gated on
  `:meta-except-count`, so the common no-meta read never builds it and stays O(what it
  returns)."
  [kb view-context]
  (let [by-ctx @(:excepted kb)]
    (when-not (or (empty? by-ctx) (sx/variable? view-context))
      (let [up   (tax/context-up-global (:taxonomy kb) view-context)
            ;; only the contexts that both state an except and are visible from here —
            ;; computed once, so the predicate walks nothing it will always reject
            live (into [] (comp (filter #(contains? up (key %))) (map val)) by-ctx)
            tms  (:tms kb)]
        (when (seq live)
          (if (pos? @(:meta-except-count kb))
            ;; Meta-exceptions present: the cascade (`except-in-force?`) resolves an
            ;; except-handle to *its own* targets anywhere in the cone, so it needs the
            ;; whole roster in one map.  Flatten it once, here — O(excepts in the cone) —
            ;; and pay it only on the KB that actually stores a meta-except, which is
            ;; almost none.
            (let [target->ehs (reduce (fn [m entries]
                                        (reduce-kv (fn [m2 target ehs]
                                                     (update m2 target (fnil into #{}) ehs))
                                                   m entries))
                                      {} live)]
              (fn [handle]
                (boolean
                 (when-let [ehs (get target->ehs handle)]
                   (some #(except-in-force? tms target->ehs % #{}) ehs)))))
            ;; The common case — no meta-exception, so a believed except is in force.
            ;; Ask the handle of each live context's own map directly, without flattening:
            ;; the work is one lookup per context that states an except, bounded by the
            ;; question, not by how many handles the cone hides.  This is what keeps a
            ;; scoped read O(what it returns) rather than O(what the KB hides).
            (fn [handle]
              (boolean
               (some (fn [entries]
                       (when-let [ehs (get entries handle)]
                         (some #(jtms/in? tms %) ehs)))
                     live)))))))))

(defn excepted?
  "Is the sentex at `handle` hidden from `view-context` by a believed `except`?  The
  one-shot form of `hidden-fn`, for a caller with a single handle to ask about."
  [kb handle view-context]
  (boolean (when-let [hidden? (hidden-fn kb view-context)] (hidden? handle))))

(defn excepted-anywhere?
  "Is `handle` hidden from at least one context by a believed visibility `except`?

  This is the unscoped belief-transition question used by the derived-cache
  reconcile. The roster is keyed by the contexts that state exceptions, and a
  context always sees itself, so those keys are a complete set of witnesses.
  `excepted?` still performs the meta-exception cascade, so an except suppressed in
  its own context does not count here."
  [kb handle]
  (boolean (some #(excepted? kb handle %) (keys @(:excepted kb)))))

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
  `[handle a b]` triples with no sentex at index 2, so it filters with this directly.

  **A sentence that quotes takes the mention-aware read instead.**  Inside a quoted
  position — a `quotingFunction`'s arguments, or the proposition an attitude attributes to
  its agent — a symbol is retired by a *spelling* rename and not by a `sameAs` / `equals`
  identity merge, which makes the flat per-symbol shortcut unsound there and would retire a
  belief nobody renamed.  Whether the sentence quotes at all is asked first
  (`any-mention-position?`), so an ordinary sentence in a KB that merely grants `believes`
  keeps the flat read."
  [kb visible merged? sentence]
  (let [marks (tax/mention-marks (:taxonomy kb))]
    (if (and marks (any-mention-position? marks sentence))
      (not= (representative-term-mention kb @visible marks sentence false) sentence)
      (sx/some-symbol? (fn [t]
                         (and (merged? t) (not (sx/variable? t))
                              (not= t (representative-in kb @visible t))))
                       sentence))))

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

(defn- visible-matches
  "The retrieval both of `matches-visible`'s arities perform: the chosen path, then the
  two visibility filters.  One definition, so a cached and an uncached read cannot come
  to answer differently."
  [kb sentence view-context]
  (->> (if *hierarchical-retrieval*
         (matches-hierarchical kb sentence view-context)
         (matches-visible* kb sentence view-context))
       (without-excepted kb view-context)
       (without-retired kb view-context)))

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
  against itself.  With `literal-cache/*enabled*` false this is the bare call.

  `*belief-blind*` is in the key for the same reason and a sharper one: a `CxEverything`
  read and an ordinary one ask the *same literal at the same context* and must not answer
  each other.  Left off, the first read of a pair fills the entry and the second is served
  it — so a blind read would hide a defeated default it was asked for, or an ordinary one
  would report a default it must not, whichever happened to run first.

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
        rename
        (lc/lookup (:matches kb)
                   [canonical view-context
                    *hierarchical-retrieval* *arg-root-retrieval* *structural-index*
                    *belief-blind*]
                   #(visible-matches kb canonical view-context)))))))

;; ---- whose declarations bind a tuple ------------------------------------

(defn constraining-predicates
  "The predicates whose argument declarations of kind `kind` bind a `pred` tuple —
  `pred` itself first, then every super-predicate of it `context` can see that some
  sentence declares `kind` of.

  `(genl fatherOf parentOf)` says every `fatherOf` tuple **is** a `parentOf` tuple, and
  a tuple set only narrows going down, so `(arg parentOf 1 person)` constrains every
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
  "What the backward chainers filter a rule-expanded answer against: `{:by-sentence
  {sentence #{context}} :functors #{functor}}` over the datums the JTMS currently holds
  **defeated** — or **nil** when nothing is defeated.

  Nil is the gate every caller reads, and it is the common case: a KB with no
  contradiction pays one set deref per query and nothing else.  `:functors` is the second
  gate, and the one that keeps the cost off a KB that *has* a defeat somewhere: a goal
  whose functor no defeated datum carries can produce no defeated answer, so it is never
  checked.

  Built once per query rather than asked per answer.  The defeated set is a *derived*
  state recomputed each settle (`vaelii.impl.jtms`), and a query writes nothing, so it
  cannot move underneath the search that read it."
  [kb]
  (let [ds (jtms/defeated (:tms kb))]
    (when (seq ds)
      (reduce (fn [idx h]
                (if-let [sx (p/get-sentex (:records kb) h)]
                  (-> idx
                      (update-in [:by-sentence (:sentence sx)] (fnil conj #{}) (:context sx))
                      (update :functors conj (nm/functor (:sentence sx))))
                  idx))
              {:by-sentence {} :functors #{}}
              ds))))

(defn defeatable-goal?
  "Could an answer to `goal` be one belief has already defeated — is its functor one some
  defeated datum carries?  False for every goal when `idx` is nil.

  The push-time gate: a chainer that answers false here adds no check to the goal at all,
  so a KB with no defeat on that predicate runs the search it always ran."
  [idx goal]
  (boolean (and idx (contains? (:functors idx) (nm/functor goal)))))

(defn defeated-answer?
  "Is `sentence` — an answer a rule expansion produced — a stored sentex the JTMS holds
  defeated and `context` can see?

  Canonicalized against the KB before the lookup (`kb-sentex`), since the answer is built
  from a goal and its bindings while the defeated set holds stored sentences: a symmetric
  literal's arguments are sorted in one and not the other, and comparing them raw would
  miss the very answer being filtered.

  **Visible from the query's context**, because a defeat is a claim about a stored sentex
  and a reader that cannot see that sentex is not the reader it was decided for.  An
  unscoped read (a nil or variable context) sees every context, so any defeat counts —
  the same reading `matches-visible` gives the wildcard."
  [kb idx sentence context]
  (boolean
   (when idx
     (when-let [ctxs (get (:by-sentence idx) (:sentence (kb-sentex kb sentence context)))]
       (if (or (nil? context) (sx/variable? context))
         true
         (boolean (some #(tax/sees? (:taxonomy kb) context %) ctxs)))))))

;; ---- dead ends -----------------------------------------------------------

(def ^:dynamic *dead-end*
  "An optional observer of the DFS's **dead ends** — `(fn [goal depth])` — or nil, the
  default.

  A dead end is a subgoal the search could neither match nor expand: no visible
  believed fact unified with it, and no rule concluding it unified either.  It is
  reported only when the branch was not merely **cut short** — by the per-path loop
  guard, by `:max-depth`, or by the term-growth ceiling
  (`default-max-term-growth`) — and that distinction is the whole of what makes the
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

  nil costs one var deref per expanded goal."
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
     :answer-vars (form-variables (vec goals))
     :term-base   (reduce (fn [d g] (max (long d) (long (term-depth g)))) 0 goals)}]))

(defn prove-from
  "The resumable core of `prove`: run the DFS from an explicit `stack` (and the
  `solutions` gathered so far) under `bounds`, a map of optional caps —

    :deadline     an absolute `System/nanoTime` instant; stop once reached
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
  continuation."
  [kb rules-fn context
   {:keys [deadline max-results max-depth max-term-growth leaf-solver est-override]}
   stack solutions]
  ;; one search scope for this *segment*: the transitive closure walked once per node
  ;; rather than once per join binding, and the resident networks held still for its
  ;; length (`observe/with-search-scope`).  The loop is eager, which is the macro's
  ;; precondition.  A segment, not a query — `prove-seq` drives the same search in
  ;; several calls, and each opens a scope of its own, which is sound because a query
  ;; writes nothing for the pin to hold still against.
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
          (let [{:keys [goals bindings seen depth answer-vars term-base]} (peek stack)
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
              ;; a **vector**, and a goal never is (see `core/goal-conjunction`), so the two
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
              ;; binding, and no rule frames (see the `*deferred-solver*` section above).
              (sx/deferred-literal? (substitute (first goals) bindings))
              (let [g          (substitute (first goals) bindings)
                    rest-goals (rest goals)
                    frames     (for [b (solve-deferred kb g context)]
                                 {:goals rest-goals :bindings (merge bindings b)
                                  :seen seen :depth depth :answer-vars answer-vars
                                  :term-base term-base})]
                (recur (into stack frames) solutions))

              :else
              (let [g          (substitute (first goals) bindings)
                    rest-goals (rest goals)
                    k          (goal-key g)
                    ;; a leaf match may hand the conjuncts behind it a deep *stored* term,
                    ;; and nothing about that is a rule growing one — so the basis rises
                    ;; with it (`grown-term-base`), and only a rule's own nesting is
                    ;; measured against the allowance
                    fact-frames (for [b (leaf-solutions kb g context leaf-solver)]
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
                                      (into (form-variables g))
                                      (into (form-variables rest-goals))))
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
                (recur (into stack (concat fact-frames rule-frames)) solutions)))))))))

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
