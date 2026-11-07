;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.provers
  "Pluggable provers for the query engine.  A prover answers a goal and declares
  how it expects to perform, so the engine can choose among applicable provers:

    applicable?   can it answer this goal at all?
    est-bindings  ~how many solution bindings it will produce
    cost          a qualitative first-answer cost tier (see `cost-tiers`)
    completeness  0..100 — see the contract below
    solve         the solutions, as raw binding maps

  `ask` runs the cheapest *complete* prover alone (fewest `est-bindings`);
  otherwise it unions the applicable provers cheapest first by `cost` tier.
  Built-in provers: transitivity (genl/genlCx,
  complete via the cached closures), disjointness (complete), `minCommonGenl` and
  `maxCommonSpec` (complete, read off the same closures), `different` (the
  unique-name assumption read off the equality closure — ground only, see
  docs/equality.md), facts (the index), and rules (backward chaining through the same
  engine).

  ## What completeness 100 claims

  **For this goal shape, my answers are a superset of what every other prover reading
  the same sources would answer.**  That is the reading that licenses running alone,
  and it is a claim a prover is competent to make about itself.

  One alternative to avoid — *nothing else can answer this goal* — is a claim about a
  predicate, and it stops being true the moment a KB adds a second way to reach that
  predicate.  Whether such a way exists is not a question any one prover can answer,
  because it is about the sources it does **not** read.  So the engine asks it, once
  per goal, in `sole-prover`: a claimant runs alone only when `shadowing-channels` is
  empty.  A prover therefore declares a constant and reasons only about its own
  sources, and a prover registered through `add-prover` is guarded without its author
  knowing the mechanism exists.

  A computed prover normally earns the claim it makes: the closure provers are built
  out of the very facts `FactProver` would return and out of the derivations a rule
  contributes, and a calculus reads both into its network — converse and composition
  included — before entailing anything.

  ## Why a prover is not a predicate's property

  Nothing here is declared per predicate, and the registry is deliberately unreachable
  from `vaelii.impl.predicates` — which holds what is *said* about each term of the
  engine's grammar, and holds nothing about who answers a goal.  It is the completeness
  argument above, one level down: a claim about *a predicate* is not a claim any single
  component is competent to make.  Three reasons, and they are why binding provers to
  predicates in the declaration is the wrong shape rather than the missing half.

  * **`applicable?` reads a goal's shape, not a predicate's name.**  `EvaluableProver`
    reads the arguments in front of it; `QuantityProver` reads a unit table first;
    `ArgTypeProver` answers a goal on any predicate carrying a declared argument type.
    None of the three is \"predicate P is answered by prover X\", so none of them has an
    entry to write.
  * **`add-prover` is public API**, and it registers a prover with no declaration entry
    at all.  Nine ship in-tree opt-in — `space`, `interval`, `stp`, `duration`, `sign`,
    `orientation`, `relative`, `calendar`, `distance`, each documenting its own
    registration — and third-party ones are the point of the extension.  A framework
    requiring an entry either breaks those or grows an escape hatch that makes the entry
    advisory, and an advisory entry is a hand-kept list again: the thing `predicates` exists to
    stop being.
  * **`sole-prover` already answers the coordination question** a per-predicate binding
    would be reaching for, and answers it better.  A prover declares a constant about its
    own sources, and the engine asks once per goal whether anything shadows it.  That is
    a question about the KB, which moves when the KB does, rather than about the
    vocabulary, which does not.

  What the *declaration* carries is narrower, and is a fact about the declaration rather
  than about any prover: the `:answers` facet, meaning this term's arrival moves what a
  level-6 query says about some predicate — which is what obliges it to post an exception
  re-check, by its own arms or through `special/declaration-subjects`
  (`predicates/check-facets`).  That is the line the four functor lists in this file sit
  on either side of, and it is the same line each time: a prover's **shape** table stays
  with the prover, and its **enrolment** is the declaration's."
  (:require [clojure.string :as str]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.datetime :as datetime]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.except :as exc]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types
             :refer [Prover SupportingProver applicable? completeness cost
                     est-bindings solve solve-with-support support-functors
                     support-sources]]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

(def cost-tiers
  "First-answer cost tiers, cheapest first: is the answer something you look up, compute, or
  search for?  Qualitative, not milliseconds.

  - `:lookup`: a bounded single-step retrieval (an O(1) ground test, a cached closure or
    metadata read, or one index hit).
  - `:compute`: a fixpoint over stored facts before the first answer (a closure).
  - `:search`: recursive backward chaining.

  `cost-rank` gives the ordinal.  The union path orders applicable provers by it, and
  `budget`'s `:max-cost` uses it as a ceiling.  No registry member expands a rule, so `:search`
  is unoccupied and `:max-cost :compute` and `:search` select the same provers; `add-prover`
  can supply a searching one.  Rule expansion is bounded by `core/query`'s `:max-depth`."
  [:lookup :compute :search])

(def cost-rank (into {} (map-indexed (fn [i t] [t i])) cost-tiers))

;; Several records reach the engine that dispatches them, and the engine is assembled
;; below the records it holds — so the knot is closed with one forward declaration.
;; `unknown` / `thereExists` / an aggregate run their argument back through
;; `solve-goal-with` over the whole `registry`; `parse-rule` builds the `exceptWhen`
;; guard that a rule read carries; `solve-inverted` composes the metadata provers minus
;; itself.
(declare parse-rule solve-inverted solve-mirrored registry solve-goal-with est-goal)

(defn- pvar? [x] (sx/variable? x))
(def ^:private ground? sx/ground-term?)
(defn- binary? [goal] (and (sequential? goal) (= 2 (count (rest goal)))))
(defn- binary-pred? [goal p] (and (binary? goal) (= p (first goal))))

;; ---- what can shadow a computed answer ----------------------------------

(defn- concludes-goal?
  "Does a stored rule, in any context, conclude something `goal` unifies with?  The
  candidates are `res/concluding-rule-handles` (the goal's predicate or a spec of it),
  behind `res/concludes?`'s index-only answer, and the match is `res/subsuming-unify`, the
  test the backward chainer applies before it expands a rule.  A goal whose predicate
  some rule concludes, but at arguments the goal's cannot unify with, is concluded by
  no rule."
  [kb goal context]
  (let [pred (nm/functor goal)]
    (and (res/concludes? kb pred context)
         (let [taken (set (sx/form-variables goal))]
           (boolean
            (some (fn [h]
                    (when-let [c (:consequent (p/get-sentex (:records kb) h))]
                      (res/subsuming-unify
                       kb goal (:consequent (res/freshen-rule {:consequent c :antecedents []} taken))
                       res/no-bindings context)))
                  (res/concluding-rule-handles kb pred context)))))))

(defn- unread-inverse?
  "Is some predicate `tax/inverses-under` declares inverse to `pred` a source the
  calculus owning `pred` does not read?  A partner `q` is read when
  `qkb/converse-entailed?` holds of it, and with no registered calculus owning `pred`,
  every partner is unread."
  [kb pred context]
  (when-let [qs (seq (tax/inverses-under (reasoning/taxonomy kb) pred context))]
    (let [calc (qkb/calculus-for kb pred)]
      (not (and calc (every? #(qkb/converse-entailed? calc pred %) qs))))))

(defn shadowing-channels
  "The ways this KB could reach `goal` that a **computed** prover does not read: the set a
  conditionally-complete prover checks before claiming its answers are a superset of everyone
  else's (the completeness contract at the head of this file).  Each channel is found by
  differencing the complete prover against every other applicable prover.

  - `:preserving`: an `(transitiveInArg P n R)` declaration licenses a claim about a tuple in
    no stored fact, rule conclusion or constraint network.
  - `:rules`: a rule whose consequent unifies with the goal (`concludes-goal?`).  A
    `set/backwardRule` never fires forward and no registry member is one, so the claim must
    be read in the scope that reaches the rule.  Not narrowed to backward rules: a forward
    rule is absorbed only if the fixpoint ran to it (`{:chain? false}`, `:max-depth`).
  - `:inverse`: a declared `(inverse P Q)` for a goal about `P`, unless the calculus owning
    `P` owns `Q` and its converse table implies the pair (`unread-inverse?`).
  - `:negates`: a `(not (Q …))` goal with `Q` at or below a side of a `negates` declaration
    (`NegatesProver`).
  - `:calendar`: an argument, of the goal or of the literal it negates, that is a calendar
    term (`(YearFn 2000)`, `DatetimeFn`, `InstantFn`), which carries its ordering in its
    fields (`vaelii.impl.calendar`).  A pure test on the arguments.

  Absorbed, so not a channel: a stored fact, a merged term (rewritten into the goal first),
  `symmetric` / `transitive` / `reflexive` over a calculus's own predicate, and `arg` type
  inference and the metadata provers, which answer shapes no computed prover claims.

  Cost: `inherit/positions` is behind a root-intersection presence check, `tax/inverses-under`
  and `tax/negates-over` are one map read each, and `datetime/time-term?` reads the goal's
  arguments.  `res/concludes?` probes the consequent index per member of `pred`'s spec closure
  (O(specs) for a goal no rule concludes), and `concludes-goal?` then fetches concluding rules
  until one unifies.  `cond->` evaluates every test."
  [kb goal context]
  (when (sequential? goal)
    (let [pred (nm/functor goal)]
      (cond-> #{}
        (seq (inherit/positions kb pred context))            (conj :preserving)
        (concludes-goal? kb goal context)                   (conj :rules)
        (unread-inverse? kb pred context)                    (conj :inverse)
        (and (= sx/not-functor pred) (sequential? (second goal))
             (seq (tax/negates-over (reasoning/taxonomy kb) (first (second goal)) context)))
        (conj :negates)
        (some datetime/time-term? (nm/args (cond-> goal (sx/negation? goal) second))) (conj :calendar)))))

(defn sole-prover
  "The prover that may answer `goal` **alone**, or nil for the union path.

  A prover claims `completeness` 100 for its goal shape, subsuming every prover whose sources
  it reads.  The engine then asks whether a source none of them reads exists
  (`shadowing-channels`); if so, nobody runs alone.  The guard lives here and not in each
  prover, so a new channel is one edit and `add-prover` registrants are guarded.  Guarding
  only moves a goal from one prover to the union, which includes the claimant, so every
  claimant is asked alike, including unstorable goal shapes (`different`, `unknown`,
  `thereExists`, `forall`, aggregates).

  The channels are read once per goal and only for a goal some prover claims.  Each claimant's
  estimate is taken once and carried, because `sort-by` re-evaluates its keyfn per comparison;
  the sort is stable, so ties break on registry order.  See docs/inference.md."
  [kb applicable goal context]
  (let [claimants (filterv #(>= (budget/checked-call
                                 (fn [] (completeness % kb goal context)))
                                100)
                           applicable)]
    (when (and (seq claimants)
               (empty? (budget/checked-call
                        (fn [] (shadowing-channels kb goal context)))))
      (->> claimants
           (map (juxt identity #(budget/checked-call
                                 (fn [] (est-bindings % kb goal context)))))
           (sort-by second)
           ffirst))))

;; ---- facts (the index) --------------------------------------------------

(defn- est-by-functor
  "Estimated bindings for a goal: how many stored facts share its functor.  Read from
  the predicate extent, which counts either polarity and any arity — the trie's
  `count-at [pred]` sees only positive facts, since a negative one keys under
  `:false` and would estimate 0."
  [kb goal]
  (if (sequential? goal) (reads/stored-count-with-functor (:index kb) (first goal)) 1))

(defrecord FactProver []
  Prover
  (applicable?  [_ _ _ _] true)
  (est-bindings [_ kb goal _] (est-by-functor kb goal))
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 50)                     ; rules may derive more
  ;; `map`, not `mapv`: matches-visible is lazy all the way down to the store, so a
  ;; caller taking one solution pays for one record fetch.  Every solve below is
  ;; lazy for the same reason.
  (solve           [_ kb goal context] (map second (res/matches-visible kb goal context))))

;; ---- transitivity (genl / genlCx via the cached closures) ---------------

(def transitive-predicates
  "The relations the cached-closure `TransitivityProver` answers — genl / genlCx, held
  out of the generic per-predicate transitive machinery.  Defined once in the taxonomy.

  Not enrolled in the declaration, because it already is: `tax/closure-relations` is the
  entries whose `:storage` is `[:edge …]`, and `predicates_test` asserts the two equal.  An
  alias where the prover reads it, over a second enumeration to keep in step."
  tax/closure-relations)

(defn- trans-fns [kb pred context]
  (let [tx (reasoning/taxonomy kb)]
    (if (= pred 'genl)
      ;; genl answers from the asking context's vantage; the genlCx closures
      ;; are deliberately global — visibility scoped by visibility is circular
      {:up #(tax/genls tx % context) :down #(tax/specs tx % context) :all (tax/types tx)}
      {:up #(tax/context-up tx %) :down #(tax/context-down tx %) :all (tax/contexts tx)})))

(defrecord TransitivityProver []
  Prover
  (applicable? [_ _ goal _]
    (and (binary? goal) (contains? transitive-predicates (first goal))))
  ;; est-bindings reads the same scoped closures solve answers from, or the planner
  ;; would size a fan the solver never yields
  (est-bindings [_ kb goal context]
    (let [[pred a b] goal {:keys [up down all]} (trans-fns kb pred context)]
      (cond (and (ground? a) (ground? b)) 1
            (ground? a) (count (up a))
            (ground? b) (count (down b))
            :else (count all))))
  (cost         [_ _ _ _] :lookup)
  ;; The closure is authoritative over the sources it reads: it is *built* from the
  ;; stored edges, and a derived one reaches it through the derivation path.  A source
  ;; it does not read is `sole-prover`'s question, not this one's.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [[pred a b] goal {:keys [up down all]} (trans-fns kb pred context)]
      (cond
        (and (ground? a) (ground? b)) (if (contains? (up a) b) [{}] [])
        (ground? a) (map (fn [s] {b s}) (up a))      ; a's supertypes/ancestors
        (ground? b) (map (fn [s] {a s}) (down b))    ; b's subtypes/descendants
        ;; One variable in **both** places — `(genl ?x ?x)` — asks which members the
        ;; closure holds of themselves, and binds one variable rather than two.  Stated
        ;; rather than left to fall through: `{a x b y}` with two equal keys throws
        ;; `IllegalArgumentException: Duplicate key` out of a prover and past `ask`
        ;; untyped.  The cached closures are **reflexive** (`genls t` includes `t`), so
        ;; the answer is every node the relation holds at all — the `:when` follows the
        ;; closure rather than asserting a reflexivity of its own.
        (= a b) (for [x all :when (contains? (up x) x)] {a x})
        :else (for [x all, y (up x)] {a x b y})))))

;; ---- disjointness -------------------------------------------------------

;; An open disjointness goal is answered from the declarations, not the vocabulary.  A
;; `(disjoint x y)` declaration convicts `specs(x) × specs(y)` (`tax/separating-partners`,
;; `tax/separating-pairs`), so what is fed to `tax/disjoint?`, which still decides the ground
;; goal, is bounded by the declaration set and not the type count (docs/taxonomy.md).
;; `distinct` because two declarations can convict one type.

(defn- disjoint-with
  "The types disjoint from `a` in `context`: every subtype of a type a visible
  declaration separates `a` from.  Lazy past the partner set, which is bounded by the
  declarations that name a supertype of `a`."
  [tx a context]
  (distinct (mapcat #(tax/specs tx % context) (tax/separating-partners tx a context))))

(defn- disjoint-cross
  "`[x y]` for every pair of types a visible declaration separates — the two-variable
  goal, as the union of `specs × specs` over the separating pairs."
  [tx context]
  (distinct (mapcat (fn [[x y]]
                      (for [u (tax/specs tx x context), v (tax/specs tx y context)] [u v]))
                    (tax/separating-pairs tx context))))

(defn- self-disjoint
  "The types disjoint from **themselves** — a type below both sides of one separation,
  so it can have no instances.  The `(disjoint ?x ?x)` answer."
  [tx context]
  (distinct (mapcat (fn [[x y]]
                      (let [below (tax/specs tx y context)]
                        (filter below (tax/specs tx x context))))
                    (tax/separating-pairs tx context))))

(defrecord DisjointnessProver []
  Prover
  (applicable? [_ _ goal _] (binary-pred? goal 'disjoint))
  ;; Sized off the declarations, like the enumeration it estimates: the sum of the
  ;; convicted subtrees, an upper bound on the answer (two partners may share a
  ;; subtype) that costs a cached closure read per partner and no walk over the types.
  (est-bindings [_ kb goal context]
    (let [[_ a b] goal, tx (reasoning/taxonomy kb)
          spec-count (fn [t] (count (tax/specs tx t context)))
          sum        (fn [f xs] (transduce (map f) + 0 xs))]
      (cond
        (and (ground? a) (ground? b)) 1
        (ground? a) (sum spec-count (tax/separating-partners tx a context))
        (ground? b) (sum spec-count (tax/separating-partners tx b context))
        ;; both open: the cross product per separation, or — for one variable in both
        ;; places — the intersection, which the smaller side bounds
        (= a b) (sum (fn [[x y]] (min (spec-count x) (spec-count y)))
                     (tax/separating-pairs tx context))
        :else (sum (fn [[x y]] (* (spec-count x) (spec-count y)))
                   (tax/separating-pairs tx context)))))
  (cost         [_ _ _ _] :lookup)
  ;; The cache is built from the stored declarations and refreshed from belief, so it
  ;; contains what a fact or a forward rule could say.
  (completeness [_ _ _ _] 100)
  ;; scoped: a disjointness holds where its declaration (and the genl edges it
  ;; closes under) are visible, so the query's own context is the vantage — a
  ;; `?ctx` context is the unscoped read, as everywhere
  (solve [_ kb goal context]
    (let [[_ a b] goal tx (reasoning/taxonomy kb)]
      (cond
        (and (ground? a) (ground? b)) (if (tax/disjoint? tx a b context) [{}] [])
        (ground? a) (map (fn [t] {b t}) (disjoint-with tx a context))
        (ground? b) (map (fn [t] {a t}) (disjoint-with tx b context))
        ;; `(disjoint ?x ?x)` — one variable in both places, so one binding; the same
        ;; `Duplicate key` the transitivity prover above states its way past
        (= a b) (map (fn [x] {a x}) (self-disjoint tx context))
        :else (map (fn [[x y]] {a x b y}) (disjoint-cross tx context))))))

;; ---- the minimal common genls and maximal common specs -------------------
;;
;; `(minCommonGenl ?x t1 t2 …)` binds `?x` to each member of `tax/min-common-genls` of the
;; input types, and `(maxCommonSpec ?x t1 t2 …)` to each member of `tax/max-common-specs`.
;; With argument 1 ground the goal is a membership test, and its negation `(not
;; (minCommonGenl x t1 …))` holds when `x` is no member: the set is computed from the
;; closure in full, so a type outside it is proved outside it rather than left unknown.
;; Both predicates are query-only (`wff/common-genl-problems`), so no stored fact or rule
;; conclusion answers either one beside this prover.

(def common-genl-predicates
  "The predicates `CommonGenlProver` answers, each to the taxonomy read that computes it."
  {'minCommonGenl tax/min-common-genls
   'maxCommonSpec tax/max-common-specs})

(defn- common-genl-goal
  "`[read result types]` when `goal` is `(P result t1 t2 …)` for a `common-genl-predicates`
  functor `P`, every input type ground and `result` a variable or a ground term, else nil."
  [goal]
  (when (and (sequential? goal) (<= 3 (count goal)))
    (when-let [read (get common-genl-predicates (first goal))]
      (let [[_ result & types] goal]
        (when (and (every? ground? types) (or (pvar? result) (ground? result)))
          [read result types])))))

(defn- common-genl-negation
  "The `common-genl-goal` reading of a negated goal `(not (P result t1 …))` whose
  `result` is ground, else nil."
  [goal]
  (when (rules/negative-literal? goal)
    (when-let [reading (common-genl-goal (second goal))]
      (when (empty? (sx/free-vars goal)) reading))))

(defrecord CommonGenlProver []
  Prover
  (applicable? [_ _ goal _]
    (boolean (or (common-genl-goal goal) (common-genl-negation goal))))
  (est-bindings [_ kb goal context]
    (if-let [[read result types] (common-genl-goal goal)]
      (if (pvar? result) (count (read (reasoning/taxonomy kb) types context)) 1)
      1))
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative: the predicates are refused as stored facts, so nothing else reads a
  ;; source this prover misses, and the set it tests against is complete over the closure.
  (completeness [_ _ _ _] 100)
  ;; scoped: the closures are read through the edges the asking context sees, and a
  ;; `?ctx` context is the unscoped read, as for `genl`
  (solve [_ kb goal context]
    (let [tx (reasoning/taxonomy kb)]
      (if-let [[read result types] (common-genl-goal goal)]
        (let [found (read tx types context)]
          (if (pvar? result)
            (map (fn [t] {result t}) (nm/sort-by-content-key identity found))
            (if (contains? found result) [{}] [])))
        (let [[read result types] (common-genl-negation goal)]
          (if (contains? (read tx types context) result) [] [{}]))))))

;; ---- generic relation reasoners (predicate metadata) --------------------

(defn- hop-patterns
  "The one-hop lookup patterns for `node` under `pred`, each binding `?rv` to the neighbour.
  `dir` is `:succ` (node in argument 1) or `:pred` (node in argument 2).

  One probe per visible `(inverse P' Q)` with `P'` at or below `pred`, plus the direct one,
  since `(P x y)` and `(Q y x)` are one edge recorded two ways and a partner of a
  sub-predicate records a `pred` tuple by subsumption (`inverses-under`).  Every declared
  partner is probed, so visibility does not depend on declaration order.  The partner is probed
  with `matches-visible` on the swapped literal and not by delegating to the registry, so the
  step relation is a function of the KB alone (`vaelii.impl.literal-cache`) and a mutual
  inverse pair cannot cycle here.  A `P` declared its own inverse yields the two probes of a
  symmetric predicate."
  [kb dir pred node context]
  (let [qs (sort (tax/inverses-under (reasoning/taxonomy kb) pred context))]
    (if (= dir :succ)
      (into [(list pred node '?rv)] (map #(list % '?rv node)) qs)
      (into [(list pred '?rv node)] (map #(list % node '?rv)) qs))))

(defn- closure-key
  "The key a walk's reach and its neighbour sets are held under, one function because three
  sites must agree: the open ask that fills the cache and the closed pair that reads it from
  either end.

  `[dir pred node context]` covers what the step relation reads.  The belief mode is the
  fifth, not covered by the clock: a `CxEverything` read moves nothing, so without it a blind
  and an ordinary read share an entry.  The sixth and seventh are `tax/*search*` and
  `tax/*network-belief*`.  `memo-neighbours` is not a site: its memo is bound per search step
  (`observe/with-search-scope`), where the belief mode cannot change, and keying it here would
  put a `^:dynamic` deref in the walk's innermost loop (`res/belief-blind?`)."
  [dir pred node context]
  [dir pred node context (res/belief-blind?) exc/*unscoped-own* tax/*search* tax/*network-belief*])

(defn- memo-neighbours
  "The neighbours of `node` under `pred` as `{neighbour #{handle}}`: the terms one hop away,
  each with the handles of the stored sentexes that record the hop, cached in
  `observe/*reach-memo*` when one is bound.  `dir` is `:succ` (node in argument 1) or `:pred`
  (node in argument 2).

  The key `[dir pred node context]` covers what the step relation reads (`closure-key` gives
  the belief mode).  Neighbours are keyed by term, so an edge recorded in both spellings is one
  member whose handle set gathers every spelling.  The handles make this a map: a closure
  answer supports a forward firing (`SupportingProver`) and rests on the edges it crossed, and
  keeping every spelling avoids keying the justification on arrival order.  Read with
  `matches-visible`'s `cached?` false, since a walk asks each literal once and an insertion
  per node would clear the solution cache."
  [kb dir pred node context]
  (let [compute #(reduce (fn [m [h b]]
                           (if-let [rv (get b '?rv)]
                             (update m rv (fnil conj #{}) h)
                             m))
                         {}
                         (mapcat (fn [pat] (res/matches-visible kb pat context false))
                                 (hop-patterns kb dir pred node context)))]
    (if-let [m observe/*reach-memo*]
      (let [k [dir pred node context]]
        (if (contains? @m k)
          (do (observe/note-neighbours! true) (get @m k))
          (let [v (compute)]
            (observe/note-neighbours! false)
            (swap! m assoc k v)
            v)))
      (do (observe/note-neighbours! false) (compute)))))

(defn- succs
  "y such that (pred x y) is believed, visible from context (memoized per query) — the
  neighbour terms alone, the handles beside them being the support walk's business."
  [kb pred x context]
  (keys (memo-neighbours kb :succ pred x context)))

(defn- preds-of
  "x such that (pred x y) is believed, visible from context (memoized per query)."
  [kb pred y context]
  (keys (memo-neighbours kb :pred pred y context)))

(defn- walk-sources
  "Every term the closure can start from: argument 1 of a believed `pred` fact, and
  argument 2 of a believed partner fact for each visible `(inverse P Q)`.  A node with no
  outgoing edge reaches nothing and contributes no pair, so this is the whole closure's
  seed set and not an enumeration of the vocabulary — bounded by the extent, the way
  `DisjointnessProver`'s open goal is bounded by the declarations."
  [kb pred context]
  (let [qs   (sort (tax/inverses-under (reasoning/taxonomy kb) pred context))
        ends (fn [pat k] (keep #(get (second %) k) (res/matches-visible kb pat context)))]
    (distinct (apply concat
                     (ends (list pred '?lv '?rv) '?lv)
                     (map #(ends (list % '?lv '?rv) '?rv) qs)))))

(defn- on-a-cycle
  "The nodes reachable from themselves under `step`, starting from `sources` — the answer
  to `(P ?x ?x)` for a declared-transitive `P`.

  **One pass over the graph, not one closure per source.**  Asking `reaches?` per source
  walks that source's whole reach to fail, so an acyclic chain of *n* nodes costs O(n²) to
  answer nothing — the form a temporal or part-of chain actually has, and the shape this
  arm is most often asked about.  A node lies on a cycle exactly when its strongly
  connected component has more than one member, or when it has a self-edge, so Tarjan
  answers every source at once in O(V+E).

  Iterative (`graph/scc`): a 100k-node `before` chain would overflow a recursive walk."
  [sources step]
  (let [cyclic (volatile! (transient #{}))]
    ;; the self-edge is read off the successors already in hand: a singleton component
    ;; is cyclic only through one, and asking `step` again would double the retrievals
    (graph/scc sources
               (fn [v]
                 (let [succ (vec (step v))]
                   (when (some #(= v %) succ) (vswap! cyclic conj! v))
                   succ))
               (fn [members]
                 (when (> (count members) 1)
                   (vswap! cyclic #(reduce conj! % members)))))
    (persistent! @cyclic)))

;; ---- the closure answer cache ------------------------------------------
;; `reach` is a fixpoint, and this is the only layer that can answer a repeat: a walk asks
;; each node's neighbour literal once, so the per-literal solution cache is neither
;; consulted nor filled by one (`res/matches-visible`, `cached?` false).  A repeat costs
;; 52 µs against 127 µs for the walk over a 40-member class (`lein bench-walk`).
;; A reach set is neither tier-dependent nor scope-dependent, the two properties
;; `literal-cache` requires and `solve-goal` lacks: dropping this prover means `solve` is
;; never called, and the walk reads `matches-visible` and the taxonomy's generation-keyed
;; memos, never `observe/cached`.  The entry is an answer of this prover, not of the
;; registry.

(def ^:dynamic *closure-answer-limit*
  "The most reach **members** one KB's closure cache holds before it is dropped
  wholesale.  Members, not entries, and that is the whole of the design: an entry here is
  a whole reach set, so ten entries can be ten members or a million, and a bound counting
  entries would bound nothing.  A single reach larger than this is never stored — it is
  the case the bound exists for — and a total that reaches it drops the map rather than
  evicting entry by entry, the wholesale clearing `literal-cache` and `observe` take and
  for the reason they give.

  Dynamic so a test can drive the bound rather than build a corpus large enough to reach
  it — the bound is a decision, and one nothing exercises is one nothing checks."
  100000)

(defn- closure-hit
  "The cached reach at `k`, or nil — only under `clock`, since one clock move retires
  every entry at once and the clock value is therefore the map's rather than the entry's.
  A KB with no cache atom answers nil, which is a miss and costs an extra walk rather than
  a wrong answer."
  [kb k ^long clock]
  (when-let [a (reasoning/closures kb)]
    (let [c @a]
      (when (== clock (long (:clock c -1)))
        (get (:entries c) k)))))

(defn- hold-closure
  "Hold `v` at `k`, under `clock`.  No `!`: it destroys nothing and every entry is
  derived, so the next ask recomputes whatever the drop below took."
  [kb k v ^long clock]
  (let [lim (long (caches/limit-of :closure-answers *closure-answer-limit*))]
    (when (and (reasoning/closures kb) (<= (count v) lim))
      (swap! (reasoning/closures kb)
             (fn [c]
               (let [c (if (== clock (long (:clock c -1)))
                         c
                         {:clock clock :members 0 :entries {}})
                     m (+ (long (:members c 0)) (count v))]
                 (cond
                   (contains? (:entries c) k) c
                   (> m lim) {:clock clock :members 0 :entries {}}
                   :else (assoc c :members m :entries (assoc (:entries c) k v)))))))))

(defn- cached-reach
  "The reach of `node` under `pred` in `dir`, from the KB's cache when it holds one, else
  walked and held.

  The clock is read **before** the walk and the answer kept only if it has not moved by
  the time the walk finishes — `literal-cache/lookup`'s discipline, and the same two
  reasons.  Reading the clock afterwards would claim the set describes a state it was never
  computed from; and a caller that *writes while it reads* — forward chaining, whose own
  conclusions move the clock under it — fills this with nothing rather than with
  something stale.  Belief is covered by the same clock value: a relabel moves the clock,
  so a defeated edge retires the closure that crossed it without anything here knowing
  which entry to look for.  Belief *mode* is not: see `closure-key`."
  [kb dir pred node context step]
  (let [k     (closure-key dir pred node context)
        clock (observe/change-clock)
        t     (some-> (reasoning/closures kb) (caches/tally-of :R2))]
    (if-let [v (closure-hit kb k clock)]
      (do (caches/hit t) v)
      (caches/held-if-settled
       #(caches/recomputed t (graph/reach-all (step node) step))
       (fn [v]
         (when (caches/tallying?)
           (when-let [old (get (:entries @(reasoning/closures kb)) k)]
             (caches/compared t (= old v))))
         (when (== (observe/change-clock) clock) (hold-closure kb k v clock))
         v)))))

(defn- reaches?
  "Is `tgt` in the transitive reach of `seed` under `step`?  Stops at the first
  sighting, so a near answer is cheap — the membership question is *not* the closure
  question, and answering it by building the closure charges a two-hop pair for the
  whole extent (measured flat at 7ms from 2 hops to 800 on an 800-long chain).  Only a
  goal with an open argument needs every node, and that is what `reach` is for.

  Guards with `seen`, so a cycle terminates: nothing refuses one in a
  declared-transitive predicate the way `wff` refuses a `genl` cycle, and a cyclic
  transitive relation genuinely does entail reflexivity around the loop."
  [seed step tgt]
  (loop [seen #{}, frontier (vec seed)]
    (if-let [x (peek frontier)]
      (cond
        (= x tgt) true
        (seen x)  (recur seen (pop frontier))
        :else     (recur (conj seen x) (into (pop frontier) (step x))))
      false)))

(defn- support-parents
  "One breadth-first walk out from `root`, recording for every node reached the node it was
  first reached from and the handles of that hop: `{node [parent #{handle}]}`, with `nil` as
  the parent of `root`'s own neighbours.  The first visit is along a shortest chain, so a
  chain is at most as long as the graph is deep whatever the edge arrival order.  Neighbour
  sets come from `memo-neighbours`, sharing its memo inside a search scope."
  [kb dir pred root context]
  (let [edges #(memo-neighbours kb dir pred % context)]
    (:tree (graph/bfs-tree (map (fn [[n hs]] [n [nil hs]]) (edges root))
                           (fn [n _] (map (fn [[m hs2]] [m [n hs2]]) (edges n)))
                           (constantly false)))))

(defn- support-chain
  "The handles of the chain `support-parents` recorded from its root to `node`, or nil
  when nothing reached `node`.

  Every hop contributes every handle that records it, which is the `SupportingProver` protocol's sanctioned
  over-approximation: a hop written both as `(P x y)` and as an inverse `(Q y x)` is
  licensed by either, and naming only one would decide the justification by arrival order.

  Guarded with `seen` because a cycle can make a node its own ancestor in the parent map's
  eyes — the parent pointers are a tree over the *first* sighting, and a cycle's last edge
  closes back onto a node already in it."
  [parents node]
  (loop [n node seen #{} out #{}]
    (if-let [[p hs] (and n (not (seen n)) (get parents n))]
      (recur p (conj seen n) (into out hs))
      (when (seq out) out))))

(def ^:dynamic *unenumerated*
  "nil, or a collector (`unenumerated-collector`) that `TransitivePredicateProver` adds a
  predicate to when it does not enumerate the closure for a goal asked with both arguments
  open. A read that reports the set binds it around each eager stretch of its search
  (docs/anytime.md, \"Where the collector lives\")."
  nil)

(def ^:private ^:dynamic *in-guard*
  "True inside an `unknown` or `exceptWhen` evaluation (`as-guard`), where a missed closure
  pair can admit an answer rather than lose one."
  false)

(defn unenumerated-collector
  "A fresh collector for `*unenumerated*`: `:all` holds every predicate the arm recorded,
  `:guarded` the subset recorded inside an `unknown` or `exceptWhen` evaluation."
  []
  (atom {:all #{} :guarded #{}}))

(defn unenumerated-report
  "Collector `a` as `{:unenumerated [P …] :unenumerated-in-guards [P …]}`, each vector in
  content order."
  [a]
  (let [order #(into [] (nm/sort-by-content-key nm/print-key compare %))
        {:keys [all guarded]} @a]
    {:unenumerated (order all) :unenumerated-in-guards (order guarded)}))

(defn with-unenumerated
  "`(f)` with a fresh collector bound, as `[result report]`, `report` being
  `unenumerated-report`'s. `f` must be eager, since the collector is a binding."
  [f]
  (let [a (unenumerated-collector)
        r (binding [*unenumerated* a] (f))]
    [r (unenumerated-report a)]))

(defn collecting-seq
  "The seq `(f)` returns, with `*unenumerated*` bound to collector `a` around the call and
  around each pull, for a lazy read: a binding around the call alone has ended before a
  pull runs the arm."
  [a f]
  (letfn [(pulls [xs]
            (lazy-seq
             (binding [*unenumerated* a]
               (when-let [s (seq xs)]
                 (cons (first s) (pulls (rest s)))))))]
    (pulls (binding [*unenumerated* a] (f)))))

(defn- as-guard
  "`(f)` with the arm recording into the collector's `:guarded` set as well."
  [f]
  (if *unenumerated* (binding [*in-guard* true] (f)) (f)))

(defn- unblocked
  "`sols`, each a binding map or a `[bindings support]` pair, less those naming a node of an
  unsatisfiable component of the network of the calculus claiming the goal's predicate at
  `context` (`qcn-kb/blocked-nodes`).  A declared property of a calculus predicate answers
  no goal there that the calculus does not (docs/qcn.md, \"Unsatisfiability is per
  component\")."
  [kb [pred a b] context sols]
  (let [blocked (when-let [c (qkb/calculus-for kb pred)]
                  (not-empty (qkb/blocked-nodes c kb context)))]
    (if blocked
      (remove (fn [s] (let [bnd (if (map? s) s (first s))]
                        (or (contains? blocked (get bnd a a)) (contains? blocked (get bnd b b)))))
              sols)
      sols)))

(defrecord TransitivePredicateProver []          ; declared-transitive predicates (not genl/genlCx)
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal)
         (tax/has-prop? (reasoning/taxonomy kb) :transitive (first goal) context)
         (not (contains? transitive-predicates (first goal)))))
  (est-bindings [_ kb goal _] (est-by-functor kb goal))
  (cost         [_ _ _ _] :compute)              ; computes the reach fixpoint before the first answer
  ;; not the *sole* complete method — the same predicate may also be symmetric /
  ;; inverse, so union with those provers rather than running alone.
  (completeness [_ _ _ _] 70)
  (solve [_ kb goal context]
    (unblocked
     kb goal context
     (let [[pred a b] goal
           fwd  #(succs kb pred % context)
           back #(preds-of kb pred % context)]
       (cond
         ;; A closed goal asks about *one* pair, so it stops at the answer — and it
         ;; **consults** the closure cache without filling it, which is the whole of the
         ;; asymmetry: an entry answers the pair by membership, while computing one to
         ;; store would charge a two-hop question for the entire extent, the early exit
         ;; `reaches?` exists for.
         (and (ground? a) (ground? b))
         (let [clock (observe/change-clock)
               from  (closure-hit kb (closure-key :succ pred a context) clock)
               into' (closure-hit kb (closure-key :pred pred b context) clock)]
           (cond
             from  (if (contains? from b) [{}] [])
             into' (if (contains? into' a) [{}] [])
             :else (if (reaches? (fwd a) fwd b) [{}] [])))
         ;; an open argument enumerates, and `reach` is a fixpoint — computing *any* of
         ;; the closure computes all of it, so only the wrapping is lazy here.  That is
         ;; inherent to a closure, not a missed optimization.
         (ground? a) (map (fn [y] {b y}) (cached-reach kb :succ pred a context fwd))
         (ground? b) (map (fn [x] {a x}) (cached-reach kb :pred pred b context back))
         ;; `(P ?x ?x)` asks which nodes lie on a cycle and binds one variable.  It is written out
         ;; for the `Duplicate key` reason `TransitivityProver` gives above, and answered by one
         ;; condensation, since `reaches? x x` would walk the whole reach to fail on an acyclic chain.
         ;; The sort key is a printed form (`nm/print-key`), because a binding can be a list and a
         ;; bare sort throws on a non-`Comparable` term.
         (= a b) (map (fn [x] {a x})
                      ;; the key keeps a list-valued binding sortable; built once per term
                      (nm/sort-by-content-key nm/print-key compare
                                              (on-a-cycle (walk-sources kb pred context) fwd)))
         ;; Both open: nothing from here, so the extent answers through the ordinary match path.
         ;; `completeness` 70 makes the registry union rather than run this alone, so an empty seq
         ;; is a contribution of none.  The closure of a transitive relation is quadratic in a
         ;; chain's length, and `reach` is a fixpoint costing a whole node's closure per pair, so it
         ;; is computed for membership and one bound end and never enumerated whole.  A report read
         ;; learns of the skip through `*unenumerated*`.
         :else (do (when-let [a *unenumerated*]
                     (let [g? *in-guard*]
                       (swap! a #(cond-> (update % :all conj pred) g? (update :guarded conj pred)))))
                   [])))))

  SupportingProver
  ;; Both sets are empty: the functors this answers are those a KB declared
  ;; `(transitive P)` of, a taxonomy read that a protocol with no `kb` argument cannot
  ;; return.  `chain/transitive-antecedent?` and `chain/transitive-rejoin-rules` ask the
  ;; taxonomy instead, and `solve-with-support` needs no functor list.
  (support-functors [_] #{})
  (support-sources  [_] #{})
  ;; The same solutions `solve` gives, in the same order, each carrying the handles of one
  ;; chain of stored edges.  The bindings come from the same `reach` / `reaches?`, closure
  ;; cache included, and the chain from one breadth-first pass with parent pointers that
  ;; shares `memo-neighbours`.  A cycle answer is walked per node, since the condensation
  ;; holds no edges.  Both arguments open answers nothing, as in `solve`.  A chain of more
  ;; than one handle also rests on the declaration, so the support names every believed
  ;; `(transitive P)` that `context` sees (`res/declared-by`); a declaration stated
  ;; apart from the hops licenses the pair only below both.
  (solve-with-support [_ kb goal context]
    (unblocked
     kb goal context
     (let [[pred a b] goal
           fwd   #(succs kb pred % context)
           back  #(preds-of kb pred % context)
           decls (delay (res/declared-by kb :transitive pred context))
           with  (fn [sup] (when sup (if (next sup) (into sup @decls) sup)))
           chain (fn [dir root node]
                   (with (support-chain (support-parents kb dir pred root context) node)))]
       (cond
         (and (ground? a) (ground? b))
         (if-let [sup (and (reaches? (fwd a) fwd b) (chain :succ a b))]
           [[{} sup]]
           [])

         (ground? a)
         (let [parents (support-parents kb :succ pred a context)]
           (keep (fn [y] (when-let [sup (with (support-chain parents y))] [{b y} sup]))
                 (cached-reach kb :succ pred a context fwd)))

         (ground? b)
         (let [parents (support-parents kb :pred pred b context)]
           (keep (fn [x] (when-let [sup (with (support-chain parents x))] [{a x} sup]))
                 (cached-reach kb :pred pred b context back)))

         (= a b)
         (keep (fn [x] (when-let [sup (chain :succ x x)] [{a x} sup]))
               (nm/sort-by-content-key nm/print-key compare
                                       (on-a-cycle (walk-sources kb pred context) fwd)))

         :else [])))))

(defrecord TransitiveInArgProver []       ; (transitiveInArg P n R) / (transitiveInArgInverse P n R)
  Prover
  (applicable? [_ kb goal context]
    (boolean (if-let [[_ lit] (inherit/goal-verdict goal)]
               (seq (inherit/positions kb (nm/functor lit) context))
               (inherit/open-goal? kb goal context))))
  ;; 1 is a ground goal's answer count, not the cost (docs/inherit.md, "What one question costs")
  (est-bindings [_ kb goal _] (if (seq (sx/free-vars goal)) (est-by-functor kb goal) 1))
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 60)
  (solve [_ kb goal context]
    (inherit/with-memo
      ;; `:ambiguous` yields nothing; the claim walk stops at the `ask`'s deadline
      (binding [inherit/*deadline* budget/*deadline*]
        (cond (seq (sx/free-vars goal))         (inherit/open-answers kb goal context)
              (inherit/answers? kb goal context) [{}]
              :else                             []))))
  SupportingProver
  (support-functors [_] #{})
  (support-sources  [_] #{})
  (solve-with-support [_ kb goal context]
    (inherit/with-memo
      (binding [inherit/*deadline* budget/*deadline*]
        (let [read (fn [b g] (or (seq (map (fn [hs] [b (set hs)]) (inherit/answer-readings kb g context)))
                                 [[b #{}]]))]
          (cond (seq (sx/free-vars goal))
                (into [] (mapcat #(read % (res/substitute goal %))) (inherit/open-answers kb goal context))
                (inherit/answers? kb goal context) (vec (read {} goal))
                :else                              []))))))

(defrecord SymmetricProver []
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal) (tax/has-prop? (reasoning/taxonomy kb) :symmetric (first goal) context)))
  (est-bindings [_ kb goal _] (est-by-functor kb goal))
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 50)                 ; augments the fact prover
  ;; Delegates the mirrored goal rather than reading raw matches, for `InverseProver`'s
  ;; reason: a symmetric predicate's mirror composes with the *other* provers, so the
  ;; mirror of a claim that is preserved or computed — not stored — is still an answer.
  ;; See `solve-mirrored` for the re-entry bound.
  (solve [_ kb goal context]
    (let [[pred a b] goal]
      (solve-mirrored kb pred a b context))))

(defn- inverted-partners
  "The partner predicates `solve-inverted` asks for the binary `goal` or the `(not …)` over
  one: `tax/inverses-under` its functor for a positive goal, `tax/inverses-over` it under
  `res/holding-class` for a negated one.  Empty for any other shape."
  [kb goal context]
  (let [tx (reasoning/taxonomy kb)]
    (cond
      (binary? goal) (tax/inverses-under tx (first goal) context)
      (and (sx/negation? goal) (binary? (second goal)) (symbol? (first (second goal))))
      (tax/inverses-over tx (first (second goal)) context (res/holding-class kb))
      :else #{})))

(defrecord InverseProver []
  Prover
  (applicable? [_ kb goal context]
    (boolean (seq (inverted-partners kb goal context))))
  (est-bindings [_ kb goal _] (est-by-functor kb goal))
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 50)
  ;; Delegates the swapped goal to the engine rather than to raw fact matching, so
  ;; an inverse *composes* with its partner's other properties — `(afterEvent C A)`
  ;; over a declared-transitive `beforeEvent` chain reaches the closure prover, not
  ;; just stored direct links.  (That was a general gap for any `(inverse P Q)` with
  ;; transitive Q, documented as an afterEvent special case.)  See `solve-inverted`
  ;; for why the delegate list excludes this prover.
  (solve [_ kb goal context]
    (solve-inverted kb goal context)))

(defrecord ReflexiveProver []
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal) (tax/has-prop? (reasoning/taxonomy kb) :reflexive (first goal) context)))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 50)
  ;; the diagonal holds of a term the declared argument types admit at both positions
  ;; (`res/arg-admits-fn`), the admission a calculus asks of the same goal, and outside an
  ;; unsatisfiable component of the calculus's network (`unblocked`)
  (solve [_ kb goal context]
    (let [[p a b] goal
          admits? #(let [f (res/arg-admits-fn kb p context)] (and (f % 0) (f % 1)))]
      (unblocked kb goal context
                 (cond (and (ground? a) (ground? b)) (if (and (= a b) (admits? a)) [{}] [])
                       (ground? a) (if (admits? a) [{b a}] [])
                       (ground? b) (if (admits? b) [{a b}] [])
                       :else [])))))

;; ---- evaluable predicates (computed, not stored) ------------------------

(def literal-value-kinds
  "The value kind of a literal value, most specific first: each kind with the EDN test a
  value of it passes.  A value denotes itself, so its kind is decidable from the value
  alone.  `checks/value-kind` classifies a value by the first test it passes, and
  `EvaluableProver` answers a value-kind membership by the kind's own test, so `integer`
  falls under `number` there by `number?`.  A symbol is not a literal: a constant can
  denote a value of any kind."
  [['string    string?]
   ['boolean   boolean?]
   ['integer   integer?]
   ['number    number?]
   ['keyword   keyword?]
   ['character char?]])

(defn literal-value-kind
  "The most specific value kind of `x`, or nil when `x` is no literal value."
  [x]
  (some (fn [[k test]] (when (test x) k)) literal-value-kinds))

(def ^:private value-kind-tests
  (into {} literal-value-kinds))

(def value-kind-predicates
  "The value kinds `EvaluableProver` answers for a literal argument, beside `integer`,
  which it answers for any ground argument."
  '#{string number boolean keyword character})

(def evaluable-predicates
  "Predicates a prover computes from its ground arguments rather than looks up.

  - `lessThan` / `greaterThan`: variable-arity arithmetic comparisons, `(lessThan 1 2 3)`
    states 1 < 2 < 3.  `greaterThan` is folded to `lessThan` when stored (`vaelii.impl.sentex`)
    and answered directly when asked.
  - `integer`: the unary EDN-kind check, which lets the sign-refined integer collections in
    core.txt resolve by evaluation (docs/defns.md).
  - `string`, `number`, `boolean`, `keyword`, `character`: value kinds, answered only for a
    literal argument (`literal-value-kind`).  A symbol or compound is left to the other
    provers.
  - `matchesPattern`: `(matchesPattern ?string ?pattern)` holds when the whole of the string
    matches the regular expression, both ground; false for a non-string subject.  It runs
    through `bounded-matches?`, so a backtracking pattern is a `:pattern-too-costly` refusal.

  The set is what `EvaluableProver` reads its arguments as, not a claim about what answers a
  predicate; the `:answers` facet of each is checked against it by `predicates_test`."
  (into '#{lessThan greaterThan integer matchesPattern} value-kind-predicates))

(def ^:private ^:const match-step-budget
  "Characters one `matchesPattern` match may read before it is refused as too costly.  A
  linear match reads O(string length); a catastrophically-backtracking pattern reads
  super-linearly and blows this, so the two separate cleanly.  Per match, because a goal
  matches one string rather than scanning a vocabulary — the scan-wide budget `find-terms`
  carries has no counterpart here."
  1000000)

(defn- bounded-matches?
  "Does the whole of `s` match the regular expression `pattern`, read through a step-limited
  `CharSequence` that throws `:pattern-too-costly` once the match reads past
  `match-step-budget` characters?  A `Matcher` reads a character per backtracking step, so a
  pathological pattern is refused on the step that exceeds the budget rather than running
  unbounded — which keeps `EvaluableProver`'s completeness-100 claim true for a
  ground goal.  An uncompilable pattern yields nil here; the assert entry point refuses one
  loudly (`checks/matches-pattern-problem`), so a compile failure reaching query time is a
  goal that never passed a check, answered as no match rather than as an error."
  [^String pattern ^String s]
  (when-let [^java.util.regex.Pattern re (try (java.util.regex.Pattern/compile pattern)
                                              (catch java.util.regex.PatternSyntaxException _ nil))]
    (let [seen (java.util.concurrent.atomic.AtomicLong.)
          bounded (reify CharSequence
                    (length [_] (.length s))
                    (charAt [_ i]
                      (when (> (.incrementAndGet seen) (long match-step-budget))
                        (throw (ex-info (str "regex is too costly to evaluate against "
                                             (pr-str s) " — the match read past "
                                             match-step-budget " characters of it")
                                        {:type :pattern-too-costly :scope :candidate})))
                      (.charAt s i))
                    (subSequence [_ a b] (.subSequence s ^int a ^int b))
                    (toString [_] s))]
      (.matches (.matcher re ^CharSequence bounded)))))

(defn- literal-value-kind-goal?
  "Is `goal` a value-kind membership `(k x)`, `k` one of `value-kind-predicates` and `x` a
  literal value?"
  [goal]
  (and (sequential? goal) (contains? value-kind-predicates (first goal))
       (= 1 (count (rest goal))) (some? (literal-value-kind (second goal)))))

(defn term-value-kind-goal?
  "Is `goal` a value-kind membership `(k x)`, `k` one of `value-kind-predicates`, over a
  ground `x` that is no literal value?  `EvaluableProver` leaves it to the other provers,
  since a constant or a function application can denote a value of any kind."
  [goal]
  (and (sequential? goal) (contains? value-kind-predicates (first goal))
       (= 1 (count (rest goal))) (ground? goal) (nil? (literal-value-kind (second goal)))))

(defn- negated-value-kind-goal?
  "Is `goal` `(not (k x))` over a literal-value-kind goal?"
  [goal]
  (and (sequential? goal) (= 'not (first goal)) (= 2 (count goal))
       (literal-value-kind-goal? (second goal))))

(defn- literal-of-kind?
  "Does the literal `x` pass value kind `k`'s test?"
  [k x]
  ((value-kind-tests k) x))

;; ---- expression kinds: what a quoted form is ----------------------------------
;; `(Quote X)` denotes the expression X.  Some of X's kinds follow from how X is written
;; (`shape-kinds`); whether `(R a)` is a predication, a non_atomic_term or ill-formed is
;; what the KB states of R (`stated-kinds`).  docs/argtypes.md, "What a quoted form is".

(def formula-heads
  "The heads whose application is a formula whatever its operands: the connectives, the
  rule and exception frames, and the quantifiers."
  '#{not and or implies exceptWhen ist unknown thereExists forall exists})

(defn shape-kinds
  "The most specific expression kinds of the form `x` that its spelling decides, as a
  set: `variable`, `symbol`, a value kind (`literal-value-kind`), or for a compound one
  of `open_formula` / `sentence` under a `formula-heads` head, `sentex_handle_term` for
  `(sentexHandle N)` with N a positive integer, `non_atomic_expression` beside
  `open_expression` / `closed_expression` under any other symbol or variable head, and
  `ill_formed_expression` beside the same under any other head.  A variable inside a
  nested `(Quote …)` or bound by a quantifier in `x` is not free (`sx/unquoted-free-vars`).
  `#{}` for nil."
  [x]
  (let [openness #(if (seq (sx/unquoted-free-vars x)) 'open_expression 'closed_expression)]
    (cond
      (sx/variable? x)       #{'variable}
      (symbol? x)            #{'symbol}
      (literal-value-kind x) #{(literal-value-kind x)}
      (sequential? x)
      (let [h (first x)]
        (cond
          (contains? formula-heads h)
          #{(if (= 'open_expression (openness)) 'open_formula 'sentence)}
          (and (sx/sentex-handle? x) (pos? (long (second x)))) #{'sentex_handle_term}
          (symbol? h) #{'non_atomic_expression (openness)}
          :else       #{'ill_formed_expression (openness)}))
      :else #{})))

(def expression-kind-predicates
  "The kinds `ExpressionKindProver` answers of a quoted form, as a set: the expression
  lattice `reflection.txt` declares and the value kinds below it.  Forward chaining
  discharges an antecedent through the prover only when its functor is here
  (`support-answered-preds`),
  so a kind a KB adds below `expression` is answered by a query and not by a firing."
  '#{expression atomic_expression non_atomic_expression atomic_term variable symbol
     unrepresented_term string number integer keyword boolean character
     denotational_term non_atomic_term sentex_handle_term formula sentence open_formula
     predication closed_predication open_predication literal closed_literal open_literal
     wff_expression ill_formed_expression ill_formed ill_formed_sentence
     open_expression closed_expression})

(def ^:private stated-kind-floor
  "The kinds `stated-kinds` can give a form.  A relation's stored kind or length moves the
  answers at or above one of them (`relation-moved-answers`)."
  '[closed_predication open_predication non_atomic_term ill_formed_sentence ill_formed
    open_formula ill_formed_expression])

(defn- quoted-form
  "`[F x handles]` when the term `q` is a quoted form: `(F x)` with `F` a quoting function
  (`sx/quoting-functors`), handles empty, or a reified constant whose `natFormula`,
  visible from `context`, is one, handles that statement.  Else nil.  A reified constant
  is a symbol in a reified namespace (`nat-read/reified-nat-symbol?`)."
  [kb q context]
  (cond
    (and (sequential? q) (= 2 (count q)) (sx/quoting-functor? (first q)))
    [(first q) (second q) []]

    (and (symbol? q) (= "nat" (namespace q)))
    (some->> (res/matches-visible kb (list 'natFormula q '?e) context)
             (keep (fn [[h b]]
                     (let [e (get b '?e)]
                       (when (and (sequential? e) (= 2 (count e)) (sx/quoting-functor? (first e)))
                         [(first e) (second e) [h]]))))
             seq
             (nm/min-by-content-key #(nth % 1)))))

(defn- expression-kind-goal?
  "Is `goal` `(k q)`, `k` a ground type below `expression` from `context` and `q` a
  quoted form (`quoted-form`)?"
  [kb goal context]
  (let [tax (reasoning/taxonomy kb)
        q   (when (and (sequential? goal) (= 2 (count goal))) (second goal))]
    ;; the spelling tests run first: every membership goal reaches this
    (and (some? q) (symbol? (first goal)) (not (sx/variable? (first goal)))
         (or (and (sequential? q) (= 2 (count q)) (sx/quoting-functor? (first q)))
             (and (symbol? q) (= "nat" (namespace q))))
         (tax/genl? tax (first goal) 'expression context)
         (some? (quoted-form kb q context)))))

(defn- relation-kinds
  "`{kind handles}` for each of `predicate` and `function` the symbol `r` is a member of
  from `context`: the content-least believed membership `(T r)` whose `T` reaches the
  kind (`res/type-memberships`), its handle followed by the edges of one `genl` path from
  `T` to the kind (`tax/reach-support`)."
  [kb r context]
  (let [tax (reasoning/taxonomy kb)
        ms  (sort-by (juxt #(nm/name-key (nm/functor (:sentence %))) #(nm/name-key (:context %)))
                     (res/type-memberships kb r context))]
    (into {}
          (keep (fn [k]
                  (some (fn [m]
                          (let [t (nm/functor (:sentence m))]
                            (when (tax/genl? tax t k context)
                              [k (into [(:id m)] (map first) (tax/reach-support tax :genl t k context))])))
                        ms)))
          '[predicate function])))

(defn stated-kinds
  "The expression kinds of the compound `x` under a symbol head `r` that what the KB states
  of `r` decides, as `{kind handles}`, each kind with the statements it rests on.  When
  `r` is a predicate and not a function (`relation-kinds`), `x` is a `closed_predication`,
  or an `open_predication` when a variable is free in it.  When `r` is a function and not
  a predicate, a closed `x` is a `non_atomic_term`.  When the argument count breaks `r`'s
  length (`arity/broken-binding`, read the same at every context), `x` is an
  `ill_formed_sentence` for a predicate `r` and a closed `x`, an `ill_formed` and an
  `open_formula` for a predicate `r` and an open `x`, and an `ill_formed_expression`
  otherwise; the binding's grounds and route are among the handles.  The map is empty for
  any other `x`, and for an `r` the KB places under both kinds or neither."
  [kb x context]
  (let [r (when (sequential? x) (first x))]
    (if (or (not (symbol? r)) (sx/variable? r) (contains? formula-heads r))
      {}
      (let [open? (boolean (seq (sx/unquoted-free-vars x)))
            rel   (relation-kinds kb r context)
            p     (when-not (get rel 'function) (get rel 'predicate))
            f     (when-not (get rel 'predicate) (get rel 'function))
            bad   (arity/broken-binding kb r (dec (count x)))]
        (cond
          bad      (let [hs (into (:grounds bad) (:route bad))]
                     (cond
                       (nil? p) {'ill_formed_expression hs}
                       open?    (let [hs (into hs p)] {'ill_formed hs 'open_formula hs})
                       :else    {'ill_formed_sentence (into hs p)}))
          p        {(if open? 'open_predication 'closed_predication) p}
          (and f (not open?)) {'non_atomic_term f}
          :else    {})))))

(defn stated-kind-handles
  "The handles of the believed memberships `(T r)`, at every context, of the symbol `r`
  heading the compound the goal `g` quotes, when `g` is on an expression kind
  (`expression-kind-predicates`); else nil.  `stated-kinds` reads these beside the
  prover's source functors, so a forward join asks `g` at their contexts too
  (`source-contexts`'s `also`)."
  [kb g]
  (when (and (sequential? g) (= 2 (count g)) (contains? expression-kind-predicates (first g)))
    (when-let [[_ x _] (quoted-form kb (second g) '?ctx)]
      (let [r (when (sequential? x) (first x))]
        (when (and (symbol? r) (not (sx/variable? r)) (not (contains? formula-heads r)))
          (not-empty (mapv :id (res/type-memberships kb r '?ctx))))))))

(defn- expression-kind-support
  "The handles `(k q)` rests on, as a vector, or nil when no kind of the form `q` quotes
  reaches `k` from `context`: the `natFormula` statement when `q` is a reified constant,
  then one `genl` path from the first kind of the form that reaches `k`, the kinds its
  spelling decides (`shape-kinds`) in name order and then the kinds the KB decides
  (`stated-kinds`) in name order, each of these with the handles it rests on.  The
  quoting function itself is fixed by the engine and rests on no statement."
  [kb [k q] context]
  (let [tax (reasoning/taxonomy kb)]
    (when-let [[_ x hs] (quoted-form kb q context)]
      (let [reach (fn [[s sup]]
                    (when-let [path (tax/reach-support tax :genl s k context)]
                      (-> hs (into sup) (into (map first) path))))]
        (or (some reach (map vector (sort-by nm/name-key (shape-kinds x)) (repeat [])))
            (some reach (sort-by (comp nm/name-key key) (stated-kinds kb x context))))))))

(defrecord EvaluableProver []                    ; arithmetic comparison, EDN-kind + string-shape check
  Prover
  (applicable? [_ kb goal context]
    (or
     ;; a literal's value kind is fixed, so its negation is computed too: (not (string 7))
     (negated-value-kind-goal? goal)
     (and (sequential? goal) (contains? evaluable-predicates (first goal))
          (case (first goal)
            integer
            ;; the unary kind check: one ground argument, of any EDN kind (a non-integer
            ;; simply yields no solution — which is what makes a failing `(integer ?x)`
            ;; necessary a sound negative witness for a string / symbol member).  A
            ;; quoted form is `ExpressionKindProver`'s: `(Quote 5)` denotes an integer.
            (and (= 1 (count (rest goal))) (ground? goal)
                 (nil? (quoted-form kb (second goal) context)))
            (string number boolean keyword character)
            ;; the other value kinds: one argument, and a literal value, since a symbol
            ;; or a compound could denote a value of the kind
            (literal-value-kind-goal? goal)
            matchesPattern
            ;; the binary string-shape check: two ground arguments.  A non-string subject
            ;; yields no solution, so a failing `(matchesPattern ?x p)` is a sound negative
            ;; witness the way `integer` is for a non-integer.
            (and (= 2 (count (rest goal))) (ground? goal))
            ;; lessThan / greaterThan: the variable-arity arithmetic comparisons
            (and (>= (count (rest goal)) 2)
                 (every? number? (rest goal)))))))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative for a ground goal: the arithmetic cannot be wrong about two numbers, nor
  ;; `integer?` about one term's EDN kind, nor a value-kind test about a literal, nor
  ;; `matchesPattern` about a string and a pattern.
  (completeness [_ _ _ _] 100)
  (solve [_ _ goal _]
    (let [args (rest goal)
          ok   (case (first goal)
                 not            (let [[k x] (second goal)] (not (literal-of-kind? k x)))
                 lessThan       (apply < args)
                 greaterThan    (apply > args)
                 integer        (integer? (first args))
                 (string number boolean keyword character)
                 (literal-of-kind? (first goal) (first args))
                 matchesPattern (let [[s p] args]
                                  (and (string? s) (string? p) (bounded-matches? p s)))
                 false)]
      (if ok [{}] []))))

(defn admits-position?
  "Does positive position `n` exist in a well-formed application of a relation with this arity
  shape?  `true` when it does, `false` when it does not, `nil` when the KB has not said.

  `admitsArgnum`, `checks/arg-position-problem` and `quality`'s position census all read it, so
  they cannot answer one position two ways.  `variable?` is whether the relation reads a chain
  of any length; `declared` is its exact declared arity or nil.  A variable-arity relation
  admits every positive position, a fixed-arity one one through its declared arity, and a
  relation with neither leaves the question open."
  [variable? declared n]
  (cond
    (not (and (integer? n) (pos? n))) false
    variable?                         true
    (integer? declared)               (<= n declared)
    :else                             nil))

(defrecord AdmitsArgnumProver []                 ; the position query over a relation's arity
  Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 'admitsArgnum (first goal))
         (= 2 (count (rest goal))) (ground? goal)   ; a ground relation and position
         (let [[p n] (rest goal)] (and (symbol? p) (integer? n)))))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative for a ground goal: the answer is computed from the relation's length,
  ;; inherited through `genl` included (`arity/relation-length`), and its `variable_arity`
  ;; release (`arity/released?`), each read the same at every context.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal _]
    (let [[p n] (rest goal)
          var   (arity/released? kb p)]
      (if (true? (admits-position? var (when-not var (:exact (arity/relation-length kb p))) n))
        [{}]
        []))))

;; ---- different: the unique-name assumption over the equality closure ----

;; An unmerged `indeterminate_term` member suspends the UNA for itself (docs/predall.md).
(defn- skolem-indeterminate? [kb term context]
  (and (nat-read/reified-nat-symbol? term)
       (boolean
        ;; 'SkolemFn is skolem/skolem-function's value, copied for the same cycle reason
        (some (fn [[_ b]] (let [e (get b '?e)]
                            (and (sequential? e) (= 'SkolemFn (first e)))))
              (res/matches-visible kb (list 'natFormula term '?e) context)))))

(defn- category-indeterminate? [kb term context]
  ;; a believed member of `indeterminate_term` or of any collection that genl-reaches it,
  ;; in ONE indexed point-read: `res/matches-visible` fans the functor over its genl-spec
  ;; closure, so a stored `(vague_kind term)` under `(genl vague_kind indeterminate_term)`
  ;; matches the `indeterminate_term` pattern already.  A membership scan beside this read
  ;; would decide nothing it does not and would walk every sentex naming the term on the
  ;; negative answer, which is the common one.
  (boolean (seq (res/matches-visible kb (list 'indeterminate_term term) context))))

(defn indeterminate-term?
  "Is `term` an unmerged **indeterminate term** in `context`: a skolem constant, read off
  its `SkolemFn` minting expression, or a believed member of the `indeterminate_term`
  category, subkinds included (docs/predall.md)?  Public for `vaelii.impl.predall`'s
  `predAllSpecified` audit, which asks the same question of a filler."
  [kb term context]
  (or (skolem-indeterminate? kb term context)
      (category-indeterminate? kb term context)))

(defn indeterminacy-supports
  "The handles of the stored sentexes, in any context, that make `term` an indeterminate
  term where they are visible: its `SkolemFn` minting expression and its memberships of
  `indeterminate_term` or a subkind (`indeterminate-term?`'s two readings), sorted."
  [kb term]
  (into (sorted-set)
        (map first)
        (concat (filter (fn [[_ b]] (let [e (get b '?e)] (and (sequential? e) (= 'SkolemFn (first e)))))
                        (when (nat-read/reified-nat-symbol? term)
                          (res/matches-visible kb (list 'natFormula term '?e) '?ctx)))
                (res/matches-visible kb (list 'indeterminate_term term) '?ctx))))

(defn- pairwise-distinct?
  "Do no two of `args` share an equivalence class as `context` sees the merges, with no
  argument an unmerged `indeterminate_term`?  `(different A A)` fails on the `=` arm
  without reading the closure.  Compound arguments normalize recursively
  (`res/representative-term`).

  The exemption is read after the pairwise check, so a goal that fails on a repeat reads
  no `indeterminate_term`: `(different A A)` measures 14.6 us/op against 19.4 for the
  other order, over a KB holding core.txt and no indeterminate term."
  [kb context args]
  (let [vis     (res/visible-supporter-fn kb context)
        rep     #(res/representative-term kb vis %)
        v       (vec args)
        exempt? (fn [t] (and (= (rep t) t) (indeterminate-term? kb t context)))]
    (and (every? (fn [[a b]] (not (or (= a b) (= (rep a) (rep b)))))
                 (for [i (range (count v)), j (range (inc i) (count v))]
                   [(nth v i) (nth v j)]))
         (not-any? exempt? v))))

(defrecord DifferentProver []
  Prover
  ;; Ground only: inapplicable to an open goal, so `plan` shows no prover for one rather
  ;; than an empty answer (docs/equality.md, "The unique-name assumption survives").
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 'different (first goal))
         (>= (count (rest goal)) 2)
         (every? ground? (rest goal))))
  (est-bindings [_ _ _ _] 1)                    ; ground test: it holds or it does not
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative: `different` is never stored (`wff` refuses it).
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (if (pairwise-distinct? kb context (rest goal)) [{}] [])))

;; ---- sameAs / equals: the equality closure, read as a relation ----------

(def ^:private closure-equations
  "The equations the closure answers as a relation: reflexive, symmetric and transitive
  over the partition.  `rewriteOf` is not here.  It is directional, and the goal
  `(rewriteOf P D)` is answered by the stored edge as spelled (`res/goal-held-as-spelled?`)."
  '#{sameAs equals})

(defn- scoped-equiv-class
  "`term`'s equivalence class as `visible?` sees the merges: the global class when the read
  is unscoped or nothing merged `term`, else the scoped election (`tax/scoped-class`), since
  an invisible edge can split a class."
  [kb visible? term]
  (let [tx (reasoning/taxonomy kb)]
    (if (and visible? (tax/merged? tx term))
      (first (tax/scoped-class tx term visible?))
      (tax/equiv-class tx term))))

(defn- terms-equal-in?
  "Do ground terms `a` and `b` reach one normal form as `visible?` sees the merges and the
  schematic equations?  Each side is a **term**, so it takes the congruence walk and then
  `rewrite/normalize` at its own root; `res/normal-form` reads its argument as a sentence
  and would leave the root of a term such as `(fatherOf (fatherOf Tom))` unrewritten."
  [kb visible? a b]
  (or (= a b)
      (let [rules (res/rewrite-rules-in kb visible?)
            nf    #(rewrite/normalize rules (res/representative-term kb visible? %))]
        (= (nf a) (nf b)))))

(defrecord EqualityProver []
  Prover
  ;; A ground goal, or a symbol beside a variable; the other shapes are left to the
  ;; stored equations (docs/equality.md, "Answering an equation").
  (applicable? [_ _ goal _]
    (and (binary? goal) (contains? closure-equations (first goal))
         (let [[_ a b] goal]
           (or (and (ground? a) (ground? b))
               (and (symbol? a) (not (pvar? a)) (pvar? b))
               (and (pvar? a) (symbol? b) (not (pvar? b)))))))
  (est-bindings [_ kb goal context]
    (let [[_ a b] goal]
      (if (and (ground? a) (ground? b))
        1
        (count (scoped-equiv-class kb (res/visible-supporter-fn kb context)
                                   (if (ground? a) a b))))))
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative over the believed equations, asserted or derived, scoped as
  ;; `FactProver` is.  A backward rule concluding an equation is `sole-prover`'s question.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [[_ a b] goal
          vis (res/visible-supporter-fn kb context)]
      (cond
        (and (ground? a) (ground? b))
        (if (terms-equal-in? kb vis a b) [{}] [])
        (ground? a) (map (fn [t] {b t}) (sort (scoped-equiv-class kb vis a)))
        :else       (map (fn [t] {a t}) (sort (scoped-equiv-class kb vis b)))))))

(defn- structure-kind
  "The kind `sx/structure-constructors` names for `t`, a ground application of a structure
  constructor, else nil (docs/nat.md, \"A data structure is a structural term\").  A ground
  application holds no rest variable, so it is never dotted."
  [t]
  (when (and (seq? t) (seq t) (ground? t))
    (get sx/structure-constructors (first t))))

(defn- entry-parts
  "The key and value of `(EntryFn k v)`, else nil."
  [e]
  (when (and (seq? e) (= 'EntryFn (first e)) (= 3 (count e))) (rest e)))

(defn- structure-items
  "The arguments of a structure of `kind` as the store spells it, a set's or map's repeats
  dropped by identity, so a KB that declares no mark on the constructor still reads one."
  [kb kind s]
  (let [items (rest (sx/canonical-subterm s (res/store-marks kb)))]
    (if (#{:set :map} kind) (distinct items) items)))

(defn- same-term-fn
  "`terms-equal-in?` over one read of the rewrite rules, each side's normal form computed
  once."
  [kb context]
  (let [vis   (res/visible-supporter-fn kb context)
        rules (delay (res/rewrite-rules-in kb vis))
        nf    (memoize #(rewrite/normalize @rules (res/representative-term kb vis %)))]
    (fn [a b] (or (= a b) (= (nf a) (nf b))))))

(defn- same-classes
  "`xs` grouped into classes of `same?` items, each a vector in the order `xs` holds them."
  [same? xs]
  (reduce (fn [cs t] (if-let [i (first (keep-indexed #(when (same? t (first %2)) %1) cs))]
                       (update cs i conj t)
                       (conj cs [t])))
          [] xs))

(defn- match-item
  "Bindings extending `b` under which goal argument `x` is item `t`: by `same?` when `x` is
  ground, by unification otherwise."
  [same? x t b]
  (if (ground? x) (when (same? x t) b) (res/unify x t b)))

(defn- count-binding
  "Bindings extending `b` under which goal argument `n` is the count `c`."
  [n c b]
  (cond (pvar? n)                 (assoc b n c)
        (and (number? n) (== n c)) b))

(defn- solve-structure-relation
  "The answers to a structure relation over a ground structure, every element, entry or key
  read in `context`'s normal form: an open element binds one of each class, a set's and a
  map's count is its classes, and a map whose keys merge there answers each value."
  [kb [f :as goal] context]
  (let [s     (last goal)
        kind  (structure-kind s)
        items (structure-items kb kind s)
        same? (same-term-fn kb context)
        reps  (delay (map first (same-classes same? items)))
        times (fn [e] (if (#{:list :multiset} kind)
                        (count (filter #(same? e %) items))
                        (if (some #(same? e %) items) 1 0)))]
    (case f
      elementOf
      (let [[_ x] goal]
        (if (ground? x)
          (if (some #(same? x %) items) [{}] [])
          (keep #(res/unify x % {}) @reps)))
      cardinalityOf
      (let [c (if (#{:list :multiset} kind) (count items) (count @reps))]
        (if-let [b (count-binding (second goal) c {})] [b] []))
      multiplicityOf
      (let [[_ n x] goal]
        (if (ground? x)
          (if-let [b (count-binding n (times x) {})] [b] [])
          (keep (fn [e] (when-let [b (res/unify x e {})]
                          (count-binding (res/substitute n b) (times e) b)))
                @reps)))
      valueAt
      (let [[_ v k] goal
            pairs   (case kind
                      :map  (keep entry-parts @reps)
                      :list (map-indexed (fn [i t] [(inc i) t]) items)
                      nil)]
        (for [[pk pv] pairs
              :let  [b (match-item same? k pk {})]
              :when b
              :let  [b (match-item same? (res/substitute v b) pv b)]
              :when b]
          b)))))

(defn- split-rest
  "`[explicit rest-var]` of a corresponding predicate's element arguments: the arguments
  before a dot and the variable after it, or all of them and nil."
  [args]
  (if (sx/dotted? args) [(sx/positional args) (last args)] [args nil]))

(defn- positional-matches
  "Bindings under which patterns `xs`, then rest variable `r` if any, are a list's or an
  entry's `items` in order, a ground pattern compared by `same?`."
  [same? items xs r]
  (let [n (count xs)]
    (or (when (if r (<= n (count items)) (= n (count items)))
          (when-let [b (reduce (fn [b [x t]] (or (match-item same? (res/substitute x b) t b) (reduced nil)))
                               {} (map vector xs items))]
            (if r (some-> (res/unify r (apply list (drop n items)) b) vector) [b])))
        [])))

(defn- commuting-matches
  "Bindings under which patterns `xs` name items of a multiset, set or map, compared by
  `same?`: a multiset's patterns take one occurrence each, and a set's or map's may name one
  element twice.  Without rest variable `r` they name every item; with it, `r` binds the
  items none names, in the store's order.  `v` open patterns answer up to `m^v` ways."
  [same? kind items xs r]
  (let [set?    (#{:set :map} kind)
        classes (if set? (same-classes same? items) (mapv vector items))
        go      (fn go [ps used b]
                  (if (empty? ps)
                    [[used b]]
                    (let [p (res/substitute (first ps) b)]
                      (mapcat (fn [i]
                                (when (or set? (not (used i)))
                                  (let [c (nth classes i)]
                                    (if (ground? p)
                                      (when (same? p (first c)) (go (rest ps) (conj used i) b))
                                      (mapcat #(some->> (res/unify p % b) (go (rest ps) (conj used i)))
                                              (distinct c))))))
                              (range (count classes))))))]
    (distinct
     (for [[used b] (go (sort-by (complement ground?) xs) #{} {})
           :let  [left (remove used (range (count classes)))]
           :when (or r (empty? left))
           :let  [b (if r (res/unify r (apply list (map #(first (nth classes %)) left)) b) b)]
           :when b]
       b))))

(defn- solve-structure-predicate
  "The answers to a corresponding predicate: the canonical structure its ground elements
  build, or each way its element patterns, a rest after them binding what they leave, name
  the elements of its ground structure in `context`'s normal form."
  [kb [f s & args] context]
  (let [ctor   (get sx/structure-predicates f)
        marks  (res/store-marks kb)
        [xs r] (split-rest args)
        xs     (map #(if (ground? %) (sx/canonical-subterm % marks) %) xs)]
    (cond
      (pvar? s)
      [{s (sx/canonical-subterm (apply list ctor args) marks)}]

      (not (and (seq? s) (= ctor (first s))))
      []

      :else
      (let [same? (same-term-fn kb context)
            kind  (structure-kind s)]
        (if (or (= 'EntryFn ctor) (= :list kind))
          (positional-matches same? (rest (sx/canonical-subterm s marks)) xs r)
          (commuting-matches same? kind (structure-items kb kind s) xs r))))))

(defn- structure-goal?
  "Is `goal` one `StructureProver` answers: a structure relation of its arity over a ground
  structure, or a corresponding predicate whose structure is ground, or whose elements are
  ground and undotted?"
  [goal]
  (and (seq? goal) (symbol? (first goal))
       (let [[f & args] goal]
         (cond
           (contains? sx/structure-relations f)
           (and (= ({'elementOf 2 'cardinalityOf 2} f 3) (count args))
                (some? (structure-kind (last args))))

           (contains? sx/structure-predicates f)
           (let [[s & es] args
                 [_ r]    (split-rest es)]
             (and (some? s)
                  (or (not= 'entryOf f) (= 3 (count args)))
                  (if (pvar? s)
                    (and (nil? r) (every? ground? es))
                    (and (ground? s) (or (nil? r) (pvar? r))))))
           :else false))))

(defrecord StructureProver []
  Prover
  (applicable? [_ _ goal _] (structure-goal? goal))
  (est-bindings [_ _ goal _]
    (if (contains? sx/structure-relations (first goal)) (max 1 (dec (count (last goal)))) 1))
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (if (contains? sx/structure-relations (first goal))
      (solve-structure-relation kb goal context)
      (solve-structure-predicate kb goal context))))

;; ---- evaluate: symbolic computation -------------------------------------
;; (evaluate ?result <expr>) binds ?result to the value of a symbolic expression,
;; e.g. (evaluate ?sum (+ 1 2)) => ?sum=3.  A safe whitelist evaluator, not `eval`.

(defn- expt [b e]                                  ; integer-exact for a non-negative integer exponent
  (if (and (integer? e) (not (neg? e))) (reduce * 1 (repeat e b)) (Math/pow b e)))

(def ^:private eval-ops
  {'+ + '- - '* * '/ / 'mod mod 'quot quot 'rem rem 'inc inc 'dec dec
   'min min 'max max 'abs abs 'expt expt})

(def ^:private eval-fail ::fail)

(defn- eval-expr [expr]
  (cond
    (number? expr) expr
    (and (sequential? expr) (contains? eval-ops (first expr)))
    (let [args (map eval-expr (rest expr))]
      (if (some #(= eval-fail %) args)
        eval-fail
        (try (apply (eval-ops (first expr)) args)
             (catch Exception _ eval-fail))))       ; div-by-zero, arity, etc. → no solution
    :else eval-fail))                               ; unbound var or unknown operator

(defrecord EvaluateProver []
  Prover
  (applicable? [_ _ goal _]
    (binary-pred? goal 'evaluate))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  ;; The only way to compute an expression.  That `evaluate` is an ordinary functor a
  ;; KB may also declare about is `sole-prover`'s question.
  (completeness [_ _ _ _] 100)
  (solve [_ _ goal _]
    (let [[_ result expr] goal, v (eval-expr expr)]
      (cond
        (= eval-fail v) []
        (pvar? result)  [{result v}]
        :else           (if (= result v) [{}] [])))))

;; ---- user-registered evaluatable predicates / functions -----------------
;; `EvaluableProver` and `EvaluateProver` above are the two shapes of a *computed*
;; answer — a check over ground arguments, and a value bound into an output slot — each
;; hand-written for one built-in functor.  `EvaluatableFn` is the same two shapes made
;; generic: it wraps a plain Clojure fn the caller supplies, so registering a
;; compute-a-truth predicate or a compute-a-value function is one call
;; (`vaelii.core/add-evaluatable`) rather than a hand-written five-method record.  The
;; wrapped fn is a real fn *value*, never `clojure.core/eval` of KB data — the same
;; safe-evaluation posture `EvaluateProver` keeps.

(defn- fn-arities
  "The fixed `invoke` arities `f` declares, as a set of ints — empty for a purely
  variadic fn, whose arity reflection cannot read.  An evaluatable dispatches on its
  predicate's name **and** this arity (`applicable?`), so a wrapped fn answers only the
  goal shape it can actually take, and a KB that also declares the same functor at some
  other arity is left to the other provers.  A caller whose fn is variadic sets `:arity`
  instead."
  [f]
  (into #{}
        (comp (filter #(= "invoke" (.getName ^java.lang.reflect.Method %)))
              (map #(.getParameterCount ^java.lang.reflect.Method %)))
        (.getDeclaredMethods (class f))))

(defn- out-index
  "The 0-based position of the output slot among a goal's `n` arguments, from a `:result`
  spec: `:first` → 0, `:last` → n-1, an integer → itself.  The result-binding shape reads
  the slot here and passes the rest to the wrapped fn."
  [result n]
  (case result
    :first 0
    :last  (dec n)
    (long result)))

(def deferred-est
  "The `est-bindings` an evaluatable reports while its inputs are unbound, and any prover
  whose answer to an open argument is not complete.  An evaluatable computes from ground
  inputs and enumerates nothing, so on unbound inputs it can neither answer nor prune — the
  most *unselective* a literal can be, and reported as such so the join planner
  (`vaelii.impl.plan`, through `est-goal`) runs a generator that binds those inputs first
  and the computation lands with everything ground.  It is `plan/unbounded`, which the
  unranked order also reads: a literal an `:est-override` costs at it waits for its
  binders with the ranking off."
  plan/unbounded)

(defrecord ExpressionKindProver []          ; what kind of expression a quoted form is
  Prover
  (applicable?  [_ kb goal context]
    (or (expression-kind-goal? kb goal context)
        ;; open, so the join planner reads `deferred-est` and binds it first; only a
        ;; support functor, the one a re-join plans
        (and (sequential? goal) (= 2 (count goal))
             (contains? expression-kind-predicates (first goal)) (sx/variable? (second goal))
             (tax/genl? (reasoning/taxonomy kb) (first goal) 'expression context))))
  (est-bindings [_ _ goal _] (if (sx/variable? (second goal)) deferred-est 1))
  (cost         [_ _ _ _] :lookup)
  ;; 50, not 100: a stored membership of a quoted form answers beside this, and a kind
  ;; this does not decide (a predication whose head the KB states nothing of) is a
  ;; contribution of none rather than a "no"
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (if (expression-kind-support kb goal context) [{}] []))
  SupportingProver
  (support-functors [_] expression-kind-predicates)
  ;; the lattice reaches a kind through `genl` edges and the declarations that install them
  (support-sources  [_] tax/edge-installing-functors)
  (solve-with-support [_ kb goal context]
    (if-let [sup (expression-kind-support kb goal context)] [[{} sup]] [])))

(defn- nonempty-type
  "The type `(nonempty C)` asks about, `C` a constant symbol, or nil for any other goal."
  [goal]
  (when (and (sequential? goal) (= 2 (count goal)) (= 'nonempty (first goal)))
    (let [c (second goal)]
      (when (and (symbol? c) (not (sx/variable? c))) c))))

(defn nonempty-witness
  "The handles a believed member of the type `c` seen from `context` rests on, as a set,
  or nil when `c` has none: the first in content order of the believed memberships `(S x)`
  that `res/matches-visible` answers for `(c ?x)`, `S` being `c` or a subtype, and for a
  subtype the first believed supporter of each `genl` edge on one path from `S` up to `c`
  (`tax/genl-path-edges`).  A member whose path has an edge with no believed supporter
  seen from `context` is passed over.  Reads one count per subtype of `c` first
  (`reads/stored-count-with-functor`), and the visible extent of `c` in full when one is
  positive."
  [kb c context]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        tx    (reasoning/taxonomy kb)
        ckey  (fn [h] (let [r (p/get-sentex recs h)] [(sx/sentence-of r) (:context r)]))
        least (fn [hs] (nm/min-by-content-key ckey (filter #(jtms/in? tms %) hs)))
        route (fn [h]
                (let [s (nm/functor (sx/sentence-of (p/get-sentex recs h)))]
                  (if (= s c)
                    #{h}
                    (when-let [es (tax/genl-path-edges tx s c)]
                      (let [ws (mapv (fn [[a b]] (least (tax/genl-edge-supporters tx a b context))) es)]
                        (when (every? some? ws) (into #{h} ws)))))))
        hs    (when (some #(pos? (reads/stored-count-with-functor (:index kb) %)) (tax/specs tx c context))
                (into [] (comp (map first) (distinct) (filter #(jtms/in? tms %)))
                      (res/matches-visible kb (list c '?x) context false)))]
    (when (seq hs)
      (or (route (nm/min-by-content-key ckey hs))
          (some route (nm/sort-by-content-key ckey hs))))))

(defrecord NonemptyProver []
  Prover
  (applicable?  [_ _ goal _]
    (and (sequential? goal) (= 2 (count goal)) (= 'nonempty (first goal))))
  (est-bindings [_ _ goal _] (if (nonempty-type goal) 1 deferred-est))
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (if (some-> (nonempty-type goal) (as-> c (nonempty-witness kb c context))) [{}] []))
  SupportingProver
  (support-functors [_] #{'nonempty})
  (support-sources  [_] #{})
  (solve-with-support [_ kb goal context]
    (if-let [hs (some-> (nonempty-type goal) (as-> c (nonempty-witness kb c context)))]
      [[{} hs]]
      [])))

;; ---- result types: what a function application is ------------------------------

(defn- result-type-goal?
  "Is `goal` `(k x)`, `k` a symbol and `x` a ground application of a named function, on
  a KB that declares a result type?"
  [kb goal]
  (and (sequential? goal) (= 2 (count goal))
       (let [[k x] goal]
         (and (symbol? k) (not (sx/variable? k))
              (seq? x) (symbol? (first x)) (not (sx/variable? (first x)))
              (not (contains? formula-heads (first x)))
              (ground? x)
              (nat-read/any-result-declarations? kb)))))

(defrecord ResultTypeProver []              ; (k (F a…)) read off F's declared result types
  Prover
  (applicable?  [_ kb goal _] (result-type-goal? kb goal))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  ;; 50, not 100: a function that declares no result is open-world, so an empty answer
  ;; is a contribution of none rather than a "no"
  (completeness [_ _ _ _] 50)
  (solve [_ kb [k x] context]
    (let [tax (reasoning/taxonomy kb)]
      (if (some #(tax/genl? tax % k context) (nat-read/visible-result-types kb x context)) [{}] []))))

;; ---- argN: a position inside a written formula --------------------------------

(defn- arg-position-goal?
  "Is `goal` `(argN term n formula)`?"
  [goal]
  (and (sequential? goal) (= 'argN (first goal)) (= 4 (count goal))))

(defn- arg-positions
  "The solutions of the goal `(argN term n formula)` read off how the formula is written,
  as `[bindings handles]` pairs: one per position `i` of the compound, 0 its operator,
  whose element `e` matches `term` (a variable binds to `e`, any other term equals it) and
  whose `i` matches `n` the same way.  The compound is `formula` as written, or the form a
  quoted `formula` names (`quoted-form`): `(Quote x)` names `x`, and a reified constant
  names the form its `natFormula` statement quotes, whose handle every pair carries.  A
  variable at a position is a hole and answers nothing, so a variable operator answers no
  position 0, and an open formula answers the positions of the pattern as written rather
  than of its instances.  `[]` when the compound is not a non-empty one."
  [kb [_ term n formula] context]
  (let [[x hs] (if-let [[_ x hs] (quoted-form kb formula context)] [x hs] [formula []])]
    (if (and (sequential? x) (seq x))
      (into []
            (keep-indexed
             (fn [i e]
               (when (and (not (sx/variable? e))
                          (or (sx/variable? n) (= n i))
                          (or (sx/variable? term) (= term e)))
                 [(cond-> {}
                    (sx/variable? term) (assoc term e)
                    (sx/variable? n)    (assoc n i))
                  hs])))
            x)
      [])))

(defrecord ArgPositionProver []             ; (argN term n formula), read off the formula
  Prover
  ;; Open in `formula` too, so the join planner reads `deferred-est` and binds the
  ;; formula first; `solve` answers nothing until it is bound.
  (applicable?  [_ _ goal _] (arg-position-goal? goal))
  (est-bindings [_ _ goal _]
    (let [f (nth goal 3)]
      (if (sequential? f) (count f) deferred-est)))
  (cost         [_ _ _ _] :lookup)
  ;; 50, not 100: a stored argN fact answers beside this
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context] (mapv first (arg-positions kb goal context)))
  SupportingProver
  ;; A formula written out, or quoted by a quoting function, rests on no statement: the
  ;; firing rests on the antecedent that bound it (`chain/solve-computed`).  A reified
  ;; constant rests on its `natFormula` statement.
  (support-functors [_] #{'argN})
  (support-sources  [_] #{})
  (solve-with-support [_ kb goal context] (arg-positions kb goal context)))

(defrecord EvaluatableFn [pred f arities result cost-tier complete]
  Prover
  ;; Two shapes, one record, split on whether `result` names an output slot: a *check*
  ;; predicate (no `result`, like `EvaluableProver`) and a *result-binding* function (an
  ;; output slot the value binds, like `EvaluateProver`).  `applicable?` matches the
  ;; functor and arity but **not** groundness — a join reaches an evaluatable with its
  ;; inputs still unbound, and refusing it there would drop the literal from the plan
  ;; rather than defer it; `est-bindings` is what carries the defer-me signal, and `solve`
  ;; is what holds the answer back until the inputs are ground.
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= pred (first goal))
         (let [n (count (rest goal))]
           (if result
             (let [i (out-index result n)]
               (and (<= 0 i) (< i n) (or (empty? arities) (contains? arities (dec n)))))
             (or (empty? arities) (contains? arities n))))))
  (est-bindings [_ _ goal _]
    (let [args   (vec (rest goal))
          inputs (if result
                   (keep-indexed (fn [j a] (when (not= j (out-index result (count args))) a)) args)
                   args)]
      (if (every? ground? inputs) 1 deferred-est)))  ; a computed answer is one, or none
  (cost         [_ _ _ _] cost-tier)
  (completeness [_ _ _ _] complete)
  (solve [_ _ goal _]
    (let [args (vec (rest goal))]
      (if result
        (let [i      (out-index result (count args))
              out    (nth args i)
              inputs (keep-indexed (fn [j a] (when (not= j i) a)) args)]
          (if-not (every? ground? inputs)
            []                                    ; inputs not yet bound — nothing to compute
            ;; A thrown fn — arity, type, div-by-zero — reads as no solution, never as a
            ;; crash of the query, matching `EvaluateProver`'s `eval-fail` arm.
            (let [v (try (apply f inputs) (catch Exception _ ::fail))]
              (cond
                (= ::fail v) []
                (pvar? out)  [{out v}]
                :else        (if (= out v) [{}] [])))))
        (if (and (every? ground? args)
                 (try (boolean (apply f args)) (catch Exception _ false)))
          [{}] [])))))

(defn evaluatable
  "A `Prover` wrapping the plain Clojure fn `f` as the evaluatable predicate/function
  `pred`, the value `vaelii.core/add-evaluatable` registers.  It answers by computing, in one
  of two shapes:

  - **check** (no `:result`): `(pred a …)` holds when `f` applied to the ground arguments
    returns truthy.  Every argument must be ground.
  - **result-binding** (`:result` names an output slot): `(pred … ?out …)` binds `?out` to
    `(f <the other, ground arguments>)`.  A ground output slot is checked against the value.

  `opts` (a map, or nil):

  - `:result`: `:first`, `:last`, or a 0-based index; its presence selects result-binding.
  - `:arity`: the fn's input count (an int or a set), derived by reflection when omitted; a
    variadic fn needs it stated.
  - `:cost`: a `cost-tiers` keyword, `:lookup` by default.
  - `:completeness`: 0..100, 100 by default (`sole-prover` still guards it).  Use 50 for a
    predicate a KB also stores facts under.

  Registered through `add-prover`, so it answers `ask` / `query` goals and discharges a
  conjunct or antecedent in a `query` with a `:max-depth`.  Forward materialization reaches
  it through `vaelii.impl.chain/deferred-antecedent?`.  The DFS `prove` does not, since its
  leaf is the stored facts (docs/inference.md, query-engine section)."
  ([pred f] (evaluatable pred f nil))
  ([pred f {:keys [result arity] cost-tier :cost complete :completeness
            :or {cost-tier :lookup complete 100}}]
   (->EvaluatableFn pred f
                    (cond (integer? arity) #{(long arity)}
                          (coll? arity)    (set (map long arity))
                          :else            (fn-arities f))
                    result cost-tier complete)))

(defn evaluatable-preds
  "The set of predicate functors a KB has registered as evaluatables through
  `vaelii.core/add-evaluatable` — the `EvaluatableFn` provers in its registry.

  Forward chaining reads this to treat a registered evaluatable the way it treats the
  built-in `vaelii.impl.sentex/deferred-predicates`: **computed** from the bindings the
  other antecedents produced, through the registry, never looked up as a stored fact.
  The built-ins are a static set because they are always present; the evaluatables are
  per-KB, so this set is read off the KB's live registry.  Empty for a KB with no
  registered evaluatables — the default registry has none."
  [kb]
  (into #{} (comp (filter #(instance? EvaluatableFn %)) (map :pred)) (registry kb)))

(defn- input-vars
  "The variables of `goal` prover `p` reads to compute an answer: every argument but an
  `EvaluatableFn`'s `:result` slot, `argN`'s formula, and every argument for any other
  prover.  The rest of `goal`'s variables are the ones the answer binds."
  [p goal]
  (let [args (vec (rest goal))]
    (sx/form-variables
     (cond
       (and (instance? EvaluatableFn p) (:result p))
       (let [i (out-index (:result p) (count args))]
         (keep-indexed (fn [j a] (when (not= j i) a)) args))
       (and (instance? ArgPositionProver p) (arg-position-goal? goal)) [(nth goal 3)]
       :else args))))

(defn- est-under
  "The estimate `e` the applicable provers `ps` gave for `goal` as written, read with the
  variables in `bound` bound: `deferred-est` becomes 1, the one answer or none a
  computation gives, once `bound` holds every variable the provers among `ps` that report
  `deferred-est` read (`input-vars`), and is `e` otherwise.  Each `:est-override` below
  reads a goal through this, so `plan/order` runs a computed literal once its inputs are
  bound, ahead of a literal its output binds."
  [e ps kb goal context bound]
  (if (and (= deferred-est e) (sequential? goal))
    (let [bound (if (set? bound) bound (set bound))
          ds    (filterv #(= deferred-est (est-bindings % kb goal context)) ps)]
      (if (and (seq ds) (every? #(every? bound (input-vars % goal)) ds)) 1 e))
    e))

(defn evaluatable-est-override
  "An `:est-override` for `vaelii.impl.plan/order` that costs only `preds`, a KB's registered
  evaluatable functors (`evaluatable-preds`), and returns nil for every other goal.  A goal
  costs what its `EvaluatableFn`'s `est-bindings` gives under the plan's bindings
  (`est-under`): `deferred-est` while an input is unbound, else one, so the binders run first.

  Forward chaining (`vaelii.impl.chain/planned-join`) plans with this so a registered
  evaluatable antecedent follows its binders, as the built-in `deferred-predicates` do by
  canonical order.  Scoped to evaluatables because forward chaining's leaf is the stored facts
  (`*matcher*`).  Nil when `preds` is empty."
  [kb preds]
  (when (seq preds)
    (let [ps (filterv #(and (instance? EvaluatableFn %) (contains? preds (:pred %))) (registry kb))]
      (fn [goal bound]
        (when (and (sequential? goal) (seq goal) (contains? preds (first goal)))
          (let [app (filterv #(applicable? % kb goal '?ctx) ps)
                e   (cond (seq app)     (reduce max (map #(est-bindings % kb goal '?ctx) app))
                          (ground? goal) 1
                          :else          deferred-est)]
            (est-under e app kb goal '?ctx bound)))))))

;; ---- a prover built from plain fns (`vaelii.core/prover`) -----------------

(def ^:private fn-prover-readings
  "What each per-goal reading of a `fn-prover` must be, as `{key [what ok?]}`.  A constant
  is checked once, at construction; a fn's return is checked at each call."
  {:est-bindings ["a non-negative number" #(and (number? %) (not (neg? (double %))))]
   :cost         [(str "one of " (str/join ", " cost-tiers)) (set cost-tiers)]
   :completeness ["an integer from 0 to 100" #(and (integer? %) (<= 0 % 100))]})

(defn- fn-prover-refusal [k what v]
  (ex-info (str "prover " k " must be " what ", got " (pr-str v))
           {:type :unknown-option :mismatch :bad-value :option k :value v}))

(defn- a-fn? [x] (or (fn? x) (var? x)))

(defn- checked-reading [k v]
  (let [[what ok?] (fn-prover-readings k)]
    (if (ok? v) v (throw (fn-prover-refusal k what v)))))

(defn- fn-reading
  "The reading `r` gives for `goal`: `r` itself when it is a constant (a number or a cost
  keyword, checked at construction), else its return, checked."
  [k r kb goal context]
  (if (or (number? r) (keyword? r)) r (checked-reading k (r kb goal context))))

(defn- default-est
  "`est-bindings` for a spec that names none: one answer for a ground goal, `deferred-est`
  for an open one, so the join planner binds the arguments first."
  [_kb goal _context]
  (if (ground? goal) 1 deferred-est))

(defn- checked-bindings [b]
  (if (map? b) b (throw (fn-prover-refusal :solve "a seq of binding maps" b))))

(defn- checked-support-answer [a]
  (if (and (sequential? a) (= 2 (count a)) (map? (first a))
           (coll? (second a)) (every? integer? (second a)))
    a
    (throw (fn-prover-refusal :solve-with-support
                              (str "a seq of [bindings support] pairs, bindings a map and support"
                                   " a collection of sentex handles")
                              a))))

(defrecord FnProver [applicable-fn solve-fn est cost-of complete]
  Prover
  (applicable?  [_ kb goal context] (boolean (applicable-fn kb goal context)))
  (est-bindings [_ kb goal context] (fn-reading :est-bindings est kb goal context))
  (cost         [_ kb goal context] (fn-reading :cost cost-of kb goal context))
  (completeness [_ kb goal context] (fn-reading :completeness complete kb goal context))
  (solve [_ kb goal context] (map checked-bindings (solve-fn kb goal context))))

(defrecord SupportingFnProver [applicable-fn support-fn est cost-of complete functors sources]
  Prover
  (applicable?  [_ kb goal context] (boolean (applicable-fn kb goal context)))
  (est-bindings [_ kb goal context] (fn-reading :est-bindings est kb goal context))
  (cost         [_ kb goal context] (fn-reading :cost cost-of kb goal context))
  (completeness [_ kb goal context] (fn-reading :completeness complete kb goal context))
  ;; the bindings of `solve-with-support`, so the protocol's first obligation holds by
  ;; construction rather than by a second fn agreeing with the first
  (solve [this kb goal context] (map first (solve-with-support this kb goal context)))
  SupportingProver
  (support-functors [_] functors)
  (support-sources  [_] sources)
  (solve-with-support [_ kb goal context]
    (map checked-support-answer (support-fn kb goal context))))

(def ^:private fn-prover-keys
  "The keys `fn-prover` reads."
  #{:applicable? :solve :solve-with-support :support-functors :support-sources
    :est-bindings :cost :completeness})

(defn- check-symbol-set! [k v]
  (when-not (and (set? v) (every? symbol? v))
    (throw (fn-prover-refusal k "a set of predicate symbols" v))))

(defn fn-prover
  "The `Prover` `vaelii.core/prover` builds from `spec`, a map of plain fns and constants;
  the refusals and defaults are that fn's contract.  A spec with `:solve-with-support`
  builds a `SupportingFnProver`, whose `solve` is the bindings of `:solve-with-support`;
  one with `:solve` builds a `FnProver`, which implements `Prover` alone.  Each answer is
  checked as it is realized."
  [spec]
  (opts/check! spec fn-prover-keys "prover"
               "A key nothing reads takes the default in silence.")
  (let [{app :applicable? sv :solve sws :solve-with-support fs :support-functors
         srcs :support-sources est :est-bindings c :cost done :completeness
         :or {est default-est c :compute done 50}} spec]
    (cond
      (nil? app)
      (throw (ex-info "prover needs :applicable?, a fn of [kb goal context]"
                      {:type :unknown-option :mismatch :missing-value :option :applicable?}))
      (not (a-fn? app))
      (throw (fn-prover-refusal :applicable? "a fn of [kb goal context]" app))
      (and sv sws)
      (throw (ex-info (str "prover takes :solve or :solve-with-support, not both: the solutions"
                           " of a supporting prover are the bindings of :solve-with-support")
                      {:type :unknown-option :mismatch :conflict
                       :unknown [:solve :solve-with-support]}))
      (not (or sv sws))
      (throw (ex-info "prover needs :solve or :solve-with-support, a fn of [kb goal context]"
                      {:type :unknown-option :mismatch :missing-value :option :solve}))
      (not (a-fn? (or sv sws)))
      (throw (fn-prover-refusal (if sv :solve :solve-with-support)
                                "a fn of [kb goal context]" (or sv sws))))
    (doseq [[k r] [[:est-bindings est] [:cost c] [:completeness done]]]
      (when-not (a-fn? r) (checked-reading k r)))
    (if sws
      (let [missing (filterv #(not (contains? spec %)) [:support-functors :support-sources])]
        (when (seq missing)
          (throw (ex-info (str "prover with :solve-with-support needs " (str/join " and " missing)
                               ": what it answers with support, and what it reads to answer")
                          {:type :unknown-option :mismatch :missing-companion :missing missing})))
        (check-symbol-set! :support-functors fs)
        (check-symbol-set! :support-sources srcs)
        (when (empty? fs)
          (throw (fn-prover-refusal :support-functors "a non-empty set of predicate symbols" fs)))
        (->SupportingFnProver app sws est c done fs srcs))
      (let [given (filterv #(contains? spec %) [:support-functors :support-sources])]
        (when (seq given)
          (throw (ex-info (str "prover reads " (str/join " and " given)
                               " only beside :solve-with-support")
                          {:type :unknown-option :mismatch :missing-companion
                           :missing [:solve-with-support]})))
        (->FnProver app sv est c done)))))

;; ---- quantity / measure comparison (measure-evaluating) --------------------
;; A measure is a structural NAT — `(QuantityFn N Unit)` (a point) or
;; `(QuantityIntervalFn Lo Hi Unit)` (an interval) — an `unreifiable_function`
;; application that stays *structural* so its magnitude and unit are readable.  This
;; prover normalizes two ground measures against the KB's `dimensionOf` /
;; `conversionFactor` table and compares them.  It never asserts or stores anything, and
;; it is deliberately **not** the equality closure — `sameQuantity` is a *computed*
;; result, and the closure refuses numbers and compounds outright.  See docs/quantity.md.

(def measure-comparisons
  "The measure-comparison predicates `QuantityProver` answers — check-only over two
  ground measures, never stored (declared in `measure.txt`, computed here)."
  '#{sameQuantity quantityLessThan quantityGreaterThan
     quantityLessThanOrEqual quantityGreaterThanOrEqual})

(def ^:dynamic *quantity-tolerance*
  "Absolute tolerance for measure equality.  Cross-unit normalization multiplies a
  magnitude by a stored (usually floating-point) conversion factor, so exact `=` would
  make `5 Kilogram` and `5000 Gram` unequal on a last-bit rounding difference.  Two base
  magnitudes count as equal when they differ by at most this much, and strict `<` / `>`
  demand a gap wider than it — so exactly one of `<`, `=`, `>` holds for any pair.
  Absolute (not relative) and small; rebind for a coarser or finer policy, and the
  rounding grid a computed magnitude is snapped to follows the rebinding
  (`tolerance-scale`)."
  1e-9)

(defn measure?
  "Is `x` a ground measure term — `(QuantityFn N Unit)` or
  `(QuantityIntervalFn Lo Hi Unit)`, numeric magnitude(s) and a symbol unit?  This is
  the check-only condition: a comparison is claimed only when *both* arguments are ground
  measures, so `(sameQuantity ?x M)` is refused, never enumerated.

  Public because it is the shared answer to \"is this a measure?\": every prover that
  reads one — the comparison here, the durations, the metric temporal network — must
  agree on the question, and three copies of this could not be kept agreeing.

  A magnitude is a **finite** number: `##Inf` and `##NaN` read as not-a-measure, the
  same answer `assert` gives them (`:not-well-formed`), so the magnitude arithmetic
  never sees one."
  [x]
  (let [num? (fn [n] (and (number? n) (Double/isFinite (double n))))]
    (and (sequential? x) (seq x)
         (case (first x)
           QuantityFn         (and (= 3 (count x)) (num? (nth x 1)) (symbol? (nth x 2)))
           QuantityIntervalFn (and (= 4 (count x)) (num? (nth x 1)) (num? (nth x 2))
                                   (symbol? (nth x 3)))
           false))))

(defn- table-read
  "One reading of the unit table: `[values handles]`, where `values` is the bindings of `ks`
  that every believed match of `pat` visible from `context` **agrees** on, nil when there is no
  match or two disagree, and `handles` names the declarations read.  One `matches-visible`
  read.

  Agreement and not the first match, since the first is handle order.  A disagreement is
  declined, not adjudicated, as in `duration/interval-length-with-support` and
  `stp/endpoints-with-support`.  The same declaration in several contexts collapses to one.
  `ks` is a vector because a `conversionFactor` names a base and a factor that are one
  reading.  `handles` is every declaration read: retracting one of two agreeing declarations
  withdraws a conclusion the survivor would license, which is preferred to belief depending on
  arrival order (docs/nmtms.md)."
  [kb pat context ks]
  (let [ms (res/matches-visible kb pat context)
        vs (into #{} (map (fn [m] (mapv #(get (second m) %) ks))) ms)]
    (when (= 1 (count vs))
      [(first vs) (into #{} (map first) ms)])))

(def unit-table-predicates
  "The two predicates a measure is normalized through: what `normalize-quantity` reads, and
  what a conclusion drawn from a measure comparison rests on besides the facts that bound the
  measures.  A prover's own source list, kept here and not as a `:support-source` field on the
  declaration: neither predicate is grammar (both live in `kb/upper/measure.txt`), and
  `support-source-preds` asks the registry live, so a prover added through `add-prover`
  contributes its sources."
  '#{dimensionOf conversionFactor})

(defn normalize-quantity-with-support
  "Resolve a ground measure to `[[dimension lo-base hi-base] handles]`: its dimension and its
  magnitude bounds converted direct-to-base (one multiply, no chaining), with the declarations
  the conversion was read from.  A point `(QuantityFn N U)` has `lo-base = hi-base`.

  - Dimension is `(dimensionOf U ?d)`, or `U` itself when the unit declares none, so two
    measures in the same unit always compare and two distinct undeclared units do not.
  - Base magnitude is `N × (conversionFactor U ?base ?factor)`, the factor defaulting to `1`.
    Every unit of one dimension must convert to a single base unit.

  Both reads go through `table-read`, so a unit declared twice and differently falls back to
  being its own dimension and base.  The handles are empty when the unit declares neither,
  since an absence is not a sentex a retraction can take away; `SupportingProver`'s
  `support-sources` covers a declaration arriving later."
  [kb measure context]
  (let [[lo hi unit] (case (first measure)
                       QuantityFn         (let [[_ n u] measure]   [n n u])
                       QuantityIntervalFn (let [[_ l h u] measure] [l h u]))
        [dv dh] (table-read kb (list 'dimensionOf unit '?dim) context '[?dim])
        [cv ch] (table-read kb (list 'conversionFactor unit '?base '?factor) context
                            '[?base ?factor])
        dim     (or (first dv) unit)
        factor  (let [f (second cv)] (if (number? f) f 1))]
    [[dim (* lo factor) (* hi factor)]
     (into (or dh #{}) (or ch #{}))]))

(defn normalize-quantity
  "`normalize-quantity-with-support`'s `[dimension lo-base hi-base]` alone, for a caller
  with no use for the declarations behind it."
  [kb measure context]
  (first (normalize-quantity-with-support kb measure context)))

;; ---- and the way back out ------------------------------------------------
;; `normalize-quantity` reads a measure in; these three write one back.  They live
;; beside it because they are the same contract seen from the other end — an answer is
;; rendered in the dimension's base unit, read out of the very `conversionFactor` table
;; the normalization multiplied by, so nothing separate can disagree about the unit the
;; arithmetic happened in.  Every prover that computes a measure rather than merely
;; comparing one shares them.

(defn base-unit-with-support
  "The base unit `unit` converts to, and the declaration that says so: `[base handles]`.
  The second argument of its `conversionFactor`, or `unit` itself when it declares none
  and is therefore its own base — the latter with empty support, for
  `normalize-quantity-with-support`'s reason.

  Exactly the unit `normalize-quantity`'s magnitudes come back in, because the two read
  one declaration through the same `table-read`: a unit whose factor is declined for
  disagreeing has its base declined with it, so the answer is never rendered in a unit the
  arithmetic did not happen in."
  [kb unit context]
  (let [[v hs] (table-read kb (list 'conversionFactor unit '?base '?factor)
                           context '[?base ?factor])]
    (if-let [base (first v)] [base (or hs #{})] [unit #{}])))

(defn base-unit-of
  "`base-unit-with-support`'s unit alone, for a caller with no use for the declaration
  behind it."
  [kb unit context]
  (first (base-unit-with-support kb unit context)))

(defn measure-with-support
  "A ground measure as `[[[dimension base-unit] lo-base hi-base] handles]`:
  `normalize-quantity-with-support` with its dimension paired with the unit its
  magnitudes are in (`base-unit-with-support`), and the declarations of both reads.  Two
  measures compare only under one `[dimension base-unit]` key, so a unit with no
  `conversionFactor`, its own base at factor 1, compares with itself and with no other
  unit of its dimension."
  [kb measure context]
  (let [[[dim lo hi] nsup] (normalize-quantity-with-support kb measure context)
        [base bsup]        (base-unit-with-support kb (last measure) context)]
    [[[dim base] lo hi] (into nsup bsup)]))

(defn- tolerance-scale
  "The decimal scale the tolerance grid sits on — the places `*quantity-tolerance*`
  distinguishes, `-⌊log₁₀ tol⌋`: 9 at the shipped `1e-9`, 3 under a `1e-3` rebinding.

  Derived rather than fixed, because the grid and the comparisons have to be the same
  policy: a caller who coarsens `*quantity-tolerance*` coarsens what `q=` calls equal,
  and a grid left behind would then snap two equal magnitudes to two different figures.
  Clamped to `[0, 18]` — the top of the range is what a non-positive tolerance (exact
  comparison, nothing to snap) reads as, and 18 keeps the result inside the `long`
  precision the caller tests for."
  ^long []
  (let [t (double *quantity-tolerance*)]
    (if (pos? t)
      (min 18 (max 0 (- (long (Math/floor (Math/log10 t))))))
      18)))

(defn round-magnitude
  "Snap a computed magnitude to the tolerance grid, and hand back a long when what is
  left is a whole number.  Two reasons, and only the second is cosmetic: a sum of
  converted magnitudes carries float noise that would render as `2.5000000000000004`,
  and a rendered `(QuantityFn 9000.0 Second)` is not `=` to the `(QuantityFn 9000
  Second)` a caller would write, so a bound answer would not compare equal to the
  obvious way of writing it.

  The grid is `*quantity-tolerance*`'s own (`tolerance-scale`), so rebinding the
  tolerance moves the rounding with the comparisons rather than leaving the two on
  different policies."
  [x]
  (let [b (-> (BigDecimal/valueOf (double x))
              (.setScale (int (tolerance-scale)) java.math.RoundingMode/HALF_UP)
              (.stripTrailingZeros))]
    (if (and (<= (.scale b) 0) (< (.precision b) 19))
      (.longValue b)
      (.doubleValue b))))

(defn render-quantity
  "The measure the bounds `[lo hi]` in `unit` denote: a **point** when they coincide, an
  **interval** when they do not.  A computed answer never claims a precision it lacks — an
  over-approximation renders as an interval and says so, rather than picking a figure
  out of a range it only bounded."
  [lo hi unit]
  (let [lo* (round-magnitude lo)
        hi* (round-magnitude hi)]
    (if (<= (abs (- lo* hi*)) *quantity-tolerance*)
      (list 'QuantityFn lo* unit)
      (list 'QuantityIntervalFn lo* hi* unit))))

(defn q=
  "Are two base magnitudes equal within `*quantity-tolerance*`?  Normalization multiplies
  by a stored (usually floating-point) conversion factor, so exact `=` would make one sum
  unequal to itself written in another unit.  The measure comparisons here and
  `duration`'s bound checks call it."
  [a b]
  (<= (abs (- a b)) *quantity-tolerance*))
(defn- q<  [a b] (< a (- b *quantity-tolerance*)))
(defn- q>  [a b] (> a (+ b *quantity-tolerance*)))
(defn- q<= [a b] (<= a (+ b *quantity-tolerance*)))
(defn- q>= [a b] (>= a (- b *quantity-tolerance*)))

(defn- measures-hold?
  "Does comparison `pred` hold between two measures `[key lo hi]` (`measure-with-support`)?
  The interval reading is **necessary** (definite): the comparison holds only when it
  holds of every point of each interval, which collapses to ordinary number comparison for
  a point (`lo = hi`).  A **key mismatch is never comparable** — a dimension, or a base
  unit, the two do not share — and the guard yields nil (⇒ the goal fails); it never
  throws."
  [pred [d1 lo1 hi1] [d2 lo2 hi2]]
  (when (= d1 d2)
    (case pred
      sameQuantity               (and (q= lo1 lo2) (q= hi1 hi2))
      quantityLessThan           (q< hi1 lo2)
      quantityGreaterThan        (q> lo1 hi2)
      quantityLessThanOrEqual    (q<= hi1 lo2)
      quantityGreaterThanOrEqual (q>= lo1 hi2)
      nil)))

(defn measures-agree?
  "Can the ground measures `a` and `b` denote one magnitude, read at `context`: both
  measures, normalized under one `[dimension base-unit]` key (`measure-with-support`),
  with bounds that meet within `*quantity-tolerance*`.  Two points agree when they are
  equal, a point and an interval when the interval holds the point, and two intervals
  when they overlap.  False for anything that is not a measure.  The functional check
  and the tuple placement read it, so a functional slot holding `(QuantityFn 20
  Kilogram)` and `(QuantityFn 20000 Gram)` holds one value (docs/quantity.md)."
  [kb a b context]
  (boolean
   (when (and (measure? a) (measure? b))
     (let [[k1 lo1 hi1] (first (measure-with-support kb a context))
           [k2 lo2 hi2] (first (measure-with-support kb b context))]
       (and (= k1 k2) (q<= lo1 hi2) (q<= lo2 hi1))))))

(defrecord QuantityProver []                     ; measure comparison over the unit table
  Prover
  (applicable? [_ _ goal _]
    (and (binary? goal) (contains? measure-comparisons (first goal))
         (measure? (nth goal 1)) (measure? (nth goal 2))))
  (est-bindings [_ _ _ _] 1)                     ; a ground test: it holds or it does not
  (cost         [_ _ _ _] :lookup)               ; a couple of table reads + arithmetic
  ;; Authoritative: a measure comparison is never a stored fact, so the unit table
  ;; contains every answer there is.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [[pred a b] goal]
      (if (measures-hold? pred
                          (first (measure-with-support kb a context))
                          (first (measure-with-support kb b context)))
        [{}] [])))

  SupportingProver
  (support-functors [_] measure-comparisons)
  ;; The unit table, and nothing else.  The measure *terms* are already in the firing's
  ;; antecedents — a comparison is check-only over two ground measures, so whatever bound
  ;; them was an ordinary matched antecedent — and only the conversion behind them is read
  ;; from somewhere no antecedent names.
  (support-sources [_] unit-table-predicates)
  (solve-with-support [_ kb goal context]
    ;; Both normalizations are read whichever way the comparison goes, so the support is
    ;; the union: a `(quantityLessThan (QuantityFn 500 Gram) (QuantityFn 1 Kilogram))`
    ;; that holds only because a gram is a thousandth of a kilogram rests on the gram's
    ;; row *and* the kilogram's, and retracting either is what un-holds it.
    (let [[pred a b] goal
          [na sa] (measure-with-support kb a context)
          [nb sb] (measure-with-support kb b context)]
      (if (measures-hold? pred na nb) [[{} (into sa sb)]] []))))

;; ---- negation as failure: unknown / thereExists / forall / closed extents ----
;; Each runs its argument through the registry and is ground/closed only.  See
;; docs/naf.md.

(defn- conjunct-computed?
  "Is conjunct `c` computed (a nested `(unknown …)`, an evaluable, an aggregate) rather
  than matched?"
  [c]
  (or (sx/unknown? c) (sx/deferred-literal? c)))

(defn- planned-conjuncts
  "`conjuncts` in an order every computed conjunct can run in, given the variables
  `bound` at entry: each computed one, and each literal in `tests`, placed once the
  variables it reads are bound, matched conjuncts keeping their canonical order.  A
  conjunct nothing can make ready is placed anyway, not dropped; `sentex/check-naf-closed`
  refuses such a rule (docs/naf.md, \"The conjunction is joined\")."
  [conjuncts bound tests]
  (loop [pending (vec conjuncts) bound (set bound) out []]
    (if (empty? pending)
      out
      (let [i (or (first (keep-indexed
                          (fn [i c] (when (or (not (or (conjunct-computed? c) (contains? tests c)))
                                              (every? bound (sx/deferred-input-vars c bound)))
                                      i))
                          pending))
                  0)
            c (nth pending i)]
        (recur (into (subvec pending 0 i) (subvec pending (inc i)))
               (into bound (concat (sx/free-vars c) (sx/deferred-output-vars c bound)))
               (conj out c))))))

(defn conjunction-solutions
  "Lazy solutions of the conjunctive level-6 body `conjuncts`, extending `bindings`, in
  `context`: the one joined evaluator `unknown`, `thereExists`, `exceptWhen` and an
  aggregate's census read.  Each conjunct, in `planned-conjuncts` order, is substituted
  with what the conjuncts before it bound, put in `norm`'s normal form when `norm` is
  non-nil, and run through the registry.  A closed negative conjunct over a predicate a
  closed extent is declared on (`rules/closed-extent-antecedents`) runs after the
  conjuncts that bind it, since `ClosedExtentProver` answers it only ground.  Lazy throughout, so a caller taking one
  solution enumerates no extent (docs/naf.md, \"The conjunction is joined\")."
  ([kb conjuncts bindings context] (conjunction-solutions kb conjuncts bindings context nil))
  ([kb conjuncts bindings context norm]
   (let [pv (registry kb)]
     (reduce (fn [sols c]
               (res/lazy-mapcat
                (fn [b]
                  (let [g0 (sx/canon (res/substitute c b))
                        g  (if norm (sx/canon (norm g0)) g0)]
                    (map #(merge b %) (solve-goal-with kb pv g context))))
                sols))
             [bindings]
             (planned-conjuncts conjuncts (keys bindings)
                                (set (rules/closed-extent-antecedents (reasoning/taxonomy kb)
                                                                      conjuncts)))))))

(defn conjunction-derivable?
  "Does the conjunctive level-6 body `conjuncts` have a solution under `bindings` in
  `context`?  An empty conjunction has none."
  ([kb conjuncts bindings context] (conjunction-derivable? kb conjuncts bindings context nil))
  ([kb conjuncts bindings context norm]
   (boolean (and (seq conjuncts)
                 (seq (take 1 (conjunction-solutions kb conjuncts bindings context norm)))))))

(defrecord UnknownProver []
  Prover
  (applicable?  [_ _ goal _] (and (sx/unknown? goal) (empty? (sx/free-vars goal))))
  (est-bindings [_ _ _ _] 1)                    ; a ground test: it holds or it does not
  ;; a bounded level-6 subquery (no backchaining), so at worst a closure, never a search
  (cost         [_ _ _ _] :compute)
  ;; authoritative: `unknown` is not assertible, so no other prover holds a claim on it
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (if (as-guard #(conjunction-derivable? kb (sx/naf-query-conjuncts goal) {} context))
      []                                          ; S is derivable → (unknown S) fails
      [{}])))                                     ; S is not derivable → (unknown S) holds

(defrecord ThereExistsProver []
  Prover
  (applicable?  [_ _ goal _] (and (sx/there-exists? goal) (empty? (sx/free-vars goal))))
  (est-bindings [_ _ _ _] 1)                    ; an existence check: one answer or none
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    ;; any solution of the joined body suffices; the binder is projected out
    (if (conjunction-derivable? kb (sx/conjuncts (nth goal 2)) {} context)
      [{}]
      [])))

(defn closed-extent?
  "Is `pred`'s believed extent declared **complete** as read from `context` — is
  `(closed_extent_predicate pred)` visible up its `genlCx` ancestor set?  See
  docs/naf.md, \"A closed extent\"."
  [kb pred context]
  (and (symbol? pred) (tax/has-prop? (reasoning/taxonomy kb) :closed-extent pred context)))

(defn- arg-grant-covers?
  "Does a `closedExtentForArg` grant read as the bindings `b` of `?n` and `?v` cover
  `sentence`: is argument `?n` of it ground and equal to `?v`?"
  [sentence b]
  (let [n (get b '?n)]
    (and (integer? n) (pos? n) (< n (count sentence))
         (let [arg (nth sentence n)]
           (and (empty? (sx/free-vars arg)) (= arg (get b '?v)))))))

(defn closed-extent-for-arg?
  "Is the believed extent of `sentence`'s predicate declared **complete for this
  sentence** as read from `context` — is a `(closedExtentForArg P n v)` visible up its
  `genlCx` ancestor set whose position `n` in `sentence` is ground and equal to `v`?
  The taxonomy prop `:closed-extent-arg` is the presence check; the position and value
  are read from the believed grants visible from `context`."
  [kb sentence context]
  (let [pred (nm/functor sentence)]
    (boolean
     (and (symbol? pred)
          (tax/has-prop? (reasoning/taxonomy kb) :closed-extent-arg pred context)
          (some (fn [[_ b]] (arg-grant-covers? sentence b))
                (res/matches-visible kb (list 'closedExtentForArg pred '?n '?v) context))))))

(defn closed-extent-for?
  "Is `sentence`'s believed extent declared complete from `context` — by a
  `closed_extent_predicate` grant on its predicate, or by a `closedExtentForArg` grant
  whose position and value the sentence matches?"
  [kb sentence context]
  (or (closed-extent? kb (nm/functor sentence) context)
      (closed-extent-for-arg? kb sentence context)))

(defrecord ClosedExtentProver []
  Prover
  ;; `(not (P a …))` where P's extent is declared complete from here, whole or for the
  ;; value one argument holds.  Ground only, for `unknown`'s reason: an open
  ;; `(not (P ?x))` is a search over the domain's complement.
  (applicable?  [_ kb goal context]
    (and (rules/negative-literal? goal)
         (empty? (sx/free-vars goal))
         (closed-extent-for? kb (second goal) context)))
  (est-bindings [_ _ _ _] 1)                    ; a ground test: it holds or it does not
  ;; a bounded level-6 subquery on the positive goal, so at worst a closure
  (cost         [_ _ _ _] :compute)
  ;; partial: FactProver answers a stored `(not (P a))`, and the union dedups
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    ;; the extent is complete, so no positive answer *is* the negative answer
    (if (seq (take 1 (solve-goal-with kb (registry kb) (second goal) context)))
      []
      [{}])))

(defrecord ForallProver []
  Prover
  (applicable?  [_ _ goal _] (and (sx/forall? goal) (empty? (sx/free-vars goal))))
  (est-bindings [_ _ _ _] 1)                    ; a closed test: it holds or it does not
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    ;; the desugared nested NAF, handed back to the registry (docs/naf.md)
    (solve-goal-with kb (registry kb) (sx/desugar-forall-literal goal) context)))

;; ---- evaluative defnSufficient: prove membership by evaluating the condition ----
;; A `(defnSufficient Coll C)` whose condition `C` is built from computed predicates alone
;; (`integer`, `lessThan`, an `add-evaluatable` check) derives no member forward, since its
;; companion rule (`sentex/defn-companion-rules`) fires only when a stored conjunct binds the
;; member.  On `(Coll a)` this prover substitutes `a` for `?x` in `Coll`'s visible conditions
;; and asks whether the condition holds through the registry, which evaluates them
;; (`conjunction-derivable?`, level 6, no backchaining).  It augments the fact prover and the
;; forward rule (completeness 50); a believed condition is deduped.
;;
;; Positive membership descends to a spec's sufficient over `tax/specs`, which is reflexive.
;; A passing sufficient admits even against a failing own necessary (the inconsistency is
;; documented, not arbitrated), but a failing necessary of a strict genl fast-fails the
;; query (`genl-necessary-fails?`).  The negation prover is the converse build, below.

(def ^:private ^:dynamic *defn-stack*
  "The collections a defn prover solve is already inside — the re-entry guard shared by the
  positive (sufficient-descent) and negative (necessary-ascent) walks, so a self-referential
  condition — `(defnSufficient Coll (Coll ?x))`, which nothing forbids — cannot recur
  without end.  Level-6 has no depth guard of its own, so the re-entry is bounded here."
  #{})

(defn- defn-conditions
  "The conditions `C` of every visible `(pred coll C)` for the definitional relation
  `pred` (`defnSufficient` / `defnNecessary`), from `context` — the member still named by
  `sx/defn-member-var`, which fact canonicalization preserves (only rule canonicalization
  renames variables).  Lazy, so a `take 1` applicability probe stops at the first."
  [kb pred coll context]
  (keep #(get (second %) '?cond)
        (res/matches-visible kb (list pred coll '?cond) context)))

(defn- condition-holds?
  "Does the defn condition `cond` hold for `member`, evaluated at query time through the
  registry (level-6, no backchaining)?  The member is substituted for `sx/defn-member-var`
  and each conjunct answered by the evaluables, the facts and the closures.  **Two-valued**:
  a condition that is not derivable is false — there is no third 'unknown' state."
  [kb cond member context]
  (conjunction-derivable?
   kb (sx/conjuncts (res/substitute cond {sx/defn-member-var member})) {} context))

;; ---- applicability checks: is a defn even in reach, without the per-node walk? ---
;; Both defn provers ship in the default registry, so their `applicable?` runs on EVERY
;; ground unary goal — and the exact test, "does `coll`'s spec/genl ancestor set carry a
;; visible defn", is a `tax/specs`/`tax/genls` walk with a `matches-visible` per node.  On a
;; goal about a predicate that bears no defn (the overwhelming majority, even under a full
;; upper ontology where only a dozen collections are defined) that walk finds nothing at a
;; cost that scales with the predicate's fan-out.  Two cheaper questions decide it instead,
;; each equivalent to the walk's emptiness test but bounded by the DECLARATIONS, not the
;; taxonomy: first "is there any such defn fact at all" (one functor count — the whole
;; answer on a defn-free KB), then "is any of the few declaring collections in the
;; subsumption relation to `coll`" (a `tax/genl?` per declarer).

(defn- has-defn-fact?
  "O(1): does the store hold ANY `pred` (`defnSufficient` / `defnNecessary`) fact?  The
  O(1) pre-filter the applicability checks and the negative fast-fail share — a
  defn-free KB answers here, before any taxonomy read.  `stored-count-with-functor` is the
  same one-integer presence check the engine's other definitional checks front themselves
  with (reads.clj)."
  [kb pred]
  (pos? (reads/stored-count-with-functor (:index kb) pred)))

(defn- defn-declaring-colls
  "The collections carrying a visible `(pred coll _)` declaration, from `context` — the
  arg0 of each such fact, read off the functor posting.  One per declaration, so a small
  set even under a full ontology; empty on a KB that declares no defn of this kind."
  [kb pred context]
  (into #{} (keep #(get (second %) '?coll))
        (res/matches-visible kb (list pred '?coll '?cond) context)))

(defn- spec-carries-sufficient?
  "Does `coll`'s reflexive spec ancestor set carry a visible defnSufficient — the
  `DefnSufficientProver` applicability test, without the per-spec walk?  A declaring
  collection is a spec of `coll` exactly when it is `coll` or a subtype of it, so this is
  `(seq (spec-sufficient-conditions kb coll context))` decided over the declaring
  collections and a `tax/genl?` each, independent of `coll`'s descendant count.
  Short-circuits on a defn-free KB before touching the taxonomy."
  [kb coll context]
  (and (has-defn-fact? kb 'defnSufficient)
       (let [tx (reasoning/taxonomy kb)]
         (boolean (some (fn [d] (or (= d coll) (tax/genl? tx d coll context)))
                        (defn-declaring-colls kb 'defnSufficient context))))))

(defn- genl-carries-necessary?
  "Does `coll`'s reflexive genl ancestor set carry a visible defnNecessary — the
  `DefnNecessaryNegationProver` applicability test, the converse of
  `spec-carries-sufficient?`?  A declaring collection is a genl of `coll` exactly when it
  is `coll` or a supertype of it.  Bounded by the declaring collections, not by `coll`'s
  ancestor count; short-circuits on a defn-free KB."
  [kb coll context]
  (and (has-defn-fact? kb 'defnNecessary)
       (let [tx (reasoning/taxonomy kb)]
         (boolean (some (fn [d] (or (= d coll) (tax/genl? tx coll d context)))
                        (defn-declaring-colls kb 'defnNecessary context))))))

(defn- spec-sufficient-conditions
  "Every defnSufficient condition in `coll`'s spec ancestor set (reflexive `tax/specs`), lazily —
  `coll`'s own and every spec's, the descent the positive walk admits on."
  [kb coll context]
  (mapcat #(defn-conditions kb 'defnSufficient % context)
          (tax/specs (reasoning/taxonomy kb) coll context)))

(defn- most-general-first
  "`colls` ordered most-general-first — a linear extension of the genl partial order, so an
  ancestor is always checked before any of its descendants.  The key is the ancestor count
  (`tax/genls` is reflexive; a genl's ancestors are a subset of its spec's, so the count
  ascends down the chain), with a printed-term tie-break for a deterministic order."
  [tx context colls]
  (sort-by (fn [c] [(count (tax/genls tx c context)) (nm/print-key c)]) colls))

(defn- genl-necessary-fails?
  "Does some necessary of a **strict** genl of `coll` fail for `member` — the positive
  query's fast-fail?  Walks the strict-genl ancestor set most-general-first and stops at the first
  failing necessary (the broadest disqualifier), so a consistent KB rejects without
  evaluating the sides or the (possibly expensive) sufficient.
  **Strict** (excludes `coll` itself): a collection's own necessary does not veto its own
  sufficient — sufficient is authoritative — and the ancestor set is a set, so a defn reachable
  by two genl paths (a diamond's apex) is checked exactly once.  Sound only on a consistent
  KB: on an inconsistent one the negation prover records
  the ¬member half and this merely declines to admit."
  [kb coll member context]
  (and (has-defn-fact? kb 'defnNecessary)
       (let [tx        (reasoning/taxonomy kb)
             ancestors (disj (tax/genls tx coll context) coll)]
         (boolean
          (some (fn [g]
                  (some (fn [c] (not (condition-holds? kb c member context)))
                        (defn-conditions kb 'defnNecessary g context)))
                (most-general-first tx context ancestors))))))

(defrecord DefnSufficientProver []
  Prover
  ;; A ground unary membership goal `(Coll a)` for a `Coll` whose spec ancestor set carries a
  ;; visible defnSufficient.  Ground because the condition is evaluated against the member:
  ;; an open `(Coll ?x)` would ask a computed condition to *enumerate* its members, which a
  ;; sufficient built from `integer` / `lessThan` cannot do (no generator enumerates an
  ;; infinite extent).
  (applicable? [_ kb goal context]
    (and (sequential? goal)
         (symbol? (first goal))
         (= 1 (count (rest goal)))
         (ground? goal)
         (not (contains? *defn-stack* (first goal)))
         (spec-carries-sufficient? kb (first goal) context)))
  (est-bindings [_ _ _ _] 1)                    ; a ground membership test: it holds or not
  (cost         [_ _ _ _] :compute)             ; a bounded level-6 subquery, at worst a closure
  ;; Augments `FactProver` and the forward defn rule rather than replacing them: a
  ;; believed condition is answered by both and deduped, so the union carries the stored
  ;; path and adds the computed one.  Not the sole complete method, so it never runs alone.
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (let [coll   (first goal)
          member (second goal)]
      (binding [*defn-stack* (conj *defn-stack* coll)]
        ;; Fast-fail FIRST (short-circuit `or`), so a failing genl-necessary rejects
        ;; without the sufficient ever being evaluated — a pure speedup on a consistent KB.
        (if (or (genl-necessary-fails? kb coll member context)
                (not (some (fn [c] (condition-holds? kb c member context))
                           (spec-sufficient-conditions kb coll context))))
          []
          [{}])))))

;; ---- negated defn checks: (not (coll x)) via a FAILING necessary (the converse) --------
;; The exact converse of the positive walk, with three flips:
;; member ↔ non-member, sufficient ↔ necessary, and the genl-walk direction — the positive
;; walk descends to a spec's *sufficient*, the negative ascends to a genl's *necessary*.
;; `(not (Coll x))` is provable iff a defnNecessary fails for `x` — `Coll`'s own or any
;; genl's (member ⇒ every necessary up the chain, so a failed one anywhere at-or-above
;; proves ¬member).  This is NOT closed-world negation-as-failure: it never fires merely
;; because `(Coll x)` cannot be proved; it fires only on a necessary that positively FAILS
;; (two-valued — the condition is evaluably false).  A `Coll` with no necessary in its ancestor set
;; makes this prover inapplicable, so absence of a proof is never mistaken for a disproof.

(defn- ancestor-necessary-conditions
  "Every defnNecessary condition in `coll`'s **reflexive** genl ancestor set (`tax/genls`), lazily
  — `coll`'s own and every genl's.  Reflexive (unlike the positive fast-fail's strict ancestor set)
  because a collection's own failing necessary is itself a sound negative witness."
  [kb coll context]
  (mapcat #(defn-conditions kb 'defnNecessary % context)
          (tax/genls (reasoning/taxonomy kb) coll context)))

;; ---- what a :monotonic definition decides about a literal value ---------------
;; The argument checks judge a literal value by its kind (`checks/value-outside?`), and a
;; type no kind reaches convicts it.  A `:monotonic` defn over evaluable conditions states
;; the kind a type's members are, so it decides the value first: docs/defns.md, "A
;; definition decides a literal value at the argument check".

(defn- value-defn-matches
  "The visible `(f coll ?cond)` matches of `pred` (`defnSufficient` / `defnNecessary`) and
  of `defnIff`, which states both, from `context`, lazily.  The value checks read `defnIff`
  here; the defn provers read the bare forms (`defn-conditions`)."
  [kb pred coll context]
  (mapcat #(res/matches-visible kb (list % coll '?cond) context) [pred 'defnIff]))

(defn- value-defn-stored?
  "O(1): does the store hold any `defnSufficient`, `defnNecessary` or `defnIff` fact?"
  [kb]
  (boolean (some #(pos? (reads/stored-count-with-functor (:index kb) %))
                 '[defnSufficient defnNecessary defnIff])))

(defn- value-defn-colls
  "The collections a visible `pred` or `defnIff` definition names, from `context`."
  [kb pred context]
  (into #{} (keep #(get (second %) '?coll)) (value-defn-matches kb pred '?coll context)))

(defn- monotonic-conditions
  "The conditions of the visible `:monotonic` definitions stating a `pred` condition on
  `coll`, from `context`: `res/holding-class` reads the live class, so a `:default` or an
  OUT definition contributes none."
  [kb pred coll context]
  (let [class-of (res/holding-class kb)]
    (keep (fn [[h b]] (when (= :monotonic (class-of h)) (get b '?cond)))
          (value-defn-matches kb pred coll context))))

(defn- condition-on-value
  "`true` or `false` when every conjunct of the condition `cond` is an evaluable literal or
  its negation (`evaluable-predicates`, the KB's evaluatables) and the evaluation answers
  for the literal value `v`, else nil.  A conjunct naming a stored predicate leaves a value
  open, and a pattern too costly to match decides nothing."
  [kb cond v context]
  (let [evs (into evaluable-predicates (evaluatable-preds kb))
        lit (fn [l] (if (rules/negative-literal? l) (second l) l))]
    (when (every? #(let [l (lit %)] (and (sequential? l) (contains? evs (first l))))
                  (sx/conjuncts cond))
      (try (condition-holds? kb cond v context)
           (catch clojure.lang.ExceptionInfo e
             (when-not (= :pattern-too-costly (:type (ex-data e))) (throw e)))))))

(defn value-definition-frame
  "The half of `value-definition` no value enters, for the type `t` from `context`:
  `{:above :below :own}`, the `:monotonic` necessary conditions of the strict supertypes
  of `t`, the sufficient conditions of `t` and its subtypes, and `t`'s own necessary
  conditions, each in the order `value-definition` tries them.  Nil when `t` is no symbol
  or the store holds no definition."
  [kb t context]
  (when (and (symbol? t) (value-defn-stored? kb))
    (let [tx    (reasoning/taxonomy kb)
          conds (fn [pred cs] (into [] (mapcat #(monotonic-conditions kb pred % context)) cs))
          nec   (value-defn-colls kb 'defnNecessary context)]
      {:above (conds 'defnNecessary
                     (filter #(and (not= % t) (tax/genl? tx t % context)) (sort-by nm/print-key nec)))
       :below (conds 'defnSufficient
                     (filter #(or (= % t) (tax/genl? tx % t context))
                             (sort-by nm/print-key (value-defn-colls kb 'defnSufficient context))))
       :own   (when (contains? nec t) (conds 'defnNecessary [t]))})))

(defn value-definition
  "What the `:monotonic` definitions decide about the literal value `v` under the type `t`,
  from `context`: `:outside` when a necessary condition of a strict supertype of `t` is
  false on `v`, else `:member` when a sufficient condition of `t` or of a subtype of `t`
  is true on `v`, else `:outside` when a necessary condition of `t` itself is false on
  `v`, else nil.  Only a condition `condition-on-value` evaluates decides, and nil for a
  `v` that is no literal value.  The order is the defn provers': a supertype's necessary
  is checked first, and a sufficient admits against `t`'s own necessary.  The argument
  checks read this (`checks/value-outside?`), and pass `frame-of`, a thunk answering
  `value-definition-frame` of `t` and `context`, to share it across values."
  ([kb v t context] (value-definition kb v t context #(value-definition-frame kb t context)))
  ([kb v t context frame-of]
   (when (literal-value-kind v)
     (when-let [{:keys [above below own]} (frame-of)]
       (binding [*defn-stack* (conj *defn-stack* t)]
         (let [any? (fn [answer cs] (some #(= answer (condition-on-value kb % v context)) cs))]
           (cond
             (any? false above) :outside
             (any? true below)  :member
             (any? false own)   :outside)))))))

(defn value-definition-reaches?
  "Can a `:monotonic` definition decide a literal value under the type `t`, from `context`
  (`value-definition`): does a visible `:monotonic` definition state a sufficient
  condition of `t` or of a subtype, or a necessary condition of `t` or of a supertype?"
  [kb t context]
  (boolean
   (and (symbol? t)
        (value-defn-stored? kb)
        (let [tx (reasoning/taxonomy kb)]
          (or (some #(and (or (= % t) (tax/genl? tx % t context))
                          (seq (monotonic-conditions kb 'defnSufficient % context)))
                    (value-defn-colls kb 'defnSufficient context))
              (some #(and (or (= % t) (tax/genl? tx t % context))
                          (seq (monotonic-conditions kb 'defnNecessary % context)))
                    (value-defn-colls kb 'defnNecessary context)))))))

(defn- definition-entries
  "The visible `(pred coll condition)` declarations as witness maps.  Keeping the
  declaring collection beside the condition matters to an integrity report: a
  sufficient inherited from a spec is evidence about a different declaration than
  the queried collection's own necessary."
  [kb pred coll context]
  (for [declaring-coll coll
        [_ bindings _] (res/matches-visible
                        kb (list pred declaring-coll '?condition) context)]
    (do
      (budget/spend!)
      {:defined-collection declaring-coll
       :condition          (get bindings '?condition)})))

(defn- definition-inconsistency
  "The definitional clash witness for one ground `(coll member)`, or nil."
  [kb coll member context]
  (binding [*defn-stack* (conj *defn-stack* coll)]
    (let [tx (reasoning/taxonomy kb)
          strict-failing?
          (some (fn [ancestor]
                  (some #(not (condition-holds? kb (:condition %) member context))
                        (definition-entries kb 'defnNecessary [ancestor] context)))
                (most-general-first tx context
                                    (disj (tax/genls tx coll context) coll)))]
      ;; Match the positive prover's short-circuit: once a strict ancestor excludes the
      ;; member, its sufficient conditions are not evaluated at all.
      (when-not strict-failing?
        (let [passing
              (->> (definition-entries kb 'defnSufficient
                     (tax/specs tx coll context) context)
                   (filter #(condition-holds? kb (:condition %) member context))
                   (sort-by (juxt (comp nm/print-key :defined-collection)
                                  (comp nm/print-key :condition)))
                   vec)
              own-failing
              (->> (definition-entries kb 'defnNecessary [coll] context)
                   (remove #(condition-holds? kb (:condition %) member context))
                   (sort-by (comp nm/print-key :condition))
                   vec)]
          (when (and (seq passing) (seq own-failing))
            {:collection coll
             :term member
             :passing-sufficient passing
             :failing-necessary own-failing}))))))

(defn- sufficient-definition-collections
  "The finite visible collection population the positive definition prover can reach.

  This is the sweep's one unavoidable open definition census: callers bound ground
  candidate terms but deliberately do not restate collection names. Every validation
  after this census is focused on one collection and one ground candidate."
  [kb context]
  (let [tx (reasoning/taxonomy kb)
        declared
        (into #{}
              (map (fn [match]
                     (budget/spend!)
                     (get (second match) '?collection)))
              (res/matches-visible
               kb '(defnSufficient ?collection ?condition) context))]
    (into #{} (mapcat #(tax/genls tx % context)) declared)))

(defn definition-inconsistencies
  "Query-only definitional inconsistencies over the finite ground `candidate-terms`.

  Returns one witness per `[collection term]` for which the definition provers can answer both
  `(collection term)` and `(not (collection term))`: some own-or-spec sufficient condition
  passes, the collection's own necessary condition fails, and no strict-genl necessary
  fast-fails the positive query.  Each witness carries every passing sufficient and failing
  necessary declaration involved.  The collections are those induced by `defnSufficient`
  declarations and their `genl` ancestors.  `vaelii.impl.integrity/kb-integrity` supplies
  `candidate-terms`.  Reads only."
  [kb candidate-terms context max-results]
  (let [query-colls (sufficient-definition-collections kb context)]
    (loop [pairs (seq (for [coll   (sort-by nm/print-key query-colls)
                            member (sort-by nm/print-key candidate-terms)]
                        [coll member]))
           findings []]
      (if-let [[coll member] (first pairs)]
        (do
          (budget/spend!)
          (if-let [finding (definition-inconsistency kb coll member context)]
            (if (and max-results (>= (count findings) max-results))
              {:status :truncated :reason :max-results :findings findings}
              (let [findings' (conj findings finding)]
                (budget/record! :definition-inconsistencies finding)
                (recur (next pairs) findings')))
            (recur (next pairs) findings)))
        {:status :complete :findings findings}))))

(defrecord DefnNecessaryNegationProver []
  Prover
  ;; A ground `(not (Coll x))` for a `Coll` whose reflexive genl ancestor set carries a visible
  ;; defnNecessary.  Ground, for the positive walk's reason: an open `(not (Coll ?x))` is a
  ;; search over the domain's complement, not a test.
  (applicable? [_ kb goal context]
    (and (rules/negative-literal? goal)
         (empty? (sx/free-vars goal))
         (let [lit (second goal)]
           (and (= 1 (count (rest lit)))
                (ground? lit)
                (not (contains? *defn-stack* (first lit)))
                (genl-carries-necessary? kb (first lit) context)))))
  (est-bindings [_ _ _ _] 1)                    ; a ground test: ¬member holds or it does not
  (cost         [_ _ _ _] :compute)             ; a bounded level-6 subquery, at worst a closure
  ;; Augments a stored `(not (Coll x))` (FactProver) and `ClosedExtentProver` rather than
  ;; replacing them; the union dedups, so the three agree wherever more than one answers.
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (let [lit    (second goal)
          coll   (first lit)
          member (second lit)]
      (binding [*defn-stack* (conj *defn-stack* coll)]
        ;; ¬member is proved by the first necessary that fails anywhere in the ancestor set.
        (if (some (fn [c] (not (condition-holds? kb c member context)))
                  (ancestor-necessary-conditions kb coll context))
          [{}]
          [])))))

;; ---- disjointness: (not (T x)) from a believed membership in a separated type ----
;; `(not (T x))` holds when `x` is believed a member of a type `S` that a visible
;; separation keeps apart from `T` (a `disjoint` pair, a disjoint metatype, a
;; `sibling_disjoint` parent or a `partition`, each closed under `genl` on both sides),
;; and every `genl` edge the separation climbs on either side holds at `:monotonic`.  A
;; `:default` edge applies forward and does not contrapose: "a `pa` is typically a `pb`"
;; leaves room for an atypical `pa` outside `pb`.  `res/separation-denials` is the read,
;; and the cover family names the same witnesses (`checks/cover-problem`).
;; Open-world: it fires on a positive membership, never on an unprovable one.

(defrecord DisjointnessNegationProver []
  Prover
  ;; A ground `(not (T x))` for a unary `T` a separation reaches (`tax/separable?`).
  ;; Ground, for `unknown`'s reason: an open `(not (T ?x))` enumerates the members of
  ;; every type separated from `T`, which is a search over the complement of an extent.
  (applicable? [_ kb goal _context]
    (and (rules/negative-literal? goal)
         (empty? (sx/free-vars goal))
         (let [lit (second goal)]
           (and (= 1 (count (rest lit)))
                (symbol? (first lit))
                (tax/separable? (reasoning/taxonomy kb) (first lit))))))
  (est-bindings [_ _ _ _] 1)                    ; a ground test: ¬member holds or it does not
  (cost         [_ _ _ _] :lookup)              ; a cached closure read per held type
  ;; Augments a stored `(not (T x))` (FactProver) and the other negation provers; the
  ;; union dedups, so they agree wherever more than one answers.
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (let [[t x] (second goal)]
      (if (res/separation-denied? kb t x context)
        [{}]
        []))))

;; ---- covering: the part a cover leaves when every other is ruled out -----
;;
;; `(covering W A B C)` says that an instance of `W` is an instance of at least one named
;; part.  With `(W x)` believed and every part but one believed **not** to hold of `x`,
;; the remaining part holds.  That is the whole of the inference, and it fires on explicit
;; negation alone: a part that merely cannot be proved rules out nothing, which is the
;; line between a coverage axiom and negation as failure (`docs/naf.md`).
;;
;; The shape is `DefnSufficientProver`'s — a ground unary membership goal, decided by
;; bounded level-6 subqueries, declining in one map lookup on a KB whose covers name
;; nothing about the goal's collection.  A `partition` declaration is recorded as a
;; cover too, so it licenses the same inference; what it adds is the separation, which is
;; `disjointness-test`'s and not this one's.

(defn- believed-literal?
  "Does the ground literal `lit` hold in `context`, through a bounded level-6 subquery?
  `conjunction-derivable?` over one conjunct — the same read `condition-holds?` makes of a
  defn condition, so a stored fact, a closure and an evaluable all count and a backward
  rule does not."
  [kb lit context]
  (conjunction-derivable? kb [lit] {} context))

(defn- cover-leaves-only
  "Does the declaration `[whole parts]` leave `part` as the only membership `member` can
  hold — `(whole member)` believed, and `(not (p member))` believed for every other part?

  The negations are asked of the *other* parts alone.  Asking it of `part` as well would
  turn a cover whose every part is ruled out into a proof of each of them; that state is a
  contradiction, and `settle` reports it as one rather than deriving from it here."
  [kb whole parts part member context]
  (and (believed-literal? kb (list whole member) context)
       (every? (fn [p] (believed-literal? kb (list 'not (list p member)) context))
               (remove #(= % part) parts))))

(defrecord CoveringProver []
  Prover
  ;; A ground unary membership goal `(Part a)` for a `Part` some visible cover names.
  ;; Ground for `DefnSufficientProver`'s reason: an open `(Part ?x)` would ask the cover to
  ;; enumerate the terms every *other* part is explicitly denied of, which is a search over
  ;; the complement of an extent rather than a test.
  (applicable? [_ kb goal context]
    (and (sequential? goal)
         (symbol? (first goal))
         (= 1 (count (rest goal)))
         (ground? goal)
         (seq (tax/covers-naming-visible (reasoning/taxonomy kb) (first goal) context))))
  (est-bindings [_ _ _ _] 1)                    ; a ground membership test: it holds or not
  (cost         [_ _ _ _] :compute)             ; one bounded level-6 subquery per part
  ;; Augments `FactProver` and the closures rather than replacing them: a stored or
  ;; inherited membership is answered by both and deduped, so the union carries the stored
  ;; path and adds the computed one.
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (let [part   (first goal)
          member (second goal)]
      (if (some (fn [[whole parts _]]
                  (cover-leaves-only kb whole parts part member context))
                (tax/covers-naming-visible (reasoning/taxonomy kb) part context))
        [{}]
        []))))

;; ---- negates: a denial read off the other side -----------------------------
;;
;; `(negates P R)` says no tuple of `P` and of `R` holds of one argument list, so a
;; believed `(R a …)` answers `(not (P a …))`, and `(not (Q a …))` for every `Q` below
;; `P`.  No denial is stored per fact: the declaration and the believed tuple are read at
;; the query (docs/taxonomy.md, "Predicate metadata").

(defn- negated-form
  "The tuple `(Q a …)` a `(not (Q a …))` goal denies, its functor a symbol, else nil."
  [goal]
  (when (rules/negative-literal? goal)
    (let [lit (second goal)]
      (when (and (sequential? lit) (symbol? (first lit)) (seq (rest lit)))
        lit))))

(defn- negated-tuple
  "The ground tuple `(Q a …)` a ground `(not (Q a …))` goal denies, its functor a
  symbol, else nil."
  [goal]
  (when-let [lit (negated-form goal)]
    (when (empty? (sx/free-vars goal)) lit)))

(defrecord NegatesProver []
  Prover
  ;; A ground `(not (Q a …))` for a `Q` at or below a side of a `negates` declaration the
  ;; reader sees.  Ground for `DisjointnessNegationProver`'s reason.
  (applicable? [_ kb goal context]
    (boolean (when-let [lit (negated-form goal)]
               (and (seq (tax/negates-over (reasoning/taxonomy kb) (first lit) context))
                    (empty? (sx/free-vars goal))))))
  (est-bindings [_ _ _ _] 1)                    ; a ground test
  (cost         [_ _ _ _] :lookup)              ; one bounded subquery per partner
  ;; Augments a stored `(not (Q a …))` (FactProver) and the other negation provers.
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context]
    (let [[q & args] (negated-tuple goal)
          tax (reasoning/taxonomy kb)
          up  (tax/genls tax q context)
          rs  (into (sorted-set) (map second) (tax/negates-over tax q context))]
      ;; `q` at or below both sides of one declaration holds of nothing
      (if (or (some up rs)
              (some #(believed-literal? kb (cons % args) context) rs))
        [{}]
        []))))

;; ---- aggregation: a reduction over a query's solutions ------------------
;; `(agg/count ?n ?v <body>)` and its four siblings, answered over the registry.
;; See docs/aggregate.md.

(defn- aggregate-violation!
  "File a numeric error in the violations ledger, once per distinct error
  (`violations/report-once`; docs/aggregate.md, \"Numbers, measures\")."
  [kb goal context message detail]
  (violations/report-once kb (merge {:violation :aggregate :sentence goal :context context
                                     :message message}
                                    detail)))

(defn- aggregate-values
  "The values `?v` takes over the body's joined solutions (`conjunction-solutions`), in
  solution order, distinct by the equality closure's representative as `context` reads
  it.  A solution that leaves `?v` unbound contributes nothing.

  `merged-term-pred` is read once per call, so a KB that has merged nothing skips the
  representative lookup.  A compound value takes the recursive `representative-term`,
  since the closure is keyed by symbol and the flat lookup returns a compound unchanged."
  [kb goal v context]
  (let [merged (tax/merged-term-pred (reasoning/taxonomy kb))
        vis    (when merged (res/visible-supporter-fn kb context))]
    (->> (conjunction-solutions kb (sx/conjuncts (sx/aggregate-body goal)) {} context)
         (keep #(get % v))
         (reduce (fn [{:keys [seen out] :as acc} x]
                   (let [k (cond
                             (not merged)    x
                             (symbol? x)     (if (merged x) (res/representative-in kb vis x) x)
                             (sequential? x) (res/representative-term kb vis x)
                             :else           x)]
                     (if (contains? seen k)
                       acc
                       {:seen (conj seen k) :out (conj out x)})))
                 {:seen #{} :out []})
         :out)))

(defn- measure-bounds
  "The values as `[base-unit [lo hi]...]`, or nil when they are not all measures under one
  `[dimension base-unit]` key (`measure-with-support`), the key a comparison requires."
  [kb values context]
  (when (every? measure? values)
    (let [ms   (mapv #(first (measure-with-support kb % context)) values)
          keys (into #{} (map first) ms)]
      (when (= 1 (count keys))
        [(second (first keys)) (mapv (fn [[_ lo hi]] [lo hi]) ms)]))))

(defn- reduce-numbers
  "The reduction of a non-empty numeric value list, over the values sorted so a float
  sum does not depend on solution order (docs/aggregate.md, \"Numbers, measures\")."
  [op xs]
  (let [xs (sort xs)]
    (case op
      :sum (reduce + xs)
      :min (reduce min xs)
      :max (reduce max xs)
      :avg (/ (double (reduce + xs)) (count xs)))))

(defn- reduce-measures
  "The reduction of a non-empty measure list, as a rendered measure, each bound summed
  in sorted order as `reduce-numbers` sums.  `:sum` and `:avg` carry an interval
  through; `:min` and `:max` answer nil unless every value is a point (`lo = hi`)."
  [op unit bounds]
  (let [los (sort (map first bounds)), his (sort (map second bounds))
        n   (count bounds)]
    (case op
      :sum (render-quantity (reduce + los) (reduce + his) unit)
      :avg (render-quantity (/ (double (reduce + los)) n) (/ (double (reduce + his)) n) unit)
      (:min :max)
      (when (every? (fn [[lo hi]] (== lo hi)) bounds)
        (let [f (if (= op :min) min max), m (reduce f los)]
          (render-quantity m m unit))))))

(defn aggregate-value
  "The value an aggregate reduces to over `values`, or nil when there is none: over an
  empty extent `:count` and `:sum` give 0 and the others nil, and a value list that is
  neither all numbers nor measures of one dimension files an `:aggregate` violation and
  gives nil."
  [kb goal op values context]
  (cond
    (= op :count) (count values)
    (empty? values) (when (= op :sum) 0)
    (every? number? values) (reduce-numbers op values)
    :else
    (if-let [[unit bounds] (measure-bounds kb values context)]
      (or (reduce-measures op unit bounds)
          (aggregate-violation! kb goal context
                                (str (first goal) " over interval measures has no "
                                     (name op) " — the bounds are only partially ordered")
                                {:values (vec values)}))
      (aggregate-violation! kb goal context
                            (str (first goal) " needs numbers or measures of one"
                                 " dimension; it cannot reduce " (pr-str (vec values)))
                            {:values (vec values)}))))

(defrecord AggregateProver []
  Prover
  ;; one of the five, a variable in the reduction slot, and every variable still free in
  ;; it one the census body binds for itself (`sx/census-bound-vars`)
  (applicable? [_ _ goal _]
    (and (sx/aggregate? goal)
         (some? (sx/aggregate-value-var goal))
         (let [bound (sx/census-bound-vars (sx/aggregate-body goal))]
           (every? bound (sx/free-vars goal)))))
  (est-bindings [_ _ _ _] 1)                    ; one answer or none, never a stream
  (cost         [_ _ _ _] :compute)             ; the body is exhausted before any answer
  (completeness [_ _ _ _] 100)                  ; not assertible, so nothing else answers
  (solve [_ kb goal context]
    (let [op     (sx/aggregate-functors (first goal))
          v      (sx/aggregate-value-var goal)
          values (aggregate-values kb goal v context)
          result (aggregate-value kb goal op values context)
          n      (second goal)]
      (cond
        (nil? result)      []
        (sx/variable? n)   [{n result}]
        ;; check mode: `==` where both are numbers, so a long and a double agree
        (and (number? n) (number? result)) (if (== n result) [{}] [])
        :else                              (if (= n result) [{}] [])))))

;; ---- modal belief projection --------------------------------------------
;; `(believes Agent P)` is answered by proving `P` inside `Agent`'s own context
;; (`CxAgent<Agent>`) rather than in the asker's — the dual projection
;; `(believes a p) ↔ p-holds-in-CxAgent<a>`.  Nothing here is belief machinery: an
;; agent context is an ordinary context, `P` is an ordinary goal, and the projection is
;; the ordinary registry run with the context swapped.  Two agents believing opposite
;; things raise no contradiction because their contexts share no genlCx ancestor, which
;; is the property the context lattice was built to give.  See `vaelii.impl.modal` and
;; docs/belief.md.  This is a projector, not a modal logic — no K/T/4/5 schema, and a
;; nested `(believes A (believes B P))` gets only what the marker's visibility gives it.

(defn- projected-goal
  "The proposition `p` of a projected attitude prepared as a goal read in the agent's
  context `actx`: its ground NATs reified to the terms `actx` resolves them to, never
  minting (`nat-read/maybe-reify-for-read`), then normalized under `actx`'s merges."
  [kb p actx]
  (res/goal-normal-form kb (nat-read/maybe-reify-for-read kb p actx) actx))

(defrecord BeliefProjectionProver []
  Prover
  ;; Claimed only for a **registered modal predicate** (`(modal_predicate P)` believed
  ;; where the query is asked — read scoped, like `abducible_predicate`), of **arity 2**,
  ;; whose **agent argument is ground** and yields a legal context name, over a
  ;; **sentence-shaped proposition**.  An unbound agent is excluded deliberately: it
  ;; would mean "search every agent's context", a different and far costlier operation
  ;; than a projection into one — `projectable-agent?` is the check, and it refuses a
  ;; `?variable` because the minted context name would carry a `?` no context name may.
  (applicable? [_ kb goal context]
    (and (binary? goal)
         (tax/has-prop? (reasoning/taxonomy kb) :modal (nm/functor goal) context)
         (modal/projectable-agent? (second goal))
         (sequential? (nth goal 2))))
  ;; The planner should order a belief query by what the *inner* query actually costs,
  ;; so delegate to the inner goal's own estimate in the agent context — a complete
  ;; prover's count when one owns the inner shape, else the index model the inner
  ;; functor would get asked directly.  Estimated under the spelling `solve` will ask,
  ;; which is the agent's, or a merge inside the agent context prices a goal the query
  ;; never runs.
  (est-bindings [_ kb goal _]
    (let [actx  (modal/context-of-agent (second goal))
          inner (projected-goal kb (nth goal 2) actx)]
      (or (est-goal kb inner actx) (est-by-functor kb inner))))
  ;; A projection is a sub-query, not a lookup: it runs the inner goal through the whole
  ;; registry before it can answer, which is the `:compute` tier.  The registry expands
  ;; no rule, so the inner query never reaches `:search` — `:compute` is both the floor
  ;; a projection deserves and the ceiling the sub-query can hit.
  (cost         [_ _ _ _] :compute)
  ;; Augments, never replaces.  `(believes A P)` can *also* be a plain stored fact, and
  ;; `believes` is a real relation someone may want to assert — so 50 keeps `FactProver`
  ;; in the union (invariant: `believes` stays assertible), and `distinct` folds the two
  ;; witnesses when both a stored belief and a projected one hold.
  (completeness [_ _ _ _] 50)
  ;; Answer `P` in the agent's context — **the agent's, never the asker's** (`context`
  ;; is discarded here on purpose: the whole point is that a belief is read from where
  ;; the belief lives).  The inner bindings are over `P`'s variables, which are exactly
  ;; the outer goal's arg-2 variables, so they project straight back out.
  ;;
  ;; `P` arrives in the spelling the caller wrote: the read entry points reify and
  ;; normalize the whole goal, and this position is held opaque to both
  ;; (`nat-read/reify-in`, `res/representative-term`), since the asker's merges are not the
  ;; agent's.  So the reify and the normalization owed it happen here, in the **agent's**
  ;; context (`projected-goal`) — which is the ordinary rule that the reader is what
  ;; elects (docs/equality.md), applied to the reader a projection actually has.  An
  ;; identity the agent holds licenses the substitution inside their own belief, and only
  ;; for them.
  (solve [_ kb goal _context]
    (let [actx  (modal/context-of-agent (second goal))
          inner (projected-goal kb (nth goal 2) actx)]
      (solve-goal-with kb (registry kb) (sx/canon inner) actx))))

;; ---- type inference from arg-constrained usage -----------------------

(defn- believed-sentexes-with
  "The sentexes naming `term` that `context` can see and does believe: the term index read,
  filtered as a retrieval is.  Visibility is `res/visible-supporter-fn` (belief, `genlCx`
  inheritance and stored `except`s), nil for a nil or `?var` context, where belief alone
  decides.  A scoped read drops a spelling `context` has retired (`res/retired-for?`).  Lazy,
  so `inferred-types` stops at the first witness."
  [kb term context]
  (let [visible? (res/visible-supporter-fn kb context)
        live?    (or visible? #(jtms/in? (reasoning/tms kb) %))
        merged?  (when visible? (tax/merged-term-pred (reasoning/taxonomy kb)))
        visible  (delay visible?)]
    (cond->> (->> (reads/as-stored-with-term (:index kb) term)
                  (keep #(p/get-sentex (:records kb) %))
                  (filter #(live? (:id %))))
      merged? (remove #(res/retired-for? kb visible merged? (sx/sentence-of %))))))

(defn subsumption-routes
  "Every route of `[handle ctx]` supporters that lets a fact spelled `stored-functor`
  answer a literal on `goal-functor`, read globally: each `genl` route no other route
  covers (`tax/reach-supports`), or the one signed route across `genlInverse` edges.  A
  route resting on an edge supporter a placed defeat or an except can hide somewhere
  (`exc/defeated-anywhere?`, `exc/closure-excepted-anywhere?`) covers only the routes
  resting on that supporter too, so a reader hiding it still reads a route it covered.
  `[[]]`, one route resting on nothing, when the functors are equal or no closure relates
  them."
  [kb goal-functor stored-functor]
  (let [tax (reasoning/taxonomy kb)]
    (or (when (and (symbol? goal-functor) (symbol? stored-functor)
                   (not= goal-functor stored-functor))
          (not-empty
           (if (contains? (tax/genls-global tax stored-functor) goal-functor)
             (tax/reach-supports tax :genl stored-functor goal-functor nil nil
                                 #(or (exc/defeated-anywhere? kb %)
                                      (exc/closure-excepted-anywhere? kb %)))
             (let [[st sw] (tax/signed-closure tax :up stored-functor nil)]
               (when-let [r (cond (contains? st goal-functor)
                                  (tax/signed-reach-support tax stored-functor goal-functor false nil nil)
                                  (contains? sw goal-functor)
                                  (tax/signed-reach-support tax stored-functor goal-functor true nil nil))]
                 [r])))))
        [[]])))

(defn- type-derivations
  "Every derivation of a type an individual `x` must have because it fills an arg-constrained
  argument of a believed relation, as `[type usage c P' T']`: the type, the believed sentex
  `(P .. x@n ..)`, and the `:instance` entry `c` of `res/arg-constraints-at` covering position
  `n` (an `(arg P' n T')`, or an `(argAndRest P' m T')` / `(args P' T')` reaching `n`), where
  `P'` is `P` or a super-predicate and `type` is `T'` or a supertype.  This is `arg` read as
  an inference: Muffet eats Bone1 and eat's 2nd argument is food, so Bone1 is food.

  The declarations are the reader `assert` uses (`res/arg-constraints-at`), `P`'s own and the
  visible super-predicates', so `ask` types what `assert` refuses for being ill-typed.  The
  declaration (`matches-visible`) and the tuple (`believed-sentexes-with`) are both read from
  the asking context.  Lazy, so a ground membership test stops at the first derivation."
  [kb x context]
  (for [s (believed-sentexes-with kb x context)
        :let [sen (:sentence s) pred (nm/functor sen) as (vec (nm/args sen))]
        :when (and (symbol? pred) (seq as))
        n (range 1 (inc (count as)))
        :when (= x (nth as (dec n)))
        {:keys [type kind via] :as c} (res/arg-constraints-at kb pred context n)
        :when (= :instance kind)
        super (tax/genls (reasoning/taxonomy kb) type context)]
    [super s c via type]))

(defn- inferred-types
  "The types `type-derivations` gives `x`, lazy and deduped: `distinct` over the lazy
  derivations, so a *ground* `(Type x)` test (ArgTypeProver.solve's `some`) realizes the
  believed-sentex scan only as far as the first sentex witnessing the type it seeks,
  instead of computing x's whole type set.  The open `(?t x)` case consumes the whole
  seq."
  [kb x context]
  (distinct (map first (type-derivations kb x context))))

(defn- constraint-declarations
  "The declarations `context` sees that state the `res/arg-constraints` entry `c`, as
  `[spelling handle]` pairs: `(arg P n T)` for one position and `(argAndRest P n T)` for a
  tail, the twin an `(args P T)` declaration's forward rule stores among them."
  [kb {:keys [from to type via]} context]
  (let [k (if (= from to) 'arg 'argAndRest)]
    (map (fn [[h]] [k h]) (res/matches-visible kb (list k via from type) context))))

(defn- derivation-supports
  "The handle sets a `type-derivations` entry rests on, one per declaration stating its
  constraint and combination of routes: the usage and the declaration, with a route
  (`subsumption-routes`) from the usage's predicate to the declared one, from the declared
  type to the derived one, and from a spec of the declaration's spelling (`arg` or
  `argAndRest`) it is stored on to that spelling."
  [kb [super s c declared t'] context]
  (let [routes #(subsumption-routes kb %1 %2)]
    (for [[k h] (constraint-declarations kb c context)
          r1 (routes declared (nm/functor (:sentence s)))
          r2 (routes super t')
          r3 (routes k (nm/functor (:sentence (p/get-sentex (:records kb) h))))]
      (into #{(:id s) h} (map first) (concat r1 r2 r3)))))

(defn- uncovered-declarations
  "The `(arg P n T')` declarations `context` sees whose `T'` is `t` or a spec of it and
  whose memberships no stored one covers, as distinct `[P n]` pairs: every such
  declaration under the constraint-only reading, and under the entailing reading those
  whose `T'` `arity/mintable-type?` refuses, since the entailment mints the rest.  A spec
  no fact names at argument 3 is skipped on one count read."
  [kb t context]
  (let [tax     (reasoning/taxonomy kb)
        ix      (:index kb)
        minted? (if argument/*assertive-arg-types?* #(arity/mintable-type? kb %) (constantly false))]
    (distinct
     (for [s (tax/specs tax t context)
           :when (and (symbol? s) (pos? (reads/stored-count-with-arg-global ix 3 s)) (not (minted? s)))
           [_ b] (res/matches-visible kb (list 'arg '?p '?n s) context)
           :let [p (get b '?p) n (get b '?n)]
           :when (and (symbol? p) (pos-int? n))]
       [p n]))))

(defn- open-candidates
  "The individuals at argument `n` of a stored fact of `P` or a predicate below it, for
  each `[P n]` of `uncovered-declarations`, stated in a context `context` sees: the
  distinct atoms at the position (`reads/as-stored-atoms-at-global`, as the trie keys the
  context last), each narrowed to `context`'s ancestor set.  A candidate set, which
  `ArgTypeProver` filters through the ground test."
  [kb t context]
  (let [tax  (reasoning/taxonomy kb)
        ix   (:index kb)
        seen (when (res/visible-supporter-fn kb context) (set (tax/context-up tax context)))]
    (distinct
     (for [[p n] (uncovered-declarations kb t context)
           p'    (tax/specs tax p context)
           a     (reads/as-stored-atoms-at-global ix p' n)
           :when (and (nm/individual? a)
                      (or (nil? seen) (seq (reads/as-stored-contexts-with-arg-in ix p' n a seen))))]
       a))))

(defn- open-type-goal?
  "Is `goal` `(t ?x)`, a constant type over an open argument, with a declaration
  `uncovered-declarations` finds?"
  [kb goal context]
  (let [[t x] goal]
    (and (symbol? t) (not (pvar? t)) (pvar? x)
         (boolean (seq (uncovered-declarations kb t context))))))

(defrecord ArgTypeProver []
  Prover
  ;; `(Type Individual)`, and `(Type ?x)` where a declaration no stored membership covers
  ;; can type an individual
  (applicable? [_ kb goal context]
    (and (sequential? goal) (= 1 (count (rest goal)))
         (or (nm/individual? (second goal)) (open-type-goal? kb goal context))))
  (est-bindings [_ _ _ _] 3)
  (cost         [_ _ _ _] :lookup)               ; lazy scan of the individual's believed sentexes — the ground test stops at the first witness
  (completeness [_ _ _ _] 50)                  ; augments stored type facts
  (solve [_ kb goal context]
    (let [[t x] goal]
      (if (pvar? x)
        ;; each candidate kept by the ground test, so the open answers are the ground ones
        (for [a (open-candidates kb t context)
              :when (some #(= t %) (inferred-types kb a context))]
          {x a})
        (let [types (inferred-types kb x context)]
          (if (pvar? t)
            (map (fn [ty] {t ty}) types)
            ;; ground `(Type x)`: `some` short-circuits the lazy `inferred-types` at the
            ;; first sentex that witnesses `t`, so a ground membership never types x in full
            (if (some #(= t %) types) [{}] []))))))

  SupportingProver
  ;; Both sets are empty, for `TransitivePredicateProver`'s reason: the functors answered
  ;; are every type and the functors read every predicate, which no constant names.
  ;; `vantage/post-hoc` reaches `solve-with-support` through `placeable-prover?`.
  (support-functors [_] #{})
  (support-sources  [_] #{})
  ;; One pair per derivation and route rather than per binding, so a binding two usages
  ;; derive appears once for each, with its own handles: a placement that drops one keeps
  ;; the other.  The bindings in order of first appearance are `solve`'s.  An open
  ;; argument's answer carries the support the ground goal on its binding carries.
  (solve-with-support [_ kb goal context]
    (let [[t x] goal]
      (distinct
       (for [a   (if (pvar? x) (open-candidates kb t context) [x])
             d   (type-derivations kb a context)
             :when (or (pvar? t) (= t (first d)))
             sup (derivation-supports kb d context)]
         [(cond (pvar? t) {t (first d)} (pvar? x) {x a} :else {}) sup])))))

;; ---- the argument-type meta-predicates, answered up genl ----------------
;; `(arg petMammal 1 animal)` succeeds off a stored `(arg petMammal 1 mammal)` when
;; `(genl mammal animal)`, as `check` walks it, so `assert` and `ask` agree.  A bounded
;; closure walk answers here instead of declaring the meta-predicates `transitiveInArg`,
;; which would route every `arg`/`genlArg` lookup through the preservation prover.
;;
;; The predicate position reaches down (`constraining-predicates`).  An unconditional type
;; reaches up: `arg`/`genlArg` position 3 and `interArg`'s target position 5.  `interArg`'s
;; trigger (position 3) is contravariant and reaches down: a stored `(interArg P n animal m U)`
;; answers `(interArg P n mammal m U)` and never `(… n thing m U)`.  The reverse is unsound
;; and incomplete against `check`.  On-demand and non-materializing, so it follows belief.
;; `arity` is not here: a sub-predicate may carry its own signature, and
;; `arity/relation-length` holds a silent one to its supers.
(def ^:private meta-constraint-shape
  "By functor: the goal-list index of the predicate, the position-number indices that must
  match a stored declaration exactly, the type indices that reach UP `genl` (covariant) and
  those that reach DOWN (contravariant).  Only `interArg`'s trigger is contravariant.  The
  homogeneity constraints `interArgs` / `interArgAndRest` hold their type in `:fixed`, since
  one type that is trigger and target reaches neither way.

  The table covers the whole `:argument-constraint` family, `quotedArg` included, so `ask`
  agrees with `checks/declaration-reader` and the entry point.  Answering `quotedArg` is not
  entailing it: nothing is minted from one (docs/argtypes.md, \"The quoted twin\").  The
  variance is this prover's reading and stays here; the key set is enrolment,
  `meta-constraint-functors`, held to the family by `predicates/check-facets`'s
  `:family-list` rule."
  '{arg      {:pred 1 :fixed [2] :types-up [3]}
    genlArg     {:pred 1 :fixed [2] :types-up [3]}
    quotedArg   {:pred 1 :fixed [2] :types-up [3]}
    interArg {:pred 1 :fixed [2 4] :types-up [5] :types-down [3]}
    ;; `argArg` names positions only, so both are fixed and only the predicate descends
    argArg   {:pred 1 :fixed [2 3]}
    ;; `interArgEqual`'s trigger is a value compared by `=`, so it is fixed with both
    ;; positions, and its target type reads up genl as `arg`'s does
    interArgEqual {:pred 1 :fixed [2 3 4] :types-up [5]}
    ;; the covering constraints: an every-position form has no fixed position, a tail
    ;; form fixes its start and reads its one type up genl as the singular forms do
    args           {:pred 1 :types-up [2]}
    argsGenl        {:pred 1 :types-up [2]}
    argAndRest      {:pred 1 :fixed [2] :types-up [3]}
    argAndRestGenl  {:pred 1 :fixed [2] :types-up [3]}
    quotedArgAndRest {:pred 1 :fixed [2] :types-up [3]}
    ;; the homogeneity constraints: the one type is trigger and target at once, so it is
    ;; covariant as a target and contravariant as a trigger and reaches neither way —
    ;; `(interArgs R animal)` convicts a reptile beside a plant that `(interArgs R
    ;; mammal)` admits, and the narrower one convicts a mammal beside a reptile the wider
    ;; one admits.  The type and the start match a stored declaration exactly, and only
    ;; the predicate position descends.
    interArgs       {:pred 1 :fixed [2]}
    interArgAndRest {:pred 1 :fixed [2 3]}})

(def meta-constraint-functors
  "The argument constraints this prover answers along the `genl` closure, as a set —
  `meta-constraint-shape`'s keys.

  Public because it is the second list that reads the `:argument-constraint` family
  **as a family**, and `predicates/check-facets` holds it and `checks/constraint-
  declaration-functors` to enumerating exactly it.  A spelling the entry point reads up
  `res/constraining-predicates` and this table omits is one declaration meaning one thing
  to `assert` and another to `ask` — which is what happened to `quotedArg`."
  (set (keys meta-constraint-shape)))

(defn- meta-generalizes?
  "Does a stored declaration on `goal`'s predicate or a super-predicate answer `goal`
  once each type position is read the way its variance allows — covariant positions up
  the `genl` closure, the contravariant trigger down it?"
  [kb goal context]
  (when-let [{:keys [pred fixed types-up types-down]} (meta-constraint-shape (nm/functor goal))]
    (let [tax  (reasoning/taxonomy kb)
          k    (nm/functor goal)
          gvec (vec goal)
          qp   (nth gvec pred)]
      (boolean
       (some
        (fn [p']
          (let [probe (cons k (map (fn [i] (if (= i pred) p' (symbol (str "?g" i))))
                                   (range 1 (count gvec))))]
            (some
             (fn [[_h b]]
               (let [sval (fn [i] (if (= i pred) p' (get b (symbol (str "?g" i)))))]
                 (and (every? #(= (sval %) (nth gvec %)) fixed)
                      ;; covariant: the stored type sits at or below the queried one
                      (every? #(tax/genl? tax (sval %) (nth gvec %) context) types-up)
                      ;; contravariant: the queried type sits at or below the stored one
                      (every? #(tax/genl? tax (nth gvec %) (sval %) context) types-down))))
             (res/matches-visible kb probe context))))
        (res/constraining-predicates kb k qp context))))))

(defrecord MetaConstraintProver []   ; (arg/genlArg/quotedArg/interArg P n T …) up the genl closure
  Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal)
         (contains? meta-constraint-shape (nm/functor goal))
         (empty? (sx/free-vars goal))))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :compute)   ; a closure walk, not a lookup — like TransitiveInArgProver
  (completeness [_ _ _ _] 50)         ; augments FactProver's stored match, never shadows it
  (solve [_ kb goal context]
    (if (meta-generalizes? kb goal context) [{}] [])))

;; ---- rules (backward chaining through the engine) -----------------------

(defn candidate-rules
  "Rules concluding the goal's predicate or a spec of it, restricted to the
  backward-capable ones (the consequent index also holds forward-only and inert rules).  A
  rule concluding a subtype answers a supertype goal (`res/concluding-rule-handles`), and
  `subsuming-unify` binds the goal variable to the subtype instance.  Each carries its
  `exceptWhen` guard (`parse-rule`).

  A rule is not a candidate when the asking context cannot see it (`res/rule-visible-from?`),
  when the KB no longer believes it (`res/rule-believed?`), or when a believed visibility
  `except` hides it from the asking context (`exc/hidden-fn`, built once per goal and nil when
  nothing is hidden).

  The result is in content order, `[sentence context]` under `nm/compare-form`, since the index
  answers in handle order and `prove-within`'s `:max-results` and the node engine's frontier
  truncate on this list (docs/nmtms.md).  The sentence is the key, so nothing is memoized;
  `:context` joins it because one sentence stated in two contexts is two rules."
  [kb goal context]
  (when (sequential? goal)
    (let [hidden? (exc/hidden-fn kb context)
          ;; the ancestor set `rule-visible-from?` reads, so the index reads no rule the
          ;; filter below would drop
          visible (when (and (symbol? context) (not (sx/variable? context)))
                    (tax/context-up (reasoning/taxonomy kb) context))]
      (->> (res/concluding-rule-handles kb (first goal) context visible)
           (map #(p/get-sentex (:records kb) %))
           (filter rules/backward-sentex?)
           (filter #(res/rule-believed? kb (:id %)))
           (filter #(res/rule-visible-from? kb context (:context %)))
           (remove #(and hidden? (hidden? (:id %))))
           (nm/sort-by-content-key (juxt sx/sentence-of :context))
           (map #(parse-rule kb % context))))))

;; ---- the engine ---------------------------------------------------------

(def default-provers
  [(->TransitivityProver) (->DisjointnessProver) (->CommonGenlProver)
   (->TransitivePredicateProver) (->TransitiveInArgProver) (->SymmetricProver) (->InverseProver) (->ReflexiveProver)
   (->EvaluableProver) (->ExpressionKindProver) (->NonemptyProver) (->ResultTypeProver) (->ArgPositionProver) (->DifferentProver) (->EqualityProver) (->EvaluateProver) (->QuantityProver)
   (->AdmitsArgnumProver)
   (->UnknownProver) (->ThereExistsProver) (->ForallProver) (->ClosedExtentProver)
   (->DefnSufficientProver) (->DefnNecessaryNegationProver) (->DisjointnessNegationProver)
   (->NegatesProver)
   (->StructureProver)
   (->CoveringProver)
   (->AggregateProver) (->BeliefProjectionProver)
   ;; FactProver before ArgTypeProver: both are :lookup / completeness 50, so vector
   ;; order breaks the stable-sort tie in the union path (`solve-goal-with`).  A stored
   ;; fact is the cheaper witness for a ground `(Type Individual)`, and the union is
   ;; lazy + `distinct` — so a consumer taking one answer gets FactProver's stored
   ;; match before ArgTypeProver.solve's inferred-type scan is ever forced.
   ;; MetaConstraintProver sits with them: it too augments FactProver (the stored
   ;; declaration is the cheaper witness) and answers the genl-generalizations on top.
   (->FactProver) (->MetaConstraintProver) (->ArgTypeProver)])

(defn registry [kb] (if-let [pv (:provers kb)] @pv default-provers))

;; ---- the optional reasoners ----------------------------------------------
;; Resolved at runtime by name, so loading this namespace loads none of the leaf
;; algebras (docs/qcn.md).  `vaelii.core/reasoners` and `add-reasoner` are the public
;; surface; a KB records the names it registered (`vaelii.impl.kb/add-reasoners!`).

(def reasoner-vars
  "The reasoners a KB can register by name, and the var holding each one's constructor.
  `vaelii.core/reasoner` documents each one."
  '{:rcc8        vaelii.impl.space/spatial-prover
    :cardinal    vaelii.impl.orientation/orientation-prover
    :relative    vaelii.impl.relative/relative-prover
    :distance    vaelii.impl.distance/distance-prover
    :allen       vaelii.impl.interval/allen-prover
    :point       vaelii.impl.point/point-prover
    :duration    vaelii.impl.duration/duration-prover
    :metric-time vaelii.impl.stp/stp-prover
    :sign        vaelii.impl.sign/sign-prover
    :calendar    vaelii.impl.calendar/calendar-prover
    :includes-instant vaelii.impl.point/includes-instant-prover
    :brave-cautious vaelii.impl.asp.prover/brave-cautious-prover})

(defn reasoner-names
  "The names of the optional reasoners, sorted."
  []
  (vec (sort (keys reasoner-vars))))

(defn check-reasoner-name!
  "`nm`, or a refusal naming the reasoners there are.  `:unknown-option`: naming a
  reasoner that does not exist is a bad argument from a caller, never something a
  sentence can be checked into."
  [nm]
  (when-not (contains? reasoner-vars nm)
    (throw (ex-info (str "no such reasoner: " (pr-str nm) " — want one of "
                         (str/join ", " (map pr-str (reasoner-names))))
                    {:type :unknown-option :mismatch :bad-value :reasoner nm
                     :known (reasoner-names)})))
  nm)

(defn reasoner
  "The prover the reasoner named `nm` registers, or `check-reasoner-name!`'s refusal."
  [nm]
  ((requiring-resolve (reasoner-vars (check-reasoner-name! nm)))))

;; ---- which provers are even worth asking ---------------------------------

(defn fact-prover?
  "Is this *the* stored-fact prover — the one that answers by matching the store, and
  whose answers therefore each name a sentex with a context?"
  [pr] (instance? FactProver pr))

(defn applicable-provers
  "The applicable provers for `goal`, in registry order.

  One function rather than three copies of the same `filterv`: `solve-goal-with`
  decides what runs, `est-goal` decides whether a complete estimate exists, and `plan`
  reports both — so a sweep that drifted between them would make the diagnostic lie
  about the dispatch it is there to explain.  A literal holding `sx/no-match` at a term
  position (`res/names-no-match?`) names no term there, so only the stored-fact prover
  reads it, and it matches nothing (docs/nat.md, Read path)."
  [kb provers goal context]
  (filterv #(budget/checked-call
             (fn [] (applicable? % kb goal context)))
           (if (res/names-no-match? kb goal) (filterv fact-prover? provers) provers)))

;; Membership tests for the lookup-to-query stack (vaelii.impl.levels), which runs
;; the engine over a *subset* of the registry: level 5 with the transitive provers
;; alone, level 6 with everything except backward chaining.  Knowing which record is
;; which belongs here, next to the records.

(defn transitive-prover?
  "Does this prover compute a transitive closure — genl/genlCx through the cached
  taxonomy, or a predicate declared `(transitive P)`?"
  [pr] (or (instance? TransitivityProver pr) (instance? TransitivePredicateProver pr)))

(defn placeable-prover?
  "Does every answer `pr` gives name the stored sentexes it rests on, one answer per
  derivation, and rest on no absence?  The stored-fact prover's answers each name a
  match; `ArgTypeProver`'s carry their usage and declaration (`solve-with-support`).  Both
  give one answer per `genl` route a subsumption crosses (`subsumption-routes`).

  `vaelii.impl.vantage` asks it of every applicable prover to decide whether a literal is
  inside post-hoc placement's domain.  A walk over stored hops is outside it, since its
  support names one chain where several chains may derive the pair.  An answer resting on
  an absence is outside it too: the unscoped pass sees facts a reader does not, so it can
  lose an answer the reader gives."
  [pr] (or (instance? FactProver pr) (instance? ArgTypeProver pr)))

;; ---- which registered provers can say what their answer rests on ---------

(defonce ^{:private true
           :doc "`[registry-vector {:answers #{functor} :sources #{functor}}]`, memoized against the
  registry's **identity**.

  A volatile pair rather than a map, for `qcn-kb/registered-calculi`'s reason: the
  overwhelmingly common registry is the `default-provers` vector itself, so one entry
  answers every KB that registered nothing *and* every stretch of writing on one that
  did.  A `swap!` on the registry produces a new value, so it simply misses and
  recomputes; last write wins and the pair is written as one value, so a lost race costs a
  recomputation and cannot answer wrongly."}
  registry-support
  (volatile! nil))

(defn- support-summary
  "The registered `SupportingProver`s' functors, as `{:answers … :sources … :reading …
  :provers …}`: what they answer with support, what they read to do it, `{source
  answers}` pairing each source with the functors of the provers reading it, and the
  provers themselves.

  A miss is a `cap/has?` scan of the registry plus two set unions; a
  hit is a deref and an identity compare.  Empty on both keys for the shipped registry
  minus nothing — `QuantityProver` is in `default-provers`, so the answers set is the
  measure comparisons even for a KB that registered no prover of its own."
  [kb]
  (let [pv (registry kb)
        [reg answer] @registry-support]
    (if (identical? pv reg)
      answer
      (let [ps (filterv #(cap/has? SupportingProver %) pv)
            v  {:answers (into #{} (mapcat support-functors) ps)
                :sources (into #{} (mapcat support-sources) ps)
                :reading (reduce (fn [m pr]
                                   (let [fs (support-functors pr)]
                                     (reduce #(update %1 %2 (fnil into #{}) fs)
                                             m (support-sources pr))))
                                 {} ps)
                :provers ps}]
        (vreset! registry-support [pv v])
        v))))

(defn support-answered-preds
  "The functors a registered `SupportingProver` answers — the antecedents forward chaining
  discharges through `solve-goal-with-support` so the firing carries what the answer rested
  on."
  [kb]
  (:answers (support-summary kb)))

(defn support-est-override
  "An `:est-override` for `vaelii.impl.plan/order` that costs a literal a registered
  `SupportingProver` answers by that prover's `est-bindings`, the largest where several
  apply, and returns nil for every other goal so the index model ranks it.

  Forward chaining (`vaelii.impl.chain/planned-join`) plans with this beside
  `evaluatable-est-override`.  The join answers such a literal by computation as well as
  by matching, so its stored-row count is not its fan-out: `includesInstant` stores no rows
  and reports `deferred-est` for an open argument, which places it after its binders."
  [kb]
  (let [{:keys [answers provers]} (support-summary kb)]
    (fn [goal bound]
      (when (and (sequential? goal) (contains? answers (first goal)))
        (let [ps   (filterv #(and (contains? (support-functors %) (first goal))
                                  (applicable? % kb goal '?ctx))
                            provers)
              ests (map #(est-bindings % kb goal '?ctx) ps)]
          (when (seq ests) (est-under (reduce max ests) ps kb goal '?ctx bound)))))))

(defn separation-est-override
  "An `:est-override` for `vaelii.impl.plan/order` that costs a `disjoint` literal by
  `DisjointnessProver`'s `est-bindings`, and returns nil for every other goal.  Forward
  chaining (`vaelii.impl.chain/planned-join`) answers the literal from the separations as
  well as from the stored sentences, so its stored-row count is not its fan-out.  A goal
  with both ends open waits for a binder (`chain/open-ends`) and is answered from the
  stored sentences alone, so it takes the index model's estimate, which costs no read of
  the separation declarations."
  [kb]
  (fn [goal _bound]
    (when (and (binary-pred? goal 'disjoint)
               (or (ground? (second goal)) (ground? (nth goal 2))))
      (est-bindings (->DisjointnessProver) kb goal '?ctx))))

(defn relation-moved-answers
  "The functors the registered `ExpressionKindProver` answers that what the KB states of a
  relation can move: those at or above a kind `stated-kinds` gives, read globally because
  the re-join reads every context.  Nil when no `ExpressionKindProver` is registered."
  [kb]
  (when-let [pr (first (filter #(instance? ExpressionKindProver %) (:provers (support-summary kb))))]
    (let [tx (reasoning/taxonomy kb)
          fs (support-functors pr)]
      (not-empty (into #{} (mapcat #(tax/genls-global-among tx % fs)) stated-kind-floor)))))

(defn quoted-anywhere?
  "Does a stored sentex hold a quoting function's application (`sx/quoting-functors`)?
  One term-index read per quoting function, belief unread (`reads/as-stored-with-term`)."
  [kb]
  (boolean (some #(seq (reads/as-stored-with-term (:index kb) %)) sx/quoting-functors)))

(defn quoted-head?
  "Does a stored sentex hold a quoted application `(F (r …))` whose head is `r`, `F` a
  quoting function?  One term-index intersection per quoting function names the
  candidates (`reads/as-stored-with-terms`), and each candidate's record is read for the
  form; belief is unread."
  [kb r]
  (let [recs (:records kb)]
    (boolean
     (some (fn [f]
             (some (fn [h]
                     (when-let [rec (p/get-sentex recs h)]
                       (some #(and (sequential? %) (= 2 (count %)) (= f (first %))
                                   (sequential? (second %)) (= r (first (second %))))
                             (tree-seq sequential? seq (sx/sentence-of rec)))))
                   (reads/as-stored-with-terms (:index kb) [f r])))
           sx/quoting-functors))))

(defn- relation-membership?
  "Is `s` a membership `(T r)` of a symbol in a type `T` at or below `relation`, which can
  move `r`'s kind (`stated-kinds`), with a quoted application headed by `r` stored
  (`quoted-head?`)?  The type test is a lookup in `relation`'s subtypes, read globally
  (`tax/specs-global`), which the taxonomy holds until a `genl` edge moves, and only a
  membership that passes it reads the term index."
  [kb s]
  (and (seq? s) (= 2 (count s))
       (let [t (first s)]
         (and (symbol? t) (not (sx/variable? t)) (symbol? (second s))
              (contains? (tax/specs-global (reasoning/taxonomy kb) 'relation) t)
              (quoted-head? kb (second s))))))

(defn support-answers-reading
  "The functors answered by the registered `SupportingProver`s that read `src`, or nil
  when none reads it: the answers the datum `s`, on `src`, can move.  A supporter reads
  a `genl` path up to the goal's predicate, so an edge `s` installs
  (`tax/installed-edges`) moves only the answers at or above the edge's upper end,
  read globally because the re-join reads every context.  The test walks down from the
  answers (`tax/genls-global-among`), so its cost does not grow with the depth of the
  edge's upper end.  A membership that can move a relation's kind
  (`relation-membership?`) moves `relation-moved-answers` whatever its functor."
  [kb src s]
  (let [read (when-let [answers (get (:reading (support-summary kb)) src)]
               (if (contains? tax/edge-installing-functors src)
                 (let [tx (reasoning/taxonomy kb)]
                   (not-empty (into #{} (mapcat (fn [[_ super]] (tax/genls-global-among tx super answers)))
                                    (tax/installed-edges s))))
                 answers))]
    (if-let [moved (when (relation-membership? kb s) (relation-moved-answers kb))]
      (into (or read #{}) moved)
      read)))

(defn support-delta-source?
  "Does the datum `s`, on `src`, move a `SupportingProver`'s answers only as a supporter
  of them: is `src` a functor some registered supporter reads, not one a `genl` edge is
  read off (`tax/edge-installing-functors`), and `s` not a membership moving a relation's
  kind (`relation-membership?`)?  Then an answer `s` makes newly given names `s` in its
  support, by the protocol's second obligation (`prover-types/SupportingProver`), and
  the re-join `s` owes keeps only the rows that rest on it (`chain/run-owed-rejoin`).
  The caller asks it of a positive datum only: a negation defeats a row, and the answer
  it widens rests on what remains."
  [kb src s]
  (boolean (and (contains? (:reading (support-summary kb)) src)
                (not (contains? tax/edge-installing-functors src))
                (not (relation-membership? kb s)))))

(defn support-source-preds
  "The functors a registered `SupportingProver` *reads*.  A datum on one of these moves an
  answer no antecedent of the rule names, so it re-joins the rules carrying a
  `support-answered-preds` antecedent (`chain/fire-rules-for`) rather than triggering them
  — which is what makes such a firing independent of whether the table or the facts
  arrived first."
  [kb]
  (:sources (support-summary kb)))

(defn held-contexts
  "The contexts holding a stored fact on one of `preds`, either polarity, or one of the
  sentexes the handles `also` name, as a set: each predicate's predicate-extent children,
  with no record read, and one record fetch per handle of `also`.

  Read from the store rather than from belief, which over-approximates in the safe
  direction: a context whose only such fact is defeated is listed, reads nothing, and
  answers nothing."
  [kb preds also]
  (let [idx  (:index kb)
        recs (:records kb)]
    (-> #{}
        (into (mapcat #(first (reads/as-stored-contexts-with-functor-global idx %))) preds)
        (into (keep (fn [h] (:context (p/get-sentex recs h)))) also))))

(defn source-contexts
  "Every context worth answering a support-carrying goal at, given `preds`: the contexts
  holding one of those facts (`held-contexts`), and the contexts where two or more of them meet
  (`tax/meet-closure`).  A caller passes the whole registry's sources (`support-source-preds`),
  which over-approximates harmlessly and shares one read across a run.

  A reading is what a reader sees through its `genlCx` ancestor set, so a context inheriting
  two contexts closes a metric network neither closes alone (`qcn-kb/reader-contexts`).  A
  wildcard context would read every context into one reading that no reader has.  Resident on
  the KB's `:qcn` atom, keyed by the change clock.  `also` names further handles whose contexts
  are parties to the meet: declarations a reading needs beside its facts."
  ([kb preds] (source-contexts kb preds nil))
  ([kb preds also]
   (observe/cached
    (reasoning/qcn kb) [::source-contexts preds also]
    (fn [_stale]
      (tax/meet-closure (reasoning/taxonomy kb) (held-contexts kb preds also))))))

(defn- adjacent-edge-contexts
  "The contexts supporting a `genl` edge out of each type of `subs` or into each type of
  `supers`, through every active edge: one adjacency read per type and one supporter
  read per edge."
  [tx subs supers]
  (into #{}
        (comp cat (remove nil?))
        (concat (for [a subs, b (tax/direct-genls-global tx a)] (tax/edge-contexts tx :genl [a b]))
                (for [b supers, a (tax/direct-specs-global tx b)] (tax/edge-contexts tx :genl [a b])))))

(defn nonempty-contexts
  "The contexts a forward join asks the ground `(nonempty C)` `g` at, or nil for any other
  goal: `source-contexts` over `preds` with the subtypes of `C` added, so every context
  holding a member reads the answer, and the contexts stating a `genl` edge into one of
  those subtypes are parties to the meet.  The subtypes are read over every context, and
  each context asks the answer from its own vantage."
  [kb preds g]
  (when-let [c (nonempty-type g)]
    (let [tx (reasoning/taxonomy kb)
          ss (tax/specs-global tx c)]
      (tax/meet-closure tx (into (held-contexts kb (into (set preds) ss) nil)
                                 (adjacent-edge-contexts tx nil ss))))))

(defn nonempty-source?
  "Can `s` arriving, leaving or moving in belief move what a registered `NonemptyProver`
  answers?  True of a membership `(T x)` of a ground term in a constant type, of a
  sentence installing a `genl` edge (`tax/installed-edges`) and of a `genlCx` edge.  A
  shape test and a scan of the registered supporters; no index read."
  [kb s]
  (boolean
   (and (seq? s)
        (let [f (first s)]
          (or (and (= 2 (count s)) (symbol? f) (not (sx/variable? f)) (not= sx/not-functor f)
                   (sx/ground-term? (second s)))
              (= 'genlCx f)
              (and (contains? tax/edge-installing-functors f) (seq (tax/installed-edges s)))))
        (some #(instance? NonemptyProver %) (:provers (support-summary kb))))))

(defn- supporter-contexts
  "The contexts stating a supporter of one of the taxonomy keys `ks`, believed or not; a
  supporter with no recorded context adds none."
  [tx ks]
  (into #{} (comp (mapcat #(vals (tax/supporters tx %))) (remove nil?)) ks))

(defn- prover-ingredient-contexts
  "The contexts holding a stored fact that every answer `pr` gives `goal` rests on, or
  nil for a prover this does not describe: one arm per prover in docs/contexts.md's
  ingredient table.  A superset is harmless; a context missed is a reader the joint
  reading never asks.  The `genl` closures, the inverse partners and the `negates`
  declarations are read through every edge: a context holding a fact its own readers
  cannot use is asked, and answers nothing."
  [kb pr goal]
  (let [tx (reasoning/taxonomy kb)
        f  (nm/functor goal)
        held #(held-contexts kb % nil)]
    (cond
      (instance? ArgTypeProver pr)
      (if (pvar? (second goal))
        (held (into #{} (mapcat #(tax/specs-global tx (first %)))
                    (uncovered-declarations kb f '?ctx)))
        (held-contexts kb nil (reads/as-stored-with-term (:index kb) (second goal))))

      (instance? SymmetricProver pr) (held (tax/specs-global tx f))
      (instance? TransitivePredicateProver pr)
      (held (into (tax/specs-global tx f) (tax/inverses-under tx f)))
      (instance? InverseProver pr)
      (held (if (sx/negation? goal)
              (into #{} (mapcat #(tax/genls-global tx %)) (tax/inverses-over tx (first (second goal))))
              (into #{} (mapcat #(tax/specs-global tx %)) (tax/inverses-under tx f))))
      (instance? MetaConstraintProver pr) (held #{f})
      (instance? ReflexiveProver pr) (set (vals (tax/prop-supporter-contexts tx :reflexive f)))

      (and (instance? TransitivityProver pr) (= 'genl f))
      (let [[_ a b] goal]
        (if (or (ground? a) (ground? b))
          (adjacent-edge-contexts tx (when (ground? a) [a]) (when (ground? b) [b]))
          (held tax/edge-installing-functors)))
      (instance? CommonGenlProver pr)
      (let [[_ _ types] (or (common-genl-goal goal) (common-genl-negation goal))]
        (adjacent-edge-contexts tx types nil))
      (or (instance? DisjointnessProver pr) (instance? DisjointnessNegationProver pr))
      (held (conj tax/separation-functors 'disjoint))
      (instance? NegatesProver pr)
      (supporter-contexts tx (map (fn [[p r]] (tax/negates-key p r))
                                  (tax/negates-over tx (first (second goal)))))
      (instance? CoveringProver pr)
      (supporter-contexts tx (map (fn [[whole parts kind]] (tax/cover-key whole parts kind))
                                  (tax/covers-naming tx f)))
      (instance? ClosedExtentProver pr) (held '#{closed_extent_predicate closedExtentForArg})
      (instance? DefnSufficientProver pr) (held '#{defnSufficient defnIff})
      (instance? DefnNecessaryNegationProver pr) (held '#{defnNecessary defnIff})
      (instance? TransitiveInArgProver pr)
      (into #{} (keep :in)
            (inherit/positions kb (nm/functor (second (inherit/goal-verdict goal))) '?ctx))
      (instance? EqualityProver pr)
      (held-contexts kb '#{sameAs equals rewriteOf} (map :handle (tax/rewrite-rules tx)))

      ;; a calculus prover (`qcn-kb/CalculusProver`):
      ;; the facts that put a node into its network
      (map? (:calculus pr)) (held (:context-predicates (:calculus pr)))
      (cap/has? SupportingProver pr) (held (support-sources pr)))))

(defn ingredient-contexts
  "The contexts holding a stored fact some answer of a computed prover to `goal` rests on:
  `prover-ingredient-contexts` of every prover `goal` dispatches to at `'?ctx` other than the
  stored-fact prover.  A context outside the `genlCx` lattice sees only itself, so it
  answers a computed goal only when it holds every ingredient; these are the contexts
  `vantage/readers` adds for it."
  [kb goal]
  (when (sequential? goal)
    (into #{}
          (comp (remove fact-prover?)
                (mapcat #(prover-ingredient-contexts kb % goal)))
          (applicable-provers kb (registry kb) goal '?ctx))))

(defn- goal-cost-rank [pr kb goal context]
  (cost-rank (budget/checked-call
              (fn [] (cost pr kb goal context)))))

(defn- dispatch-provers
  "The prover dispatch itself, with `run` saying what one prover's answers look like:
  raw bindings for `solve-goal-with`, `[bindings support]` pairs for
  `solve-goal-with-support`.

  One function rather than two copies, for `applicable-provers`' reason — the two must
  agree about *which* prover answers a goal, and a copied dispatch is two things to keep
  agreeing.  What differs between the callers is only the structure of an answer, which is
  exactly what `run` carries."
  [kb provers goal context run]
  (let [run        (fn [prover]
                     (budget/check-unit!)
                     (let [answers (budget/checked-call #(run prover))]
                       (budget/checked-seq answers)))
        applicable (applicable-provers kb provers goal context)
        complete   (sole-prover kb applicable goal context)]
    (if complete
      (run complete)
      (->> applicable
           ;; `goal-cost-rank` calls each prover's `cost` — an index/taxonomy count for
           ;; some — so rank once per prover, not once per comparison of the dispatch sort
           (nm/sort-by-content-key #(goal-cost-rank % kb goal context) compare)
           (res/lazy-mapcat run)
           distinct))))

(defn solve-goal-with
  "Raw solution bindings for `goal` in `context` from an explicit prover list.

  Lazy: provers are ordered by `cost` tier and expanded one at a time, through
  `res/lazy-mapcat` (`mapcat` would realize a chunk and call every applicable `solve`), so an
  expensive prover is never invoked if the consumer stops early.  The complete-prover branch
  runs one prover.  When several complete provers apply, the one with the fewest
  `est-bindings` runs."
  [kb provers goal context]
  (dispatch-provers kb provers goal context #(solve % kb goal context)))

(defn solve-goal
  "Raw solution bindings for `goal` in `context` via the applicable provers."
  [kb goal context]
  (solve-goal-with kb (registry kb) goal context))

(defn- answers-with-support
  "One prover's answers as `[bindings support]` pairs: its own support when it implements
  `SupportingProver`, and an **empty** support otherwise.

  Empty is the complete support for a prover that reads nothing stored: `EvaluableProver`
  compares two numbers, `EvaluateProver` computes one.  A prover that reads stored facts
  without implementing `SupportingProver` (`FactProver`, `SymmetricProver`,
  `InverseProver`) gets an empty support too, which names none of the facts it read;
  `solve-goal-reporting-support` marks which answers a `SupportingProver` gave."
  [pr kb goal context]
  (if (cap/has? SupportingProver pr)
    (solve-with-support pr kb goal context)
    (map (fn [b] [b #{}]) (solve pr kb goal context))))

(defn solve-goal-with-support
  "`solve-goal`'s support-carrying twin: each solution as `[bindings support]`, where `support`
  is the handles of the stored sentexes the answer was read from (`SupportingProver`), empty
  for any other prover (`answers-with-support`).

  Forward chaining is the caller: a firing stores a conclusion that must be withdrawable, and
  the handles must come with the bindings in one read.  The dispatch is `solve-goal`'s: the
  sole complete prover, else the applicable provers cheapest-first, lazily.  Deduped on the
  pair, so one binding reached with different support survives as two justifications."
  [kb goal context]
  (dispatch-provers kb (registry kb) goal context #(answers-with-support % kb goal context)))

(defn solve-goal-reporting-support
  "`solve-goal-with-support`'s answers as `[bindings support reported?]`, `reported?` true
  when a `SupportingProver` gave the answer.  An empty support it reports means the answer
  read nothing stored; an empty support from any other prover says nothing about what it
  read, `FactProver`'s among them."
  [kb goal context]
  (dispatch-provers kb (registry kb) goal context
                    (fn [pr] (let [r (cap/has? SupportingProver pr)]
                               (map (fn [[b sup]] [b sup r])
                                    (answers-with-support pr kb goal context))))))

(def ^:private ^:dynamic *mirror-depth*
  "How many mirror delegations are on the stack.  `solve-mirrored` re-enters the
  registry, and the mirror of a mirror is the original goal — so unbounded delegation
  is a loop, and a mutual `symmetric` + `inverse` pair could ping between the two
  delegates the same way.  Two levels admit every one-mirror-plus-one-partner
  composition; past the bound the mirror falls back to the raw stored read, which is
  the whole of what it answered before it delegated at all."
  0)

(defn- fan-mirrors-every-predicate?
  "Does the fact read of a `pred` literal at `context` probe both argument orders of every
  predicate it reads: is each predicate of its fan (`res/sub-predicates` and
  `res/swapped-sub-predicates`) symmetric at `context`?  The fan mirrors a candidate by
  that candidate's own mark, and `res/without-unbelieved-spellings` keeps the mirrored row
  at a reader believing that mark (`has-prop?` reads the same supporters)."
  [kb pred context]
  (let [tx (reasoning/taxonomy kb)]
    (every? #(tax/has-prop? tx :symmetric % context)
            (concat (res/sub-predicates kb pred context)
                    (res/swapped-sub-predicates kb pred context)))))

(defn- solve-mirrored
  "Solutions for the mirrored spelling of the symmetric `(pred a b)` — `(pred b a)`
  through the engine minus this prover, so the mirror composes with facts, the
  closures, preservation and the partner spellings rather than reading storage alone.
  The mirror of an *inherited* claim is the case that needs it: nothing is stored, and
  a raw read answers nothing for a claim `verdict` proves.

  The fact prover is left out too when `fan-mirrors-every-predicate?`, since the fact read
  of `(pred a b)` beside this prover already read both orders of every stored row."
  [kb pred a b context]
  (if (< *mirror-depth* 2)
    (binding [*mirror-depth* (inc *mirror-depth*)]
      (let [skip? (if (fan-mirrors-every-predicate? kb pred context)
                    #(or (instance? SymmetricProver %) (fact-prover? %))
                    #(instance? SymmetricProver %))
            pv    (remove skip? (registry kb))]
        ;; realized inside the binding: the depth guard is dynamic, and a lazy answer
        ;; escaping the scope would re-enter at depth zero — the loop this bounds
        (doall (solve-goal-with kb pv (list pred b a) context))))
    (map second (res/matches-visible kb (list pred b a) context))))

(defn- solve-inverted
  "Solutions for the inverted spelling of `(pred a b)`, the partner predicate with the
  arguments swapped, through the engine over a prover list minus `InverseProver`, so a mutual
  `(inverse P Q)` + `(inverse Q P)` cannot re-enter.  The delegation composes with the other
  metadata provers (transitive, symmetric, reflexive) and facts.

  Every declared partner of the predicate or a sub-predicate (`inverses-under`) is asked and the
  solutions are unioned and deduped, so the answer does not depend on declaration order.  A
  `(not (pred a b))` goal asks `(not (Q b a))` of each partner `inverted-partners` names."
  [kb goal context]
  (let [neg? (sx/negation? goal)
        [_ a b] (if neg? (second goal) goal)
        pv (remove #(instance? InverseProver %) (registry kb))]
    (->> (inverted-partners kb goal context)
         (sort)                                  ; content-keyed, so the order is stable
         (res/lazy-mapcat #(solve-goal-with kb pv (cond->> (list % b a) neg? (list 'not)) context))
         distinct)))

(defn est-goal
  "How many bindings the registry expects to produce for `goal`, or **nil** when it has no
  authoritative answer.

  Only a complete prover's estimate is returned, mirroring `solve-goal-with`, which runs it
  alone.  With none, the engine unions partial provers over the index, whose model
  `vaelii.impl.plan` uses instead (`ArgTypeProver`'s constant 3 would replace a measurement).
  The one partial estimate is `deferred-est`, from an applicable `SupportingProver` that
  computes the goal from an open argument, `(argN ?t 1 ?f)` before `?f` is bound, so the goal
  waits for its binders."
  [kb goal context]
  (let [applicable (applicable-provers kb (registry kb) goal context)]
    (if-let [complete (sole-prover kb applicable goal context)]
      (est-bindings complete kb goal context)
      (let [supporting (:provers (support-summary kb))]
        (when (some #(and (some (partial identical? %) supporting)
                          (= deferred-est (budget/checked-call
                                           (fn [] (est-bindings % kb goal context)))))
                    applicable)
          deferred-est)))))

(defn registry-est-override
  "`est-goal` as the `:est-override` a backward chainer plans with (`res/prove-from`,
  `res/initial-prove-stack`), for an executor whose leaf is the registry and only such an
  executor.  The index model is wrong for that leaf: a `genl` conjunct costs the cached
  closure's size and not the stored edges the trie counts.  A chainer whose leaf is the stored
  facts passes nothing.

  Memoized on the goal (`est-goal` reads only the goal; a query mutates nothing), or on the goal
  and its bound variables for a goal at `deferred-est` (`est-under`).  Without the memo
  `plan/order` re-estimates every remaining literal on every pick, O(k²) registry sweeps for k
  antecedents."
  [kb context]
  (let [est   (memoize (fn [goal] (est-goal kb goal context)))
        under (memoize (fn [goal bound]
                         (est-under deferred-est (applicable-provers kb (registry kb) goal context)
                                    kb goal context bound)))]
    (fn [goal bound]
      (let [e (est goal)]
        (if (= deferred-est e)
          (under goal (into #{} (filter (set bound)) (sx/form-variables goal)))
          e)))))

;; ---- exceptWhen: evaluating a rule's exception ---------------------------
;; This lives here, rather than beside the forward chainer that first needed it,
;; because *three* consumers must agree on it: forward chaining, the recursive chainer
;; (`vaelii.impl.resolution`) and the node engine (`vaelii.impl.inference`).  An
;; exception that blocked a rule forward but not backward would make two of them
;; disagree about the same rule, which is the one thing an exception must never do.
;;
;; It runs over the registry, which expands no rule — level 6 of the lookup stack
;; (`vaelii.impl.levels`), expressed here so nothing has to depend on that namespace
;; to run the check.

(defn condition-normalizer
  "A `ground-goal -> ground-goal` rewriting a block condition's substituted conjunct to the
  normal form `context` answers under (every symbol to the representative that context
  elects, then the schematic equations it can see), or nil when the KB holds no merge and no
  equation.  `vaelii.impl.levels/engine-goal` and `kb/rewrite-goal` prepare a level-6 read and
  a query the same way.

  Both the bindings a firing substituted in and the conjunct's own constants may name a
  spelling a later merge retired, and an unrewritten goal then reads as *not excepted* and
  *not derivable*.  The rewrite is scoped to `context`: a merge it cannot see must not rename
  the condition.  One visibility predicate serves the whole conjunction.  A goal
  `res/goal-held-as-spelled?` exempts (`different`, a positive equation) is exempt here as in
  `kb/rewrite-goal`."
  [kb context]
  (let [tx (reasoning/taxonomy kb)]
    (when-not (and (nil? (tax/merged-term-pred tx)) (empty? (tax/rewrite-rules tx)))
      (let [visible? (res/visible-supporter-fn kb context)
            rules    (res/rewrite-rules-in kb visible?)]
        (fn [goal]
          (if (res/goal-held-as-spelled? goal)
            goal
            (rewrite/normalize-sentence rules (res/representative-term kb visible? goal))))))))

(defn exception-holds?
  "Does `except` — a rule's `exceptWhen` query, a vector of literals — hold under
  `bindings`, evaluated in `context`?  The substituted conjuncts are put in `context`'s
  normal form (`condition-normalizer`) and joined by `conjunction-solutions`, stopping at
  the first solution; nothing in the registry expands a rule.  An unanswerable or empty
  exception does not hold.  See docs/exceptions.md, \"The exception is a query, not a
  literal\"."
  [kb except bindings context]
  (as-guard #(conjunction-derivable? kb except bindings context (condition-normalizer kb context))))

(defn exception-visible-from?
  "Does `context` see the exception `entry` (a `rule-exception-entries` element)?

  An `exceptWhen` is a sentex, so a context reasons with the exceptions its `genlCx`
  ancestor set holds and no others, exactly as it reasons with the rules
  (`res/rule-visible-from?`).  An exception stated in a context below the conclusion's
  therefore blocks nothing in the conclusion's context.  An open `?ctx` or nil
  `context` is the unscoped path and sees every exception."
  [kb context entry]
  (res/rule-visible-from? kb context (:context entry)))

(defn stored-exception-metas
  "The exceptWhen meta-sentexes stored naming the rule at `handle`, believed or not:
  what `rule-exception-entries` reads before it filters by belief."
  [kb handle]
  (into []
        (comp (map #(p/get-sentex (:records kb) %))
              (filter some?)
              (filter #(sx/exceptWhen-meta? (:sentence %)))
              (filter #(= handle (sx/exceptWhen-rule-handle (:sentence %)))))
        (reads/as-stored-naming-handle (:index kb) handle)))

(defn rule-exception-entries
  "The believed exceptWhen exceptions of the rule at `handle`, each as
  `{:context c :handle h :query q}`: `q` is one conjunction (a vector of literals) in the
  rule's canonical variables, and `c` and `h` are its meta-sentex's context and handle.
  The callers read it only for a rule in the watched-rule set."
  [kb handle]
  (into []
        (comp (filter #(jtms/in? (reasoning/tms kb) (:id %)))
              (map (fn [msx] {:context (:context msx)
                              :handle  (:id msx)
                              :query   (sx/exception-query-conjuncts (:sentence msx))})))
        (stored-exception-metas kb handle)))

(defn firing-strength
  "The class a firing of the rule `rsx` at `handle` confers on its conclusion, before its
  antecedents cap it: `:default` for a `set/defaultRule`, and for a **guarded** rule, one
  with an `(unknown S)` antecedent or an `exceptWhen` stored against it; `:monotonic`
  otherwise.  A guarded conclusion goes OUT when a blocker arrives, so it is never
  `:monotonic` (docs/nmtms.md, \"Strength propagates from the antecedents\").

  The exceptions are read as stored, belief unread, so the class is a function of the
  stored content.  `watched?` is `reads/watched-rule?`'s answer for `handle`, which the
  chainer has already read for the rule fields (`chain/rule-fields-of`); `dropping-id` is an exception meta-sentex
  on its way out, which the read leaves out."
  [kb handle rsx watched? dropping-id]
  (if (or (:defeasible rsx)
          (rules/has-naf? rsx)
          (and watched?
               (some (fn [mh]
                       (and (not= dropping-id mh)
                            (when-let [m (p/get-sentex (:records kb) mh)]
                              (and (sx/exceptWhen-meta? (:sentence m))
                                   (= handle (sx/exceptWhen-rule-handle (:sentence m)))))))
                     (reads/as-stored-naming-handle (:index kb) handle))))
    :default
    :monotonic))

(defn rule-exceptions
  "The conjunctions of `rule-exception-entries`, evaluated block-if-**any**-holds.

  The two-argument arity reads every believed exception wherever it is stored, which
  is the set a structural reader wants: the re-check index, the stratification graph
  and the candidate narrowing all over-approximate safely.  The three-argument arity
  keeps only the exceptions `context` sees (`exception-visible-from?`), which is the
  set a block decision in `context` reads."
  ([kb handle]
   (mapv :query (rule-exception-entries kb handle)))
  ([kb handle context]
   (into []
         (comp (filter #(exception-visible-from? kb context %))
               (map :query))
         (rule-exception-entries kb handle))))

(defn negated-recheck-bodies
  "The symbol-headed bodies of the negated literals rule `rh` re-checks: in its `unknown`
  antecedents, its aggregate bodies and the queries of its believed exceptWhen
  meta-sentexes."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (into []
          (keep (fn [l] (when (and (seq? l) (= 'not (first l)))
                          (let [b (second l)]
                            (when (and (seq? b) (symbol? (first b))) b)))))
          (concat (when (rules/rule? rsx)
                    (concat (rules/naf-queries rsx)
                            (mapcat rules/watched-literals (rules/aggregate-queries rsx))))
                  (mapcat rules/watched-literals (mapcat identity (rule-exceptions kb rh)))))))

(defn closed-extent-rules
  "The handles of the stored rules a closed-extent grant on `pred` makes read a
  `(not (pred …))` as negation as failure, deduplicated: each with a closed
  `(not (pred …))` antecedent (one `[:not pred]` antecedent-index lookup), and each
  watched under `not` that re-checks a `(not (pred …))` in an `unknown` antecedent, an
  aggregate body or an `exceptWhen` query (`negated-recheck-bodies`).  Read as stored,
  whether a grant on `pred` stands or not."
  [kb pred]
  (let [idx    (:index kb)
        top    (filter #(when-let [rsx (p/get-sentex (:records kb) %)]
                          (and (rules/rule? rsx)
                               (seq (rules/closed-negative-antecedents (:antecedent rsx)))))
                       (reads/as-stored-rules-by-antecedent-global idx [:not pred]))
        nested (filter #(some (fn [b] (= pred (first b))) (negated-recheck-bodies kb %))
                       (reads/watched-rules-on idx 'not))]
    (distinct (concat top nested))))

(defn closed-extent-supports
  "The handles each of which alone answers the ground `(not (P …))` literal `l` at level 6
  where it is visible, in any context and in the reading in force: each grant a
  `ClosedExtentProver` answer rests on, `(closed_extent_predicate P)` or a
  `(closedExtentForArg P n v)` whose argument `n` of `(P …)` is `v`, and each stored `l`.
  Nil when no grant covers `l`, and nil when a prover other than `ClosedExtentProver`
  and `FactProver` answers `l` in some context, since that answer names no handle."
  [kb l]
  (let [b (second l)
        p (nm/functor b)]
    (when-not (seq (take 1 (solve-goal-with kb (remove #(or (instance? ClosedExtentProver %)
                                                            (instance? FactProver %))
                                                       (registry kb))
                                            l '?ctx)))
      (when-let [gs (seq (concat (res/matches-visible kb (list 'closed_extent_predicate p) '?ctx)
                                 (filter (fn [[_ bd]] (arg-grant-covers? b bd))
                                         (res/matches-visible kb (list 'closedExtentForArg p '?n '?v) '?ctx))))]
        (into [] (comp (map first) (distinct)) (concat gs (res/matches-visible kb l '?ctx)))))))

(defn exceptions-block?
  "Is a firing of rule `handle` blocked by any of its exceptWhen exceptions under
  `bindings`, evaluated in `context`?  Block-if-**any**-conjunction-holds, over the
  exceptions `context` sees.  An ordinary rule (no exception) yields no conjunctions
  and pays nothing past the watched-rule membership read."
  [kb handle bindings context]
  (boolean (some #(exception-holds? kb % bindings context)
                 (rule-exceptions kb handle context))))

(defn rule-guard
  "The firing guard for a rule handle, or nil when the rule carries no exception.

  A guard is a predicate on a firing's completed bindings that is **true when the
  firing is permitted** — false exactly when one of the rule's exceptions holds.
  Attaching it to the parsed rule map is what lets the backward chainers construct the
  argument and then discard it, which is the same decision forward chaining makes
  before placing a conclusion.

  Backward there is no placement context, so the exception is evaluated in the
  **query's** context — the nearest analogue to \"where the conclusion would live\", and
  the context the caller is asking from."
  [kb rule-sentex context]
  (let [h (:id rule-sentex)]
    (when (and h (reads/watched-rule? (:index kb) h) (seq (rule-exceptions kb h context)))
      (fn [bindings] (not (exceptions-block? kb h bindings context))))))

(defn parse-rule
  "A rule sentex as the chainers' parsed map — antecedents, consequent, the `exceptWhen`
  guard if it has one, and the rule's own `:handle`, which is what an executor
  accumulating supports records (`vaelii.impl.inference`)."
  [kb rule-sentex context]
  {:antecedents (:antecedent rule-sentex)
   :consequent  (:consequent rule-sentex)
   :guard       (rule-guard kb rule-sentex context)
   :handle      (:id rule-sentex)})

(defn- goal-vars [goal] (sx/form-variables goal))

(defn- project
  "Project raw solution bindings onto `goal`'s variables and dedup — the shape `ask`
  returns.  Lazy, so a bounded caller (`ask-within`) still pays per result."
  [goal sols]
  (let [gvars (goal-vars goal)]
    (distinct (map (fn [b] (select-keys (res/resolve-bindings b) gvars)) sols))))

(defn ask
  "Answer `goal` in `context`; solution binding maps projected to the goal's
  variables (a ground goal yields [{}] when provable, [] otherwise)."
  [kb goal context]
  (project goal (solve-goal kb goal context)))

(defn cost-capped-provers
  "The registry minus provers whose `cost` tier exceeds `max-cost` (a tier keyword,
  see `cost-tiers`); a nil `max-cost` keeps them all.  This is `budget`'s `:max-cost`
  applied to the query engine — under time pressure, keep the cheap tiers and drop the
  closures.  `:lookup` is therefore the only ceiling that currently narrows anything:
  `:search` is unoccupied (`cost-tiers`), so it and `:compute` keep the whole registry.

  A `max-cost` that is not one of the three is **refused**, rather than read as no
  ceiling at all: a caller writing `:cheap` for `:lookup` is asking to exclude the
  expensive tier, and the one reading of a typo that is certainly wrong is to run it."
  [kb goal context max-cost]
  (if (nil? max-cost)
    (registry kb)
    (let [ceiling (or (cost-rank max-cost)
                      (throw (ex-info (str "no such cost tier: " (pr-str max-cost)
                                           " — want one of " (pr-str cost-tiers))
                                      {:type :unknown-option :mismatch :bad-value :max-cost max-cost
                                       :known cost-tiers})))]
      (filterv (fn [p]
                 (or (<= (goal-cost-rank p kb goal context) ceiling)
                     ;; `unknown` is closed-world: dropping its prover does not leave the
                     ;; query merely incomplete, it INVERTS the answer — an empty result
                     ;; for `(unknown S)` reads as "S is derivable" — and the engine would
                     ;; report that as `:complete`.  Kept past the cap: it is applicable
                     ;; only to `unknown` goals, so retaining it narrows nothing else, and
                     ;; a wrong answer outranks a best-effort cost bound.  `thereExists`
                     ;; and the aggregates under-report rather than invert, so they stay
                     ;; droppable.
                     (instance? UnknownProver p)))
               (registry kb)))))

(defn ask-capped
  "`ask`, but only provers at or below the `max-cost` tier participate (nil = all).
  A goal answerable only by a dropped tier yields nothing — the effect the
  qualitative bound asks for.  Lazy, for `vaelii.core/ask-within` to `budget/collect`."
  [kb goal context max-cost]
  (project goal (solve-goal-with kb (cost-capped-provers kb goal context max-cost) goal context)))

(defn plan
  "The applicable provers for a goal, their estimates, and which of them actually run.

  When one prover may answer the goal alone, every other applicable prover is shadowed:
  reported, never invoked.  Each entry carries `:runs?`, and a shadowed one carries
  `:shadowed-by` naming the prover that displaced it.  A prover that claims `completeness` 100
  but does not run alone, because a source none of the applicable provers reads bears on the
  goal, carries `:guarded-by` naming the channels (`shadowing-channels`).  Entries are in the
  order the engine would consult them: a single complete prover, else cheapest `cost` tier
  first."
  [kb goal context]
  ;; Each estimate is asked once and carried, and the channels once for the goal — a
  ;; plan that re-asked them per decision would cost several times what it reports on.
  (let [entries  (into [] (map (fn [pr]
                                 {:prover       (-> pr class .getSimpleName)
                                  :est-bindings (est-bindings pr kb goal context)
                                  :cost         (cost pr kb goal context)
                                  :completeness (completeness pr kb goal context)}))
                       (applicable-provers kb (registry kb) goal context))
        channels (shadowing-channels kb goal context)
        winner   (when (empty? channels)
                   (->> entries
                        (filter #(>= (:completeness %) 100))
                        (sort-by :est-bindings)
                        first))]
    (if winner
      (cons (assoc winner :runs? true)
            (for [e entries :when (not (identical? e winner))]
              (assoc e :runs? false :shadowed-by (:prover winner))))
      (for [e (sort-by #(cost-rank (:cost %)) entries)]
        (cond-> (assoc e :runs? true)
          (and (seq channels) (>= (:completeness e) 100))
          (assoc :guarded-by channels))))))

;; ---- what this namespace holds ------------------------------------------

(defn- trim-closures
  "Drop cached reaches from `kb`'s closure cache until the members held are at most `target`,
  keeping the entries iteration reaches first and recomputing the member count, and answer how
  many members went.  The cache is bounded by members rather than entries — an entry is a
  whole reach set — so the guard's target is a member count, and the trim keeps whole reaches
  up to it rather than dropping the map wholesale the way `:clear` does."
  [kb ^long target]
  (if-let [a (reasoning/closures kb)]
    (let [before (long (:members @a 0))]
      (when (> before target)
        (swap! a (fn [c]
                   (loop [es (seq (:entries c)) kept (transient {}) m 0]
                     (let [e (first es)]
                       (if (and e (<= (+ m (count (val e))) target))
                         (recur (next es) (assoc! kept (key e) (val e)) (+ m (count (val e))))
                         (assoc c :members m :entries (persistent! kept))))))))
      (max 0 (- before (long (:members @a 0)))))
    0))

(caches/register-cache
 {:cache    :closure-answers
  :label    "Closure answers"
  :scope    :kb
  :unit     "members"
  :limit    (caches/limit-thunk :closure-answers #'*closure-answer-limit*)
  :counters :kb
  :note     (str "One declared-transitive predicate's reach from one node, in one "
                 "direction, seen from one context — the answer an open-argument ask "
                 "computes. The whole map carries one change clock, so any mutation "
                 "(a relabel included, which is what makes it follow belief) retires "
                 "every entry at once. Bounded by total MEMBERS rather than entries, "
                 "since an entry is a whole reach set: a reach larger than the bound is "
                 "never stored, and a total that reaches it drops the map wholesale.")
  :read     (fn [kb] {:entries (or (some-> (reasoning/closures kb) deref :members) 0)})
  :clear    (fn [kb] (let [a (reasoning/closures kb)
                           n (if a (:members @a 0) 0)]
                       (some-> a (reset! {}))
                       n))
  :trim     (fn [kb target] (trim-closures kb target))})

(caches/register-derived
 {:id :R2 :label "Closure answers" :cache :closure-answers :kind :cache :keyed-by :node
  :holds-content? false
  :reads [:index :M1]
  :retired-by (assoc (caches/on-every :G*) :caches-cleared :W)
  :computed :read :imaged? false :at [[:closures]]
  :live (fn [kb] (let [c (some-> (reasoning/closures kb) deref)]
                   (if (== (observe/change-clock) (long (:clock c -1))) (count (:entries c)) 0)))
  :note "one clock for the whole map: a write retires every entry"})

(caches/register-derived
 {:id :K10 :label "Prover registry summary" :kind :cache :keyed-by :value :reads []
  :holds-content? false
  :retired-by (caches/on-every :I) :computed :read :imaged? false :var #'registry-support
  :value (fn [_] @registry-support)
  :note "one slot, compared by identity against the prover registry vector of the KB read; a read of a KB holding another vector replaces it"})
