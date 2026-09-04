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
  complete via the cached closures), disjointness (complete), `different` (the
  unique-name assumption read off the equality closure — ground only, see
  docs/equality.md), facts (the index), and rules (backward chaining through the same
  engine).

  ## What completeness 100 claims

  **For this goal shape, my answers are a superset of what every other prover reading
  the same sources would answer.**  That is the reading that licenses running alone,
  and it is a claim a prover is competent to make about itself.

  The tempting alternative — *nothing else can answer this goal* — is a claim about a
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
  included — before entailing anything."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.datetime :as datetime]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.violations :as violations]))

(defprotocol Prover
  (applicable?  [prover kb goal context])
  (est-bindings [prover kb goal context])
  (cost         [prover kb goal context])
  (completeness [prover kb goal context])
  (solve        [prover kb goal context]))

(defprotocol SupportingProver
  "A prover whose answer is a function of **stored facts** rather than of the goal's own
  arguments alone, and which can say which facts — the unit table a measure comparison
  normalizes through, the constraints a metric bound is closed out of, the lengths a
  duration sums.

  A separate protocol rather than a sixth `Prover` method, because implementing it is a
  choice: `EvaluableProver` computes `(lessThan 3 5)` from the numbers in front of it and
  has no support to report, while `QuantityProver` reads a `conversionFactor` row before
  it can compare two masses.  Only the second is here.

  **Forward chaining is what needs it.**  A rule antecedent discharged by a prover
  contributes no matched fact, so a firing that rested on one lists the rule and whatever
  the *other* antecedents matched — and a `conversionFactor` row behind the answer is
  supported by nothing the JTMS can reach.  Retracting it then leaves the conclusion
  believed.  `solve-with-support` closes that: each answer carries the handles it was read
  from, the join adds them to the firing's antecedents, and the ordinary relabel withdraws
  the conclusion when any of them goes.  It is the same contract
  `qcn-kb/solve-with-support` and `inherit/solve-with-support` already meet for a
  qualitative and an inherited antecedent.

    support-functors     the functors this prover answers with support, as a set
    support-sources      the functors it *reads* to answer them, as a set
    solve-with-support   the solutions of `Prover/solve`, each as `[bindings support]`

  `support-sources` is what keeps the firing order-independent.  A rule whose antecedent
  this prover answers is triggered by the facts its *other* antecedents match, and a
  `conversionFactor` row is not one of them — so a unit table stated after the rule and
  the facts would never reach a join, and the same three sentences would derive a
  conclusion or not depending on which arrived last.  Naming the sources puts such a datum
  in front of the rules carrying a `support-functors` antecedent, re-joined in full
  (`chain/rejoin-in-full`), exactly as a `(symmetric P)` declaration is.

  Two obligations on an implementer, and both are what makes the seam sound:

  * **`solve-with-support` answers exactly what `solve` answers.**  The bindings are the
    same solutions in the same order; only the support rides alongside.  A prover whose
    two methods disagreed would make a rule fire differently forward and backward.
  * **The support is enough to have produced the answer on its own.**  It may
    over-approximate — a reading taken over a set of declarations names all of them — but
    it may never omit a fact the answer moved with, since that is the fact whose
    retraction would leave a stale conclusion standing.

  An answer with **empty** support is one nothing stored licensed — the diagonal of a
  metric network, an arithmetic identity — and the forward join drops it rather than
  building a justification that names the rule alone while looking as though it named the
  facts (`qcn-kb/solve-with-support` gives the qualitative version of the same case)."
  (support-functors   [prover])
  (support-sources    [prover])
  (solve-with-support [prover kb goal context]))

(def cost-tiers
  "First-answer cost tiers, cheapest first — one question: is the answer something
  you **look up**, **compute**, or **search for**?  Qualitative, not milliseconds:
  they name the *shape* of the work.  A per-prover millisecond estimate would be a
  constant standing in for a number no implementation can compute, and a real
  wall-clock budget cannot be gated against that.

    :lookup   a bounded single-step retrieval — an O(1) ground test, a cached
              closure / metadata read, or one index hit (lazy to the first result)
    :compute  a fixpoint over stored facts before the first answer (a closure)
    :search   recursive backward chaining — open-ended proof search

  `cost-rank` turns a tier into its ordinal.  The union path orders applicable
  provers by this rank (cheapest first, so a consumer taking one answer never pays
  for a search when a lookup answers); `budget`'s `:max-cost` uses it as a ceiling —
  `:lookup` runs bounded retrieval only, `:compute` allows a closure but no search.

  **`:search` is unoccupied**, and by construction: no member of the registry expands a
  rule, so nothing here opens a proof search and `:max-cost :compute` and `:max-cost
  :search` currently select the same provers.  The tier stays because the ceiling is a
  claim about *what a prover may cost*, not a census of the shipped ones — an application
  prover that backchains belongs in it, and `add-prover` can supply one.  Rule expansion
  itself is priced by the engine that does it (`core/query`'s `:max-depth`), which is a
  bound rather than a tier."
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
(defn- has-var? [form] (boolean (some pvar? (tree-seq sequential? seq form))))
(defn- ground? [form] (not (has-var? form)))
(defn- binary? [goal] (and (sequential? goal) (= 2 (count (rest goal)))))
(defn- binary-pred? [goal p] (and (binary? goal) (= p (first goal))))

;; ---- what can shadow a computed answer ----------------------------------

(defn shadowing-channels
  "The ways this KB could reach `goal` that a **computed** prover does not read — the
  set a conditionally-complete prover checks before claiming its answers are a
  superset of everyone else's (see the completeness contract at the head of this file).

  Four channels, each found by differencing: run the complete prover alone, run every
  other applicable prover, and see what only the second answers.

  * **`:preserving`** — an `(transitiveInArg P n R)` declaration licenses a claim about a
    tuple that appears in no stored fact, in no rule conclusion and in no constraint
    network, so nothing computed from those three can contain it.
  * **`:rules`** — a rule concluding the goal's predicate, or a spec of it.  A *forward*
    rule's conclusion is stored when it fires and so is absorbed, but a
    `set/backwardRule` never fires forward: its conclusion exists only while a
    backchainer is looking for it, and no member of the registry is one.  So a complete
    prover here is claiming a superset of what the *registry* answers, while the rule is
    reached by an executor above it — and the claim has to be read in that scope or it
    over-reaches: it would let a computed answer stand in for a leaf the node engine or
    `prove` is about to expand a rule under.  Not narrowed to backward-only rules: a
    forward rule is absorbed only if the fixpoint actually ran to it, which
    `{:chain? false}` and `:max-depth` can both prevent, and being wrong here costs a
    union rather than an answer.
  * **`:inverse`** — a declared `(inverse P Q)` where the goal is about `P`.  A
    calculus applies its algebra's own converse *within its vocabulary*, and the
    taxonomy closures are keyed on their own functor, so neither reads a partner
    predicate stored under a different name.  Measured the same way, on `genl` and on
    `partOfRegion`.
  * **`:calendar`** — an argument that is a **calendar term**: `(YearFn 2000)`,
    `(MonthFn 2000 1)`, a `DatetimeFn` string, an `InstantFn` moment.  Such a term carries
    its own ordering *in its fields*, and a term that appears in no stored fact appears in
    no closure and in no constraint network either — so a calculus reading the store
    entails nothing about the pair while correctly claiming to subsume every prover that
    reads what it reads.  The structure is the source it does not read
    (`vaelii.impl.calendar`).  A pure test on the goal's own arguments, and the cheapest
    of the four: no index read, and no read at all for a goal naming no such term.

  What is **absorbed**, and it is worth being exact since a missing entry here is a
  missing answer:

  * a **stored fact** is what the closures are built out of and what a calculus reads
    into its network;
  * a **merged term** is rewritten into the goal before any prover sees it, so an
    equality reaches a computed prover already applied;
  * `symmetric` / `transitive` / `reflexive` over a predicate a calculus owns are the
    algebra's own composition and converse;
  * `arg` type inference and the metadata provers answer goal shapes no computed
    prover claims, so they are never shadowed in the first place.

  Cheap by construction on three of the four: `inherit/positions` is behind a
  root-intersection gate on any declaration naming this predicate,
  `tax/inverses-under` is one map read on a KB declaring no inverses, and
  `datetime/time-term?` reads the goal's own arguments.
  `concluding-rule-handles` is the one that is not — it probes the consequent index once
  per member of `pred`'s spec closure, so this is O(specs) index reads per goal however
  few rules conclude anything, and `cond->` evaluates every test rather than stopping at
  the first channel found.  Its own docstring carries the number."
  [kb goal context]
  (when (sequential? goal)
    (let [pred (nm/functor goal)]
      (cond-> #{}
        (seq (inherit/positions kb pred context))            (conj :preserving)
        (seq (res/concluding-rule-handles kb pred context)) (conj :rules)
        (seq (tax/inverses-under (:taxonomy kb) pred context)) (conj :inverse)
        (some datetime/time-term? (nm/args goal))             (conj :calendar)))))

(defn sole-prover
  "The prover that may answer `goal` **alone**, or nil for the union path.

  Two conditions, and they are asked of different parties.  A prover claims
  `completeness` 100 — *for this goal shape, my answers subsume every prover whose
  sources I read* — which is a claim it is competent to make about itself.  The engine
  then asks the question no single prover can: **is there a source none of them reads**
  (`shadowing-channels`)?  If so, nobody runs alone, whatever they claimed.

  Putting the guard here rather than in each prover is what makes it hold.  A fourth
  channel is one edit instead of one per claimant; a prover registered through
  `add-prover` is guarded without its author knowing the mechanism exists; and no
  prover has to reason about sources outside its own.

  Guarding is **safe in one direction only, and it is the safe one**: it can move a
  goal from one prover to the union, never the reverse, and the union path includes the
  claimant — so a guard that fires unnecessarily costs a lazy prover that may never be
  forced, while one that fails to fire loses an answer.  That asymmetry is why the
  channels are asked of every claimant alike, including the ones whose goal shape is
  unstorable (`different`, `unknown`, `thereExists`, `forall`, an aggregate): they need
  no exemption, because for them no channel ever bears.

  The channels are read **once per goal** — they are a property of the goal and the KB,
  not of the prover asking.  So is each claimant's estimate: `sort-by` re-evaluates its
  keyfn on **every comparison**, and an estimate is a real count over the taxonomy
  rather than a constant, so it is taken once per prover and carried.  The sort is
  stable and the estimate is a function of the goal and the KB, so a tie still breaks
  on registry order and not on when the comparison happened."
  [kb applicable goal context]
  (when (empty? (shadowing-channels kb goal context))
    (->> applicable
         (filter #(>= (completeness % kb goal context) 100))
         (map (juxt identity #(est-bindings % kb goal context)))
         (sort-by second)
         ffirst)))

;; ---- facts (the index) --------------------------------------------------

(defn- est-by-functor
  "Estimated bindings for a goal: how many stored facts share its functor.  Read from
  the functor root, which counts either polarity and any arity — the trie's
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
  out of the generic per-predicate transitive machinery.  Defined once in the taxonomy."
  tax/closure-relations)

(defn- trans-fns [kb pred context]
  (let [tx (:taxonomy kb)]
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

;; An open disjointness goal is answered from the **declarations**, not from the
;; vocabulary.  A `(disjoint x y)` declaration separates two subtrees, so the pairs it
;; convicts are `specs(x) × specs(y)` and every answer is a subtype of something a
;; declaration names (`tax/separating-partners`, `tax/separating-pairs`).  The answer set
;; is therefore what `tax/disjoint?` says it is — that predicate is unchanged and still
;; decides the ground goal — while what is *fed* to it is bounded by the declaration set
;; rather than by the type count.  An imported ontology carries 132,391 types over 27,195
;; declared pairs (docs/kbs.md, docs/taxonomy.md), and a term's own share of the second
;; number is one or two.
;;
;; `distinct` because two declarations can convict one type and the vocabulary scan this
;; replaces could not repeat an answer.

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
    (let [[_ a b] goal, tx (:taxonomy kb)
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
    (let [[_ a b] goal tx (:taxonomy kb)]
      (cond
        (and (ground? a) (ground? b)) (if (tax/disjoint? tx a b context) [{}] [])
        (ground? a) (map (fn [t] {b t}) (disjoint-with tx a context))
        (ground? b) (map (fn [t] {a t}) (disjoint-with tx b context))
        ;; `(disjoint ?x ?x)` — one variable in both places, so one binding; the same
        ;; `Duplicate key` the transitivity prover above states its way past
        (= a b) (map (fn [x] {a x}) (self-disjoint tx context))
        :else (map (fn [[x y]] {a x b y}) (disjoint-cross tx context))))))

;; ---- generic relation reasoners (predicate metadata) --------------------

(defn- hop-patterns
  "The one-hop lookup patterns for `node` under `pred`, each binding `?rv` to the
  neighbour.  `dir` is `:succ` (node in argument 1) or `:pred` (node in argument 2).

  **One probe per visible `(inverse P' Q)` with `P'` at-or-below `pred`, plus the direct
  one.**  `(P x y)` and `(Q y x)` are one edge recorded two ways, so a chain whose middle
  hop was written on a partner is on the graph the walk sees rather than a break in it —
  and a partner declared for a *sub-predicate* records a sub-predicate tuple, which is a
  `pred` tuple by subsumption, so its spelling is a hop here too (`inverses-under`).
  The partner set is empty for nearly every predicate, so the ordinary walk pays one map
  read per node — and where a KB declares two partners both are probed, since answering
  off one of them would put a hop's visibility at the mercy of which declaration landed
  last.

  The partner is probed with `matches-visible` on the swapped literal, **not** by
  delegating a goal to the registry.  That keeps the step relation a function of the KB
  alone — the property `vaelii.impl.literal-cache`'s docstring argues for at length — and
  it is why a mutual `(inverse P Q)` + `(inverse Q P)` pair cannot cycle here the way
  `solve-inverted` has to guard against.
  A `P` declared its own inverse yields the two probes of a symmetric predicate, which is
  what such a declaration says."
  [kb dir pred node context]
  (let [qs (sort (tax/inverses-under (:taxonomy kb) pred context))]
    (if (= dir :succ)
      (into [(list pred node '?rv)] (map #(list % '?rv node)) qs)
      (into [(list pred '?rv node)] (map #(list % node '?rv)) qs))))

(defn- closure-key
  "The key a walk's reach — and the neighbour sets it is built from — is held under.

  One function because there are **three** construction sites and they have to agree: the
  open ask that fills the cache, and the closed pair that reads it by membership from
  either end.  Written out three times, adding a component to one of them turns every hit
  into a miss and the only symptom is a slow test.

  `[dir pred node context]` covers what the step relation reads — `inverses-under` is a
  function of exactly `pred` and `context`.  The **belief mode** is the fifth, and it is
  not covered by the clock: a `CxEverything` read walks the same four with the belief
  filter off and moves nothing, so without it the two modes share one entry and whichever
  ran first answers for both — an ordinary read reporting a defeated default.  Same
  omission, and the same fix, as the literal cache's key.

  `memo-neighbours` is deliberately **not** one of the three.  Its memo is bound per search
  step (`observe/with-search-scope`) and so lives inside a single read, where the belief
  mode cannot change; a blind read and an ordinary one never share one.  Keying it here
  would put a `^:dynamic` deref in the walk's innermost loop — once per node — which is the
  cost `res/belief-blind?` exists to keep out of exactly that loop."
  [dir pred node context]
  [dir pred node context (res/belief-blind?)])

(defn- memo-neighbours
  "The neighbours of `node` under `pred` as `{neighbour #{handle}}` — the terms one hop
  away, each with the handles of the stored sentexes that record the hop — cached in
  `observe/*reach-memo*` when one is bound.  `dir` is `:succ` (node in argument 1) or
  `:pred` (node in argument 2).

  The key stays `[dir pred node context]` and covers everything the step relation reads:
  `inverses-under` is a function of exactly `pred` and `context`, both already in it — and
  the belief mode is constant for this memo's whole life, which `closure-key` says why.  The
  neighbours are keyed by **term**, so an edge recorded in both spellings — or reached
  through both probes of a self-inverse predicate — is one member, and the spellings
  gather in that member's handle set rather than making two.

  **The handles are why this is a map and not a set.**  A closure answer supports a
  forward firing (`SupportingProver`, below), and what it rests on is the edges it crossed
  — which live nowhere but here, one hop at a time.  Every spelling of a hop is kept
  rather than one chosen, because choosing would key the firing's justification on which
  spelling arrived first; the seam permits exactly this over-approximation and forbids the
  omission.

  Read with `matches-visible`'s `cached?` false, which is the whole of the walk's
  relationship with the solution cache: a walk asks each node's literal once, so that
  cache has no repeat here to serve, and one insertion per node would clear it wholesale
  under a reader that does re-ask.  Why the argument and not the toggle is
  `res/matches-visible`'s own."
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
  (let [qs   (sort (tax/inverses-under (:taxonomy kb) pred context))
        ends (fn [pat k] (keep #(get (second %) k) (res/matches-visible kb pat context)))]
    (distinct (apply concat
                     (ends (list pred '?lv '?rv) '?lv)
                     (map #(ends (list % '?lv '?rv) '?rv) qs)))))

(defn- reach [seed step]
  (loop [result #{}, frontier (vec seed)]
    (if (empty? frontier)
      result
      (let [x (peek frontier) frontier (pop frontier)]
        (if (result x)
          (recur result frontier)
          (recur (conj result x) (into frontier (step x))))))))

(defn- on-a-cycle
  "The nodes reachable from themselves under `step`, starting from `sources` — the answer
  to `(P ?x ?x)` for a declared-transitive `P`.

  **One pass over the graph, not one closure per source.**  Asking `reaches?` per source
  walks that source's whole reach to fail, so an acyclic chain of *n* nodes costs O(n²) to
  answer nothing — the shape a temporal or part-of chain actually has, and the shape this
  arm is most often asked about.  A node lies on a cycle exactly when its strongly
  connected component has more than one member, or when it has a self-edge, so Tarjan
  answers every source at once in O(V+E).

  Iterative rather than recursive: a component's depth is a chain's length, and a 100k-node
  `before` chain would take the JVM stack down.  The stack frames are `[node
  successors-still-to-visit]`, which is the recursion made explicit."
  [sources step]
  (let [index   (java.util.HashMap.)          ; node -> discovery index
        low     (java.util.HashMap.)          ; node -> lowlink
        on      (java.util.HashSet.)          ; nodes on the tarjan stack
        stack   (java.util.ArrayDeque.)       ; the tarjan stack itself
        cyclic  (volatile! (transient #{}))
        counter (volatile! 0)]
    (letfn [(component! [root]
              ;; pop one SCC; it is cyclic when it has a second member — a singleton is
              ;; cyclic only through a self-edge, which `push!` tests
              (let [members (loop [acc []]
                              (let [w (.pop stack)]
                                (.remove on w)
                                (if (= w root) (conj acc w) (recur (conj acc w)))))]
                (when (> (count members) 1)
                  (vswap! cyclic #(reduce conj! % members)))))
            (visit! [v0]
              (let [frames (java.util.ArrayDeque.)]
                (letfn [(push! [v]
                          (let [i    (vswap! counter inc)
                                succ (vec (step v))]
                            ;; the self-edge is read off the successors already in hand:
                            ;; Tarjan does not see it (a singleton component is cyclic
                            ;; only through one), and asking `step` a second time to find
                            ;; it would double a walk's retrievals — the one thing the
                            ;; walk's read path promises it does not do
                            (when (some #(= v %) succ) (vswap! cyclic conj! v))
                            (.put index v i) (.put low v i)
                            (.push stack v) (.add on v)
                            (.push frames (object-array [v (java.util.ArrayDeque.
                                                            ^java.util.Collection succ)]))))]
                  (push! v0)
                  (while (not (.isEmpty frames))
                    (let [^objects f (.peek frames)
                          v          (aget f 0)
                          ^java.util.ArrayDeque todo (aget f 1)]
                      (if (.isEmpty todo)
                        (do (.pop frames)
                            (when (= (.get low v) (.get index v)) (component! v))
                            (when-not (.isEmpty frames)
                              (let [^objects p (.peek frames)
                                    u          (aget p 0)]
                                (.put low u (min (long (.get low u)) (long (.get low v)))))))
                        (let [w (.poll todo)]
                          (cond
                            (not (.containsKey index w)) (push! w)
                            (.contains on w)             (.put low v (min (long (.get low v))
                                                                          (long (.get index w))))
                            :else                        nil))))))))]
      ;; every node with a self-edge has an outgoing edge, so `walk-sources` names it and
      ;; the walk reaches it — testing at the push rather than per source therefore finds
      ;; the same set, and finds it without a second read of anybody's neighbours
      (doseq [s sources]
        (when-not (.containsKey index s) (visit! s)))
      (persistent! @cyclic))))

;; ---- the closure answer cache ------------------------------------------
;;
;; `reach` is a fixpoint, and asking for one twice over an unmutated KB is the same
;; question twice.  **This is the only layer that can answer the repeat**, and the reason
;; is how `memo-neighbours` reads: a walk asks each node's neighbour literal once, so the
;; per-literal solution cache has no repeat of a walk's to serve and is neither consulted
;; nor filled by one (`res/matches-visible`, `cached?` false).  The walk is also
;; where the time is — over a 40-member class it is
;; 127 µs against the 15 µs of per-ask dispatch a closed one-hop goal pays too, and
;; holding the answer puts a repeat at 52 µs, which is that dispatch plus the projection
;; and nothing else (`lein bench-walk`).
;;
;; **Why this can be cached where a `solve-goal` answer cannot.**  `literal-cache`'s
;; docstring gives the two properties a cached answer needs and `solve-goal` lacks: it
;; must not be **tier**-dependent (`ask-capped` drops provers above a cost tier) and must
;; not be **scope**-dependent (a pinned scope freezes what `observe/cached` returns).  A
;; reach set is neither.  Dropping this prover means `solve` is never called, so the
;; entry is never consulted rather than served across a tier it was not computed under;
;; and the walk reads `matches-visible` and the taxonomy's own generation-stamped memos,
;; never `observe/cached`, so no pin can hand it a frozen view.  The entry is an answer of
;; *this prover*, not of the registry.

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
  every entry at once and the stamp is therefore the map's rather than the entry's.  A KB
  with no cache atom answers nil, which is a miss and costs an extra walk rather than a
  wrong answer."
  [kb k ^long clock]
  (when-let [a (:closures kb)]
    (let [c @a]
      (when (== clock (long (:clock c -1)))
        (get (:entries c) k)))))

(defn- hold-closure
  "Hold `v` at `k`, under `clock`.  No `!`: it destroys nothing and every entry is
  derived, so the next ask recomputes whatever the drop below took."
  [kb k v ^long clock]
  (when (and (:closures kb) (<= (count v) (long *closure-answer-limit*)))
    (swap! (:closures kb)
           (fn [c]
             (let [c (if (== clock (long (:clock c -1)))
                       c
                       {:clock clock :members 0 :entries {}})
                   m (+ (long (:members c 0)) (count v))]
               (cond
                 (contains? (:entries c) k) c
                 (> m (long *closure-answer-limit*)) {:clock clock :members 0 :entries {}}
                 :else (assoc c :members m :entries (assoc (:entries c) k v))))))))

(defn- cached-reach
  "The reach of `node` under `pred` in `dir`, from the KB's cache when it holds one, else
  walked and held.

  The clock is read **before** the walk and the answer kept only if it has not moved by
  the time the walk finishes — `literal-cache/lookup`'s discipline, and the same two
  reasons.  Stamping afterwards would claim the set describes a state it was never
  computed from; and a caller that *writes while it reads* — forward chaining, whose own
  conclusions move the clock under it — fills this with nothing rather than with
  something stale.  Belief is covered by the same stamp: a relabel moves the clock, so a
  defeated edge retires the closure that crossed it without anything here knowing which
  entry to look for.  Belief *mode* is not: see `closure-key`."
  [kb dir pred node context step]
  (let [k     (closure-key dir pred node context)
        clock (observe/change-clock)]
    (or (closure-hit kb k clock)
        (let [v (reach (step node) step)]
          (when (== (observe/change-clock) clock) (hold-closure kb k v clock))
          v))))

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
  "One **breadth-first** walk out from `root`, recording for every node it reaches the
  node it was first reached from and the handles of that hop —
  `{node [parent #{handle}]}`, with `nil` as the parent of `root`'s own neighbours.

  Breadth-first and not depth-first, and that is the whole of what bounds the support: the
  first time a node is reached is along a **shortest** chain, so the handles walked back
  from it are one path's worth rather than a wandering one's.  A chain is therefore at most
  as long as the graph is deep, whatever order the edges arrived in.

  The neighbour sets come from `memo-neighbours`, so this reads the same step relation the
  reach walk does and — inside one search scope — off the same memo, paying no store read
  for a node the reach already visited."
  [kb dir pred root context]
  (let [edges #(memo-neighbours kb dir pred % context)]
    (loop [parents {} frontier (into clojure.lang.PersistentQueue/EMPTY
                                     (map (fn [[n hs]] [n nil hs]))
                                     (edges root))]
      (if-let [[n p hs] (peek frontier)]
        (if (contains? parents n)
          (recur parents (pop frontier))
          (recur (assoc parents n [p hs])
                 (into (pop frontier) (map (fn [[m hs2]] [m n hs2])) (edges n))))
        parents))))

(defn- support-chain
  "The handles of the chain `support-parents` recorded from its root to `node`, or nil
  when nothing reached `node`.

  Every hop contributes every handle that records it, which is the seam's sanctioned
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

(defrecord TransitivePredicateProver []          ; declared-transitive predicates (not genl/genlCx)
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal)
         (tax/has-prop? (:taxonomy kb) :transitive (first goal) context)
         (not (contains? transitive-predicates (first goal)))))
  (est-bindings [_ kb goal _] (est-by-functor kb goal))
  (cost         [_ _ _ _] :compute)              ; computes the reach fixpoint before the first answer
  ;; not the *sole* complete method — the same predicate may also be symmetric /
  ;; inverse, so union with those provers rather than running alone.
  (completeness [_ _ _ _] 70)
  (solve [_ kb goal context]
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
        ;; One variable in **both** places — `(P ?x ?x)` — asks which nodes lie on a
        ;; cycle, and binds one variable rather than two.  Stated rather than left to
        ;; fall through, for the `Duplicate key` reason `TransitivityProver` gives above.
        ;;
        ;; Answered by one condensation rather than one closure per source: `reaches? x x`
        ;; walks x's whole reach to *fail*, so the acyclic case — the ordinary one for a
        ;; `before` or `partOf` chain — would cost O(n²) to answer nothing.
        ;; A printed key, never a bare `sort`: these are **terms**, and a term need not
        ;; be `Comparable` — an unreifiable function application stays structural in
        ;; argument position, so a binding can be a list, and a bare sort throws
        ;; `ClassCastException` on a KB whose cycle relates two of them.  Printed form is
        ;; the content key the rest of this file already ranks terms by, and it is printed
        ;; through `nm/print-key` so an ambient `*print-length*` cannot elide two nested
        ;; terms to one prefix and drop the order onto the source's handle set.
        (= a b) (map (fn [x] {a x})
                     ;; the key keeps a list-valued binding sortable; built once per term
                     (nm/sort-by-content-key nm/print-key compare
                                             (on-a-cycle (walk-sources kb pred context) fwd)))
        ;; Both open: **nothing from here**, so the extent answers — the stored `pred`
        ;; facts and those of its `genl` sub-predicates, through the ordinary match path
        ;; like any other predicate.  `completeness` 70 is what makes that work: this is
        ;; not the sole complete method, so the registry unions rather than running it
        ;; alone, and an empty seq here is a contribution of none rather than an answer
        ;; of none.
        ;;
        ;; The asymmetry with the arms above is deliberate and is the whole reason this
        ;; arm is written out rather than left to fall through.  Those bound one end, so
        ;; the work and the answer are both bounded by one node's reach.  This one is
        ;; bounded by neither: the closure of a transitive relation is **quadratic** in a
        ;; chain's length, so enumerating it for a 1M-node chain offers half a trillion
        ;; pairs — not an answer a caller asked for but a process that does not come
        ;; back.  Laziness does not rescue it either, since `reach` is a fixpoint and one
        ;; pair costs a whole node's closure.  So the closure is computed for membership
        ;; and for one bound end, and is never stored and never enumerated whole.
        ;;
        ;; A caller who does want it asks for it: `(P ?x ?x)` above for the cycle
        ;; question, or one bound end per source term.
        :else [])))

  SupportingProver
  ;; **Both sets are empty, and that is a claim rather than an omission.**  The functors
  ;; this answers are whatever a KB declared `(transitive P)` of, so they are a taxonomy
  ;; read and not a constant a protocol with no `kb` argument could return.  The two
  ;; readers that would take a fixed set ask the taxonomy instead —
  ;; `chain/transitive-antecedent?` for which antecedent the join solves by walking, and
  ;; `chain/transitive-rejoin-rules` for which rules an arriving edge owes a re-join.  What
  ;; the seam *does* carry is `solve-with-support`, which is reached through
  ;; `solve-goal-with-support`'s `satisfies?` and needs no roster at all.
  (support-functors [_] #{})
  (support-sources  [_] #{})
  ;; The same solutions `solve` gives, in the same order, each carrying the handles of one
  ;; chain of stored edges that reaches it.  The bindings come from the same `reach` /
  ;; `reaches?` the plain arm uses — the closure cache included, so a supported ask costs
  ;; the same walk — and the chain comes from one breadth-first pass with parent pointers,
  ;; which shares `memo-neighbours` with it and so buys the parents for no extra store read
  ;; inside a search scope.
  ;;
  ;; A **cycle** answer is the one arm whose chain is a round trip rather than a path, and
  ;; it is walked per node rather than per source: `on-a-cycle` answers every source with
  ;; one condensation, but the *edges* of a node's loop are not in the condensation, so the
  ;; chain is taken by one breadth-first walk from that node back to itself.  Bounded by
  ;; the nodes actually on a cycle, which is none for the acyclic chain this arm is usually
  ;; asked about.
  ;;
  ;; Both arguments open answers nothing here, exactly as `solve` does, so there is no
  ;; support to report for a closure nobody asked to enumerate.
  (solve-with-support [_ kb goal context]
    (let [[pred a b] goal
          fwd   #(succs kb pred % context)
          back  #(preds-of kb pred % context)
          chain (fn [dir root node]
                  (support-chain (support-parents kb dir pred root context) node))]
      (cond
        (and (ground? a) (ground? b))
        (if-let [sup (and (reaches? (fwd a) fwd b) (chain :succ a b))]
          [[{} sup]]
          [])

        (ground? a)
        (let [parents (support-parents kb :succ pred a context)]
          (keep (fn [y] (when-let [sup (support-chain parents y)] [{b y} sup]))
                (cached-reach kb :succ pred a context fwd)))

        (ground? b)
        (let [parents (support-parents kb :pred pred b context)]
          (keep (fn [x] (when-let [sup (support-chain parents x)] [{a x} sup]))
                (cached-reach kb :pred pred b context back)))

        (= a b)
        (keep (fn [x] (when-let [sup (chain :succ x x)] [{a x} sup]))
              (nm/sort-by-content-key nm/print-key compare
                                      (on-a-cycle (walk-sources kb pred context) fwd)))

        :else []))))

(defrecord TransitiveInArgProver []       ; (transitiveInArg P n R) / (transitiveInArgInverse P n R)
  Prover
  (applicable? [_ kb goal context]
    (and (inherit/ground-goal? goal)
         (boolean (seq (inherit/positions kb (nm/functor goal) context)))))
  ;; **1 is the answer count, not the cost.**  A closed goal has at most the one empty
  ;; solution, and that is what the engine sorts complete provers on — but this prover
  ;; reads a predicate's whole extent (or the product of its arguments' reaches,
  ;; whichever is smaller) to produce it.  `cost` is where that shows: `:compute`, not
  ;; `:lookup`.  A reader of `query-plan` who takes est-bindings for cheapness is
  ;; reading the wrong column.
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :compute)
  ;; Augments facts and rules rather than replacing them — a preserved predicate is
  ;; still an ordinary predicate whose claims can be stored and derived directly.
  (completeness [_ _ _ _] 60)
  (solve [_ kb goal context]
    ;; One memo for the whole question, so `applicable?`'s `positions` read and every
    ;; reach walk below happen once rather than once per layer.
    (inherit/with-memo
      ;; `:ambiguous` yields nothing on purpose.  Claims that disagree at incomparable
      ;; specificity are a dilemma, and the engine's stance on those is to represent
      ;; rather than decide — answering either way here would be deciding one silently.
      (if (= :for (inherit/verdict kb goal context)) [{}] []))))

(defrecord SymmetricProver []
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal) (tax/has-prop? (:taxonomy kb) :symmetric (first goal) context)))
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

(defrecord InverseProver []
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal)
         (boolean (seq (tax/inverses-under (:taxonomy kb) (first goal) context)))))
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
    (let [[pred a b] goal]
      (solve-inverted kb pred a b context))))

(defrecord ReflexiveProver []
  Prover
  (applicable? [_ kb goal context]
    (and (binary? goal) (tax/has-prop? (:taxonomy kb) :reflexive (first goal) context)))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 50)
  (solve [_ _ goal _]
    (let [[_ a b] goal]
      (cond (and (ground? a) (ground? b)) (if (= a b) [{}] [])
            (ground? a) [{b a}]
            (ground? b) [{a b}]
            :else []))))

;; ---- evaluable predicates (computed, not stored) ------------------------

(def evaluable-predicates
  "Predicates a prover computes from its ground arguments rather than looks up.
  `lessThan` / `greaterThan` are the **variable arity** arithmetic comparisons —
  `(lessThan 1 2 3)` reads as the chain 1 < 2 < 3; `greaterThan` is folded to `lessThan`
  when *stored* (see `vaelii.impl.sentex`), but a caller may still ask it directly, so both
  are answered here.

  `integer` is the **unary** EDN-kind check: `(integer 5)` holds because 5 *is* an integer,
  no stored fact needed.  It is a built-in for the same reason the comparisons are — the
  kind is always present — and it is what lets the four sign-refined integer collections in
  CxCore (`positive_integer` …) be defined by `defnSufficient` / `defnNecessary` conditions
  built on `(integer ?x)` and resolved **by evaluation** at query time, at zero storage
  cost, rather than by a forward rule that never fires because the computed condition is
  never a believed fact (docs/defns.md)."
  '#{lessThan greaterThan integer})

(defrecord EvaluableProver []                    ; arithmetic comparison + EDN-kind check
  Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (contains? evaluable-predicates (first goal))
         (if (= 'integer (first goal))
           ;; the unary kind check: one ground argument, of any EDN kind (a non-integer
           ;; simply yields no solution — which is what makes a failing `(integer ?x)`
           ;; necessary a sound negative witness for a string / symbol member).
           (and (= 1 (count (rest goal))) (ground? goal))
           (and (>= (count (rest goal)) 2)
                (every? number? (rest goal))))))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative for a ground goal: the arithmetic cannot be wrong about two numbers, nor
  ;; `integer?` about one term's EDN kind.
  (completeness [_ _ _ _] 100)
  (solve [_ _ goal _]
    (let [args (rest goal)
          ok   (case (first goal)
                 lessThan    (apply < args)
                 greaterThan (apply > args)
                 integer     (integer? (first args))
                 false)]
      (if ok [{}] []))))

;; ---- different: the unique-name assumption over the equality closure ----

(declare believed-sentexes-with)                 ; defined below, beside ArgTypeProver

;; The identity exemption for `indeterminate_term` members: the UNA is
;; suspended for an indeterminate term — a term that stands for some object without pinning
;; down which — so `(different indeterminate X)` is NOT provable against a determinate `X`
;; until a `rewriteOf`/merge pins it (at which point `rep` lifts the exemption).  Gated on
;; the extensible category, with the skolem constant its built-in first member: a skolem's
;; membership is never a stored fact, so it is read off its `SkolemFn` `termOfUnit`
;; expression, while a further kind added with `(genl NewKind indeterminate_term)` is picked
;; up through ordinary membership.  `vaelii.impl.predall/indeterminate-term?` is the audit's
;; twin of this; the two cannot share code (predall sits above the prover registry), so both
;; read the one category.
(defn- reified-nat-symbol? [term]
  ;; a reified constant — a symbol in a reserved reified namespace; the cheap gate before
  ;; the skolem `termOfUnit` read.  Master: `nat/reified-namespaces` (#{"nat" "cx"}) —
  ;; copied because the provers layer cannot require nat without a cycle through kb; if
  ;; the reserved set ever grows, this copy must move with it.
  (and (symbol? term) (contains? #{"nat" "cx"} (namespace term))))

(defn- skolem-indeterminate? [kb term context]
  (and (reified-nat-symbol? term)
       (boolean
        ;; 'SkolemFn is skolem/skolem-function's value, copied for the same cycle reason
        (some (fn [[_ b]] (let [e (get b '?e)]
                            (and (sequential? e) (= 'SkolemFn (first e)))))
              (res/matches-visible kb (list 'termOfUnit term '?e) context)))))

(defn- category-indeterminate? [kb term context]
  ;; a believed member of `indeterminate_term` or of a collection that genl-reaches it.
  ;; The direct membership is one indexed point-read and is consulted unconditionally —
  ;; gating it on declared subkinds made a direct member's exemption depend on an
  ;; unrelated (genl _ indeterminate_term) declaration.  The membership SCAN stays
  ;; gated: only walk the term's memberships when the category actually has extensions,
  ;; so a KB that never uses subkinds pays one point-read plus one taxonomy read per
  ;; `different` and no index scan.
  (let [tax (:taxonomy kb)]
    (or (boolean (seq (res/matches-visible kb (list 'indeterminate_term term) context)))
        (and (> (count (tax/specs tax 'indeterminate_term context)) 1)
             (boolean
              (some (fn [s]
                      (let [sen (:sentence s)]
                        (and (sequential? sen) (= 2 (count sen)) (= term (nth sen 1))
                             (symbol? (nth sen 0))
                             (contains? (tax/genls tax (nth sen 0) context) 'indeterminate_term))))
                    (believed-sentexes-with kb term context)))))))

(defn- indeterminate-term-arg? [kb term context]
  (or (skolem-indeterminate? kb term context)
      (category-indeterminate? kb term context)))

(defn- pairwise-distinct?
  "Do no two of `args` share an equivalence class?  A term is trivially in its own
  class, so `(different A A)` fails on the `=` arm without consulting the closure at
  all — which also keeps the answer right for a term the closure has never seen.

  Read from `context`: the unique-name assumption is what a context holds until
  *it* is told otherwise, so a merge it cannot see leaves the two names different
  there.  Otherwise a private `(sameAs A B)` would silently retire the UNA everywhere.

  Compound arguments normalize **recursively** (`res/representative-term`), which is what
  makes the answer congruence-consistent: the closure is keyed by symbol, so a flat
  lookup on `(QuantityFn 5 Kilogram)` returns it unchanged and would report it different
  from `(QuantityFn 5 Kg)` with `(sameAs Kilogram Kg)` believed.

  The UNA is **suspended** when any argument is an unpinned `indeterminate_term`: an
  indeterminate term is not provably different from anything until a merge pins it, so the
  whole difference goal is left unprovable (`rep` self-equal witnesses the unpinned state —
  a `rewriteOf`/`equals` merge moves `rep` off the term and restores the UNA)."
  [kb context args]
  (let [vis     (res/visible-supporter-fn kb context)
        rep     #(res/representative-term kb vis %)
        v       (vec args)
        exempt? (fn [t] (and (= (rep t) t) (indeterminate-term-arg? kb t context)))]
    (and (not-any? exempt? v)
         (every? (fn [[a b]] (not (or (= a b) (= (rep a) (rep b)))))
                 (for [i (range (count v)), j (range (inc i) (count v))]
                   [(nth v i) (nth v j)])))))

(defrecord DifferentProver []
  Prover
  ;; **Ground only, expressed here rather than filtered in `solve`.**  `(different ?x
  ;; Y)` asks for every term in the KB outside Y's class — an enumeration of the whole
  ;; domain — so the prover *refuses* the goal instead of answering it explosively.
  ;; Refusing and answering-with-nothing are different claims, and only the first is
  ;; honest: `plan` shows no prover, and a rule antecedent that reaches here unbound
  ;; is a planning bug the author can see rather than a silent empty join.
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 'different (first goal))
         (>= (count (rest goal)) 2)
         (every? ground? (rest goal))))
  (est-bindings [_ _ _ _] 1)                    ; ground test: it holds or it does not
  (cost         [_ _ _ _] :lookup)
  ;; Authoritative.  `different` is not assertible at all (`wff` refuses it), so the
  ;; superset claim holds against an empty field rather than against content this
  ;; happens to absorb — and `sole-prover` guards it like any other claimant anyway,
  ;; which for a shape nothing can state costs nothing.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (if (pairwise-distinct? kb context (rest goal)) [{}] [])))

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
  other arity is left to the other provers.  A caller whose fn is variadic pins `:arity`
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

(def ^:private deferred-est
  "The `est-bindings` an evaluatable reports while its inputs are unbound.  It computes
  from ground inputs and enumerates nothing, so on unbound inputs it can neither answer
  nor prune — the most *unselective* a literal can be, and reported as such so the join
  planner (`vaelii.impl.plan`, through `est-goal`) runs a generator that binds those
  inputs first and the computation lands with everything ground.  Deliberately below
  `Long/MAX_VALUE`, which the planner's fan-out sums."
  1000000000)

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
  `pred` — the value `vaelii.core/add-evaluatable` registers.  Answers a goal by
  **computing**, never by looking one up, in one of two shapes:

  * **check** (no `:result`) — `(pred a …)` holds when `f` applied to the ground
    arguments returns truthy, like `lessThan`.  Every argument must be ground.
  * **result-binding** (`:result` names an output slot) — `(pred … ?out …)` binds `?out`
    to `(f <the other, ground arguments>)`, like `evaluate`.  A ground output slot is
    checked against the computed value instead of bound.

  `opts` (a map, or nil):

  * `:result`       — `:first` (the `evaluate` convention), `:last`, or a 0-based index;
                      its presence selects the result-binding shape.
  * `:arity`        — the fn's **input** count (an int or a set of them), for `applicable?`
                      to dispatch on; derived from `f` by reflection when omitted, which a
                      variadic fn needs stated.
  * `:cost`         — a `cost-tiers` keyword; `:lookup` by default.
  * `:completeness` — 0..100; **100** by default, the authoritative-computation claim the
                      built-in evaluables make (`sole-prover` still guards it against a
                      shadowing rule/inverse the KB adds).  Drop it to 50 for a predicate a
                      KB also stores facts under, so the computed answers *augment* the
                      stored ones instead of standing alone.

  Registered through `add-prover`, so a wrapped fn is an ordinary member of the registry:
  it answers a direct `ask` / `query` goal, and — because the node engine's leaf **is**
  the registry — it discharges a conjunct or a rule antecedent inside a `query` with a
  `:max-depth`, appearing as a `:leaf` in a `{:proof? true}` derivation.  **Forward
  materialization reaches it too**: `vaelii.impl.chain/deferred-antecedent?` treats a
  registered evaluatable as a deferred antecedent, computing it through this registry the
  way it computes the built-in `vaelii.impl.sentex/deferred-predicates`, so `ask` agrees
  with `query` on a forward rule with an evaluatable antecedent.  One path does not reach
  it, by the existing engine's design rather than this wrapper's: the DFS `prove`, whose
  leaf is the stored facts.  See the query-engine section of docs/inference.md."
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

(defn evaluatable-est-override
  "An `:est-override` for `vaelii.impl.plan/order` that costs only `preds` — a KB's
  registered evaluatable functors (`evaluatable-preds`) — and returns nil for every
  other goal so the index model ranks the rest.  A goal still carrying an unbound input
  is reported as maximally unselective (`deferred-est`) and a fully ground one as the
  single answer it computes, so the planner runs the generators that bind its inputs
  first and the computation lands with everything ground.

  Forward chaining (`vaelii.impl.chain/planned-join`) plans with this so a registered
  evaluatable antecedent is pinned after its binders — the self-deferral the built-in
  evaluables get for free from canonical antecedent order, which the static
  `deferred-predicates` set drives and a per-KB evaluatable is not in.  Scoped to the
  evaluatables on purpose: forward chaining's leaf is the stored facts (`*matcher*`),
  for which the index model is the right cost, so every other goal is left to it.

  Nil when `preds` is empty, so `planned-join` passes no override and plans exactly as
  before."
  [preds]
  (when (seq preds)
    (fn [goal _bound]
      (when (and (sequential? goal) (seq goal) (contains? preds (first goal)))
        (if (ground? goal) 1 deferred-est)))))

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
  ground measures, never stored (declared in the upper CxMeasure, computed here)."
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
  `(QuantityIntervalFn Lo Hi Unit)`, numeric magnitude(s) and a symbol unit?  The
  check-only gate: a comparison is claimed only when *both* arguments are ground
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
  "One reading of the unit table: `[values handles]`, where `values` is the bindings of
  `ks` that every believed match of `pat` visible from `context` **agrees** on — nil when
  there is no match and nil when two of them disagree — and `handles` names the
  declarations it was read from.  One `matches-visible` read, belief- and
  context-filtered.

  Agreement rather than the first match, because the first is whichever the index yields,
  which is a handle order: a unit declaring two conversion factors would convert by
  whichever was written first, and the same knowledge loaded in the other order would
  give a different number out of the same KB.  The unit table therefore takes the rule
  the rest of the engine takes for a reading stated twice over —
  `duration/interval-length-with-support` on two lengths, `stp/endpoints-of` on two
  starts: a disagreement is declined, not
  adjudicated.  Restating one declaration in several contexts of the cone is not a
  disagreement; the matches carry the same bindings and collapse to one.

  `ks` is a vector because a `conversionFactor` names a base **and** a factor, and the two
  are one reading: taking the base from one declaration and the factor from another would
  convert into a unit nothing said it converts to.

  The handles are **every** declaration the reading was taken over, not one of them, and
  for the reason the value is an agreement: the reading is a property of the *set*, since
  a second declaration that agrees collapses into it while a second that disagrees
  declines it outright.  So the set is what a conclusion drawn through this table rests on,
  and naming one member of it would be naming whichever the index yielded first.
  Over-approximating in that direction is the deliberate half of the trade: retracting one
  of two agreeing declarations withdraws a conclusion the survivor would still license,
  where naming only the survivor would make belief depend on which declaration arrived
  first — the worse of the two (docs/nmtms.md)."
  [kb pat context ks]
  (let [ms (res/matches-visible kb pat context)
        vs (into #{} (map (fn [m] (mapv #(get (second m) %) ks))) ms)]
    (when (= 1 (count vs))
      [(first vs) (into #{} (map first) ms)])))

(def unit-table-predicates
  "The two predicates a measure is normalized through — what `normalize-quantity` reads,
  and therefore what a conclusion drawn from a measure comparison rests on besides the
  facts that bound the measures."
  '#{dimensionOf conversionFactor})

(defn normalize-quantity-with-support
  "Resolve a ground measure to `[[dimension lo-base hi-base] handles]` — its dimension and
  its magnitude bounds converted **direct-to-base** (one multiply, no chaining), together
  with the declarations the conversion was read from.  A point `(QuantityFn N U)` has
  `lo-base = hi-base`; an interval keeps both bounds.

  * **Dimension** is `(dimensionOf U ?d)`, or **U itself** when the unit declares none —
    so two measures in the *same unit* are always comparable (their dimension is that
    unit) while two distinct undeclared units are not (their dimensions differ).  A
    declared `dimensionOf` is what lets separate units share one dimension and compare.
  * **Base magnitude** is `N × (conversionFactor U ?base ?factor)`, the factor
    defaulting to `1` when the unit declares none (it is then its own base).  Every unit
    of one dimension must convert to a *single* base unit for the magnitudes to line up
    — the direct-to-base contract, no transitive chaining.

  A unit the KB declares **twice over and differently** has declared nothing: both reads
  go through `table-read`, so such a unit falls back to being its own dimension and its
  own base rather than converting by whichever declaration is indexed first.  Nothing is
  answered wrongly and nothing is answered differently in another load order — the price
  is that the unit compares only against itself, which is what a KB that cannot say how
  long a Furlong is has actually told the engine.

  The handles are **empty** when the unit declares neither, and that is not a gap: the two
  fallbacks are what the *absence* of a declaration means, and an absence is not a sentex
  a retraction can take away.  A declaration arriving later does change the answer, and it
  is `SupportingProver`'s `support-sources` that puts it in front of the rules concerned
  rather than a handle here."
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
  **interval** when they do not.  That is what keeps a computed answer honest — an
  over-approximation renders as an interval and says so, rather than picking a figure
  out of a range it only bounded."
  [lo hi unit]
  (let [lo* (round-magnitude lo)
        hi* (round-magnitude hi)]
    (if (<= (abs (- lo* hi*)) *quantity-tolerance*)
      (list 'QuantityFn lo* unit)
      (list 'QuantityIntervalFn lo* hi* unit))))

(defn- q=  [a b] (<= (abs (- a b)) *quantity-tolerance*))
(defn- q<  [a b] (< a (- b *quantity-tolerance*)))
(defn- q>  [a b] (> a (+ b *quantity-tolerance*)))
(defn- q<= [a b] (<= a (+ b *quantity-tolerance*)))
(defn- q>= [a b] (>= a (- b *quantity-tolerance*)))

(defn- measures-hold?
  "Does comparison `pred` hold between two normalized measures `[dim lo hi]`?  The
  interval reading is **necessary** (definite): the comparison holds only when it holds
  of every point of each interval, which collapses to ordinary number comparison for a
  point (`lo = hi`).  A **dimension mismatch is never comparable** — the guard yields nil
  (⇒ the goal fails); it never throws."
  [pred [d1 lo1 hi1] [d2 lo2 hi2]]
  (when (= d1 d2)
    (case pred
      sameQuantity               (and (q= lo1 lo2) (q= hi1 hi2))
      quantityLessThan           (q< hi1 lo2)
      quantityGreaterThan        (q> lo1 hi2)
      quantityLessThanOrEqual    (q<= hi1 lo2)
      quantityGreaterThanOrEqual (q>= lo1 hi2)
      nil)))

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
                          (normalize-quantity kb a context)
                          (normalize-quantity kb b context))
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
          [na sa] (normalize-quantity-with-support kb a context)
          [nb sb] (normalize-quantity-with-support kb b context)]
      (if (measures-hold? pred na nb) [[{} (into sa sb)]] []))))

;; ---- negation as failure: unknown / thereExists -------------------------
;; `(unknown S)` is closed-world negation: it holds exactly while `S` is *not*
;; derivable.  `(thereExists ?x S)` existentially quantifies `?x` (a variable or a
;; vector of them), so it closes those variables off — which is what lets
;; `(unknown (thereExists ?x S))` say "there is no `x` such that S".
;;
;; Both run their argument through the **registry** — the same list `exception-holds?`
;; uses.  No member of the registry expands a rule, and that is what closed-world
;; reasoning needs rather than merely tolerates: it must read what the KB *derives
;; without an unbounded proof search*, so a forward-derived fact counts (it is stored
;; and believed by the time the query runs) while something reachable only by backward
;; chaining does not.  Both are **ground/closed only** — applicability refuses a goal
;; with a free variable (`free-vars`, which excludes the quantified ones), the same
;; honest refusal `different` makes: an open `(unknown (P ?x))` is not a test but a
;; search of the whole domain's complement, and answering it explosively would be
;; wrong.  Nothing about either is stored — see docs/naf.md.

(defn- conjunct-computed?
  "Is this conjunct **computed** rather than matched — a nested `(unknown …)`, an
  evaluable, an aggregate?  A matched conjunct produces bindings and so can run first; a
  computed one consumes them and has to wait, which is the whole of the ordering below."
  [c]
  (or (sx/unknown? c) (sx/deferred-literal? c)))

(defn- planned-conjuncts
  "`conjuncts` in an order every computed conjunct can run in: each one placed once the
  variables it reads are bound, matched conjuncts otherwise keeping their canonical
  order.

  A joined query threads bindings left to right, so a nested `(unknown (asleep ?y))`
  reached before the `(childOf Bob ?y)` that binds `?y` would be an open NAF goal no
  prover claims — answered empty, and read as *not derivable*, which is the silent wrong
  answer rather than a missing one.  Canonical order sorts a query's conjuncts blind to
  variable names (`sentex/sort-naf-conjuncts`), so the written order is not available to
  rely on and the plan is recomputed here instead — the same decision `plan/order` makes
  for a rule body, in the small.

  A conjunct nothing can make ready is placed anyway rather than dropped: the assert-time
  check (`sentex/check-naf-closed`) is what refuses that rule, and a *goal* asked
  directly deserves the honest empty answer rather than a silent reordering."
  [conjuncts bound]
  (loop [pending (vec conjuncts) bound (set bound) out []]
    (if (empty? pending)
      out
      (let [i (or (first (keep-indexed
                          (fn [i c] (when (or (not (conjunct-computed? c))
                                              (every? bound (sx/deferred-input-vars c)))
                                      i))
                          pending))
                  0)
            c (nth pending i)]
        (recur (into (subvec pending 0 i) (subvec pending (inc i)))
               (into bound (concat (sx/free-vars c) (sx/deferred-output-vars c)))
               (conj out c))))))

(defn conjunction-solutions
  "Lazy solutions of the conjunctive level-6 body `conjuncts`, extending `bindings`, in
  `context` — **the** joined NAF evaluator, and the only one.

  Each conjunct is substituted with what the conjuncts before it bound, put in the normal
  form the context answers under (`norm`, or nil for none), and run through the registry;
  the solutions thread on.  Four properties, and the last is the one reading the
  conjuncts independently cannot give:

  * **All must hold.**  A conjunction is derivable only if every conjunct is, which a
    join says by having no solution the moment one of them contributes none.
  * **One answer suffices.**  `res/lazy-mapcat` throughout, so a caller taking one
    solution never enumerates an extent.
  * **No backchaining.**  The registry expands no rule, so this reaches genl
    specificity, the genlCx closure, the transitive / symmetric / inverse metadata,
    disjointness and the evaluables, and never starts a proof search from inside the
    relabel loop.
  * **The conjuncts may share a variable.**  A quantifier binds it and the join carries
    it, so `(unknown (thereExists ?c (and (childOf Tom ?c) (sick ?c))))` asks for one
    witness satisfying both — which is what its author means, and what reading the
    conjuncts independently could not say (docs/naf.md, docs/defenses.md).

  A **ground** conjunction is the degenerate case and is unchanged by the join: every
  conjunct substitutes to a ground goal, each contributes `{}` or nothing, and the
  result is exactly the independent existence checks an `exceptWhen` has always been."
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
             (planned-conjuncts conjuncts (keys bindings))))))

(defn conjunction-derivable?
  "Does the conjunctive level-6 body `conjuncts` have a solution under `bindings` in
  `context`?  An **empty** conjunction has none: nothing can make it derivable, which is
  the reading an empty exception has always taken."
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
  ;; Authoritative: `unknown` is not assertible, so nothing else can hold a claim about
  ;; it, and the closed-world answer is already a function of what the rest of the stack
  ;; derives.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    ;; NAF: the argument is *un*known exactly when the level-6 query finds nothing.  A
    ;; conjunctive argument is joined (`conjunction-solutions`), so its conjuncts may
    ;; share a quantifier's variable; an empty conjunction never holds, as an empty
    ;; exception never does.
    (if (conjunction-derivable? kb (sx/naf-query-conjuncts goal) {} context)
      []                                          ; S is derivable → (unknown S) fails
      [{}])))                                     ; S is not derivable → (unknown S) holds

(defrecord ThereExistsProver []
  Prover
  (applicable?  [_ _ goal _] (and (sx/there-exists? goal) (empty? (sx/free-vars goal))))
  (est-bindings [_ _ _ _] 1)                    ; an existence check: one answer or none
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    ;; existence over the quantified variable(s): any solution of the body suffices,
    ;; and the quantified variables are **projected out** — this binds nothing outside.
    ;; A conjunctive body is joined, so the conjuncts share the binder and one witness
    ;; has to satisfy all of them.
    (if (conjunction-derivable? kb (sx/conjuncts (nth goal 2)) {} context)
      [{}]
      [])))

(defn closed-extent?
  "Is `pred`'s believed extent declared **complete** as read from `context` — is
  `(closed_extent_predicate pred)` visible up its `genlCx` cone?

  Scoped, like `abducible_predicate` and `modal_predicate` and for their reason: this is a
  *policy* of the context that grants it, not a claim about the predicate that holds
  wherever it is mentioned.  One theory may be willing to read a vocabulary's extent as
  complete where another, reading the same predicate, will not."
  [kb pred context]
  (and (symbol? pred) (tax/has-prop? (:taxonomy kb) :closed-extent pred context)))

(defrecord ClosedExtentProver []
  Prover
  ;; `(not (P a …))` where P's extent is declared complete from here.  Ground only, for
  ;; `unknown`'s reason: an open `(not (P ?x))` is a search over the domain's complement.
  (applicable?  [_ kb goal context]
    (and (rules/negative-literal? goal)
         (empty? (sx/free-vars goal))
         (closed-extent? kb (nm/functor (second goal)) context)))
  (est-bindings [_ _ _ _] 1)                    ; a ground test: it holds or it does not
  ;; a bounded level-6 subquery on the positive goal, so at worst a closure
  (cost         [_ _ _ _] :compute)
  ;; Partial: a stored `(not (P a))` is answered by FactProver, and this augments it
  ;; rather than replacing it.  The union dedups, so the two agree wherever both answer.
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
    ;; `(forall ?y (implies B H))` is ¬∃?y (B ∧ ¬H), which in a closed world is the
    ;; nested NAF `(unknown (thereExists ?y (and B (unknown H))))`.  Desugared and handed
    ;; **back to the registry**, so the goal and the rule antecedent are answered by one
    ;; mechanism rather than by two readings that could drift (docs/naf.md).
    (solve-goal-with kb (registry kb) (sx/desugar-forall-literal goal) context)))

;; ---- evaluative defnSufficient: prove membership by evaluating the condition ----
;; `(defnSufficient Coll C)` says the condition `C` on the member `?x` is enough for
;; membership.  Its forward materialization (`sentex/defn-companion-rules`) is a rule
;; `(implies C (Coll ?x))` that fires only when `C` is a *believed* fact — so a `C` built
;; from **computed** predicates (`integer`, `lessThan`, an `add-evaluatable` check) is
;; never stored, the rule never fires, and the member is never derived.  This prover
;; closes that at query time: on `(Coll a)` it finds `Coll`'s visible defnSufficient
;; conditions, substitutes the queried member `a` for `?x`, and asks whether the condition
;; holds through the registry — which *evaluates* the computed predicates against `a`.
;;
;; Level-6 (`conjunction-derivable?` over the registry, no backchaining), so its reach
;; matches the forward rule's: a conjunctive condition is joined, and each conjunct is
;; answered by the evaluables, the facts and the closures — the same evaluator
;; `unknown` / `thereExists` / `exceptWhen` read.  It **augments** the fact prover and the
;; forward rule (completeness 50): a condition that *is* believed is answered identically
;; through `FactProver` and deduped, so this only adds the computed case.
;;
;; **Positive membership descends to a spec's sufficient.**  `(Coll a)` is provable
;; when `Coll`'s own defnSufficient passes OR a **spec**'s does — a spec is more specific,
;; below `Coll` on the genl edges (`(genl spec Coll)`), and its members are `Coll`s.  So
;; the walk descends the spec cone (`tax/specs`, which is reflexive — it includes `Coll`
;; itself, folding the own-sufficient and the spec-sufficient cases into one iteration).
;;
;; A passing sufficient admits even against a failing OWN necessary — sufficient is
;; authoritative, the resulting inconsistency documented not arbitrated.  But a failing
;; necessary of a *strict genl* fast-fails the query (`genl-necessary-fails?`): on a
;; consistent KB the broadest disqualifier is checked most-general-first and the walk
;; rejects before the sides or the sufficient are ever evaluated.  The negation prover (a
;; failing necessary proves ¬member) is the converse build, below.

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

(defn- spec-sufficient-conditions
  "Every defnSufficient condition in `coll`'s spec cone (reflexive `tax/specs`), lazily —
  `coll`'s own and every spec's, the descent the positive walk admits on."
  [kb coll context]
  (mapcat #(defn-conditions kb 'defnSufficient % context)
          (tax/specs (:taxonomy kb) coll context)))

(defn- most-general-first
  "`colls` ordered most-general-first — a linear extension of the genl partial order, so an
  ancestor is always checked before any of its descendants.  The key is the ancestor count
  (`tax/genls` is reflexive; a genl's ancestors are a subset of its spec's, so the count
  ascends down the chain), with a printed-term tie-break for a deterministic order."
  [tx context colls]
  (sort-by (fn [c] [(count (tax/genls tx c context)) (nm/print-key c)]) colls))

(defn- genl-necessary-fails?
  "Does some necessary of a **strict** genl of `coll` fail for `member` — the positive
  query's fast-fail?  Walks the strict-genl cone most-general-first and stops at the first
  failing necessary (the broadest disqualifier), so a consistent KB rejects without
  evaluating the sides or the (possibly expensive) sufficient.
  **Strict** (excludes `coll` itself): a collection's own necessary does not veto its own
  sufficient — sufficient is authoritative — and the cone is a set, so a defn reachable
  by two genl paths (a diamond's apex) is checked exactly once.  Sound only on a consistent
  KB: on an inconsistent one the negation prover records
  the ¬member half and this merely declines to admit."
  [kb coll member context]
  (let [tx        (:taxonomy kb)
        ancestors (disj (tax/genls tx coll context) coll)]
    (boolean
     (some (fn [g]
             (some (fn [c] (not (condition-holds? kb c member context)))
                   (defn-conditions kb 'defnNecessary g context)))
           (most-general-first tx context ancestors)))))

(defrecord DefnSufficientProver []
  Prover
  ;; A ground unary membership goal `(Coll a)` for a `Coll` whose spec cone carries a
  ;; visible defnSufficient.  Ground because the condition is evaluated against the member:
  ;; an open `(Coll ?x)` would ask a computed condition to *enumerate* its members, which a
  ;; sufficient built from `integer` / `lessThan` cannot do (the infinite-extent generator
  ;; is the punted, theoretically-hard case).
  (applicable? [_ kb goal context]
    (and (sequential? goal)
         (symbol? (first goal))
         (= 1 (count (rest goal)))
         (ground? goal)
         (not (contains? *defn-stack* (first goal)))
         (boolean (seq (take 1 (spec-sufficient-conditions kb (first goal) context))))))
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
;; (two-valued — the condition is evaluably false).  A `Coll` with no necessary in its cone
;; makes this prover inapplicable, so absence of a proof is never mistaken for a disproof.

(defn- cone-necessary-conditions
  "Every defnNecessary condition in `coll`'s **reflexive** genl cone (`tax/genls`), lazily
  — `coll`'s own and every genl's.  Reflexive (unlike the positive fast-fail's strict cone)
  because a collection's own failing necessary is itself a sound negative witness."
  [kb coll context]
  (mapcat #(defn-conditions kb 'defnNecessary % context)
          (tax/genls (:taxonomy kb) coll context)))

(defrecord DefnNecessaryNegationProver []
  Prover
  ;; A ground `(not (Coll x))` for a `Coll` whose reflexive genl cone carries a visible
  ;; defnNecessary.  Ground, for the positive walk's reason: an open `(not (Coll ?x))` is a
  ;; search over the domain's complement, not a test.
  (applicable? [_ kb goal context]
    (and (rules/negative-literal? goal)
         (empty? (sx/free-vars goal))
         (let [lit (second goal)]
           (and (= 1 (count (rest lit)))
                (ground? lit)
                (not (contains? *defn-stack* (first lit)))
                (boolean (seq (take 1 (cone-necessary-conditions kb (first lit) context))))))))
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
        ;; ¬member is proved by the first necessary that fails anywhere in the cone.
        (if (some (fn [c] (not (condition-holds? kb c member context)))
                  (cone-necessary-conditions kb coll context))
          [{}]
          [])))))

;; ---- aggregation: a reduction over a query's solutions ------------------
;; `(agg/count ?n ?v <body>)` and its four siblings are the third member of the
;; `unknown` / `thereExists` family, and they are built out of the same three
;; decisions.
;;
;; **The registry, and no rule expansion.**  The body runs through the registry for
;; exactly the reason `unknown` does: a count that could launch an open-ended backward
;; search is a count whose cost is unbounded, and it would be reached from inside a
;; relabel loop.  That is less of a restriction than it sounds.
;; A forward-derived fact *is* counted (it is stored and believed by the time the
;; query runs), and so is a relation held in the cached closures — `genl`, a
;; `(transitive ancestorOf)` walked by `TransitivePredicateProver` — which is what the
;; per-node transitive-ancestor count is made of.  What a level-6 body cannot see is a
;; relation reachable *only* by backward chaining: a `set/backwardRule`'s conclusions.
;;
;; **`?v` is projected out** (`sx/free-vars`), so `?n` is the only binding produced —
;; `thereExists`'s rule applied to a variable that is counted rather than witnessed.
;;
;; **Bind or check.**  A variable `?n` takes the computed value; a bound one is
;; compared against it, so an aggregate reads as a test as readily as a computation
;; (`EvaluateProver` makes the same pair).  The check arm is what lets a *firing* be
;; re-verified against the count it rested on, which is how an aggregate antecedent is
;; maintained (docs/aggregate.md).
;;
;; Nothing is stored and no JTMS node is created: a count is recomputed, never cached.

(defn- aggregate-violation!
  "File a numeric error in the violations ledger — **once per distinct error**.

  Unlike a dropped conclusion, an aggregate error is not an event that happened once:
  a count is recomputed, never cached, so the same bad extent is reduced again on every
  query, every re-check and every settle pass.  `violations/report-once` is what keeps
  the ledger from filling with copies of one defect, and it is shared with the other
  refusal that is recomputed rather than remembered — a post-join literal declined for
  disagreeing with itself."
  [kb goal context message detail]
  (violations/report-once kb (merge {:violation :aggregate :sentence goal :context context
                                     :message message}
                                    detail)))

(defn- aggregate-values
  "The **distinct** values `?v` takes over the body's solutions, in solution order.

  The body is a **joined** conjunction (`conjunction-solutions`), the same evaluator
  `unknown` and `exceptWhen` read: a census over `(and (childOf Bob ?c) (asleep ?c))`
  counts the children who are asleep, one witness satisfying both conjuncts, rather than
  the children and the sleepers apart.  A one-literal body is the degenerate case and is
  unchanged by the join — one conjunct, one registry call, the same solutions.

  Distinct by the equality closure's representative, so a `sameAs`-merged pair counts
  once: two names for one thing are one value, which is the whole point of holding the
  closure.  A solution that binds `?v` to nothing contributes nothing — it witnessed
  the body without reaching the variable being reduced over.

  **Read from `context`**, the same scoping `all-different?` puts on the same partition
  and for the same reason: a census is of what *this* context believes, and the unique
  names it holds are the ones it has not been told to merge.  A `(sameAs A B)` stated in
  a context would otherwise collapse two of them into one everywhere — including in
  the general context that was never told, whose own solutions still name both.

  The scoped read is asked per value, so it takes `merged-term-pred`'s one-snapshot
  gate rather than `merged?`'s per-call deref: a KB that has merged nothing drops the
  filter outright and a symbol that is in no class costs one set membership.  A
  **compound** value takes the recursive `representative-term` — the closure is keyed
  by symbol, so the flat lookup hands a compound back unchanged, and `(QuantityFn 5
  Kilogram)` beside `(QuantityFn 5 Kg)` under a merged unit would count as two values
  (`res/representative-term`'s own example)."
  [kb goal v context]
  (let [merged (tax/merged-term-pred (:taxonomy kb))
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
  "The values as one dimension's `[unit [lo hi]...]`, or nil when they are not all
  measures of a single dimension.  The unit answers are rendered in is the dimension's
  base — read out of the same `conversionFactor` table the normalization multiplied
  by, so nothing separate can disagree about the unit the arithmetic happened in.

  **Whose base**, though, is a question a dimension can answer two ways.  The
  direct-to-base contract says every unit of a dimension converts to a *single* base, and
  a KB that breaks it — two units of one `dimensionOf` naming different bases — has
  values whose magnitudes are already in incomparable scales.  Reading the base off
  whichever measure the extent yielded first would render the same knowledge in different
  units in different arrival orders, since the values reach here in solution order.  So
  the unit is taken from the **content-least** of them (`nm/min-by-content-key`): still
  arbitrary where the KB is inconsistent, but the same answer whatever the arrival order,
  and on the conforming KB where every base agrees there is only one answer to give."
  [kb values context]
  (when (every? measure? values)
    (let [norms (mapv #(normalize-quantity kb % context) values)
          dims  (into #{} (map first) norms)]
      (when (= 1 (count dims))
        [(base-unit-of kb (nm/min-by-content-key identity (map last values)) context)
         (mapv (fn [[_ lo hi]] [lo hi]) norms)]))))

(defn- reduce-numbers
  "The reduction of a non-empty numeric value list.  `:min` / `:max` / `:avg` have no
  answer over nothing, which is why the empty case never reaches here.

  **Summed in sorted order, because floating-point addition is not associative.**  The
  values arrive in solution order, and solution order is a function of how the facts
  were stored rather than of what they say — so `(+ 0.1 0.2 1e16 -1e16)` and the same
  four values reached in another order give different answers, and asserting the same
  KB in another order would change what the aggregate reports.  Order independence is
  the engine's first invariant (docs/nmtms.md); sorting makes the summation order a
  function of the values alone, which is what restores it.  Exactness is not on offer
  and is not what is claimed — determinism is."
  [op xs]
  (let [xs (sort xs)]
    (case op
      :sum (reduce + xs)
      :min (reduce min xs)
      :max (reduce max xs)
      :avg (/ (double (reduce + xs)) (count xs)))))

(defn- reduce-measures
  "The reduction of a non-empty measure list, as a rendered measure.

  `:sum` and `:avg` are linear in the `[lo hi]` bounds, so they carry an
  over-approximation through honestly — an interval in gives an interval out, which
  `render-quantity` says out loud rather than picking a figure out of it.  `:min` and
  `:max` need a **total** order and measure bounds only give a partial one, so they
  answer for point measures (where `lo = hi`) and refuse a genuine interval rather
  than guessing which of two overlapping ranges is the smaller.

  Each side is summed in sorted order, for the reason `reduce-numbers` gives: a
  normalized bound is a double, and a sum whose value depended on solution order would
  depend on the order the facts arrived in."
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
  "The value an aggregate reduces to over `values`, or nil when there is none.

  The empty extent is where the five differ, and deliberately: **count is 0 and sum is
  0** — the identity of each reduction, and a true answer about an empty group —
  while **min, max and avg over nothing have no answer at all** and yield no binding.
  A zero minimum would be a claim about a group that has no members, and an average
  over nothing is a division by zero however it is dressed up.

  A non-numeric value under `sum` / `min` / `max` / `avg` is an **error, not a silent
  skip**: a count of names is meaningful, an average of them is not, and quietly
  dropping the non-numbers would answer a different question than the one asked.  It
  is recorded in the violations ledger and yields nothing — `count` is unaffected,
  since counting is the one reduction that does not read the values."
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
  ;; The goal is one of the five, its reduction variable is a variable, and every
  ;; variable still free in it is one the census body **binds for itself**
  ;; (`sx/census-bound-vars`) — the reduction variable, and the join variables of a
  ;; conjunctive body.  A group variable an antecedent was meant to supply is substituted
  ;; away before the goal reaches here, so what is left is the body's own scope; a
  ;; variable the body cannot reach a witness for is a census of nothing, and this
  ;; declines it the way `UnknownProver` declines an open NAF goal.
  (applicable? [_ _ goal _]
    (and (sx/aggregate? goal)
         (some? (sx/aggregate-value-var goal))
         (let [bound (sx/census-bound-vars (sx/aggregate-body goal))]
           (every? bound (sx/free-vars goal)))))
  (est-bindings [_ _ _ _] 1)                    ; one answer or none, never a stream
  ;; the body must be *exhausted* before the first answer — a reduction has no partial
  ;; result — which is exactly what the `:compute` tier names.  Not `:lookup`: a
  ;; `{:max-cost :lookup}` budget must drop this prover, and does.
  (cost         [_ _ _ _] :compute)
  ;; Authoritative: an aggregate is not assertible, so nothing else can hold a claim
  ;; about one, and the answer is already a function of what the rest of the stack
  ;; derives.  Nothing may be unioned in.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [op     (sx/aggregate-functors (first goal))
          v      (sx/aggregate-value-var goal)
          values (aggregate-values kb goal v context)
          result (aggregate-value kb goal op values context)
          n      (second goal)]
      (cond
        (nil? result)      []
        (sx/variable? n)   [{n result}]
        ;; check mode: a bound `?n` is compared, numerically where both are numbers so
        ;; a long and a double that name one value agree
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

(defrecord BeliefProjectionProver []
  Prover
  ;; Claimed only for a **registered modal predicate** (`(modal_predicate P)` believed
  ;; where the query is asked — read scoped, like `abducible_predicate`), of **arity 2**,
  ;; whose **agent argument is ground** and yields a legal context name, over a
  ;; **sentence-shaped proposition**.  An unbound agent is excluded deliberately: it
  ;; would mean "search every agent's context", a different and far costlier operation
  ;; than a projection into one — `projectable-agent?` is the gate, and it refuses a
  ;; `?variable` because the minted context name would carry a `?` no context name may.
  (applicable? [_ kb goal context]
    (and (binary? goal)
         (tax/has-prop? (:taxonomy kb) :modal (nm/functor goal) context)
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
          inner (res/goal-normal-form kb (nth goal 2) actx)]
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
  ;; `P` arrives in the spelling the caller wrote: the read doors normalize the whole
  ;; goal, and this position is held opaque to that (`res/representative-term`), since
  ;; the asker's merges are not the agent's.  So the normalization owed it happens here,
  ;; against the **agent's** partition — which is the ordinary rule that the reader is
  ;; what elects (docs/equality.md), applied to the reader a projection actually has.
  ;; An identity the agent holds licenses the substitution inside their own belief, and
  ;; only for them.
  (solve [_ kb goal _context]
    (let [actx  (modal/context-of-agent (second goal))
          inner (res/goal-normal-form kb (nth goal 2) actx)]
      (solve-goal-with kb (registry kb) (sx/canon inner) actx))))

;; ---- type inference from arg-constrained usage -----------------------

(defn- believed-sentexes-with
  "The sentexes naming `term` that `context` **can see and does believe** — the term
  index read, filtered the way a retrieval is.

  The visibility half is `res/visible-supporter-fn`, which is belief, `genlCx`
  inheritance and the `except` roster in one memoized predicate, and which is **nil**
  for a nil or `?var` context — the unscoped read, where belief alone decides, exactly
  as it does everywhere else.  Scoping matters here because what is inferred from a
  usage is only as visible as the usage: a reader that cannot see `(eats Muffet Bone1)`
  must not learn from it that `Bone1` is food, or a sibling theory's facts type terms
  for a context that was never told them.

  Lazy, and it has to be: `inferred-types` streams this so a ground membership test
  stops at the first witness."
  [kb term context]
  (let [visible? (res/visible-supporter-fn kb context)
        live?    (or visible? #(jtms/in? (:tms kb) %))]
    (->> (reads/as-stored-with-term (:index kb) term)
         (keep #(p/get-sentex (:records kb) %))
         (filter #(live? (:id %))))))

(defn- inferred-types
  "Types an individual `x` must have because it fills an arg-constrained argument
  of a believed relation: for each believed `(P .. x@n ..)` with `(arg P n T')`,
  `x` is a `T'` and, by genl, every supertype of `T'`.  This is arg read the
  other way — as an inference, not only a constraint (e.g. Muffet eats Bone1 and eat's
  2nd argument is food, so Bone1 is food).

  **Whose declarations count is the reader `assert` uses** (`res/constraining-predicates`):
  `P`'s own, and those of the super-predicates the asking context can see, since a
  `(genl fatherOf parentOf)` edge makes every `fatherOf` tuple a `parentOf` tuple.  The
  two readings of one declaration must agree about that or a claim `assert` refuses for
  being ill-typed is one `ask` cannot type at all.

  **And the usage counts only where it can be seen.**  Both sides of the inference are
  read from the asking context — the declaration through `matches-visible`, the tuple
  through `believed-sentexes-with` — so a fact stated in a context the reader does not
  inherit from types nothing for it, exactly as that fact answers nothing for it.

  **Lazy and deduped.**  `distinct` over a lazy `for` returns a lazy, duplicate-free
  seq, so a *ground* `(Type x)` test (ArgTypeProver.solve's `some`) stops at the first
  believed sentex that witnesses the type it seeks, realizing the believed-sentex scan
  only that far — instead of computing x's whole type set.  The open `(?t x)` case
  consumes the whole seq, which enumerates every type exactly as the set did."
  [kb x context]
  (distinct
   (for [s (believed-sentexes-with kb x context)
         :let [sen (:sentence s) pred (nm/functor sen) as (vec (nm/args sen))]
         :when (and (symbol? pred) (seq as))
         ;; above `n`, since whose declarations bind a tuple is a fact about the
         ;; predicate and not about which of its positions is being read — bound
         ;; inside, the `genls` closure and its sort run once per argument position
         :let [ps (res/constraining-predicates kb 'arg pred context)]
         n (range 1 (inc (count as)))
         :when (= x (nth as (dec n)))
         p ps
         [_ b] (res/matches-visible kb (list 'arg p n '?t) context)
         :let [t' (get b '?t)]
         :when (symbol? t')
         super (tax/genls (:taxonomy kb) t' context)]
     super)))

(defrecord ArgTypeProver []
  Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 1 (count (rest goal)))
         (nm/individual? (second goal))))         ; (Type Individual), individual ground
  (est-bindings [_ _ _ _] 3)
  (cost         [_ _ _ _] :lookup)               ; lazy scan of the individual's believed sentexes — the ground test stops at the first witness
  (completeness [_ _ _ _] 50)                  ; augments stored type facts
  (solve [_ kb goal context]
    (let [[t x] goal, types (inferred-types kb x context)]
      (if (pvar? t)
        (map (fn [ty] {t ty}) types)
        ;; ground `(Type x)`: `some` short-circuits the lazy `inferred-types` at the
        ;; first sentex that witnesses `t`, so a ground membership never types x in full
        (if (some #(= t %) types) [{}] [])))))

;; ---- the argument-type meta-predicates, answered up genl ----------------
;;
;; `(arg petMammal 1 animal)` succeeds off a stored `(arg petMammal 1 mammal)`
;; when `(genl mammal animal)` — the same generalization `check` walks internally, so
;; `assert` and `ask` agree.  Answered HERE, a bounded closure walk, rather
;; than by declaring the meta-predicates `transitiveInArg`: that routes every one of the
;; KB's very many `arg`/`genlArg` lookups through the general preservation prover and
;; its chaining sweeps — a per-query tax the whole subsystem is gated to avoid, since
;; almost no predicate is preserved.  A stored `(transitiveInArg arg …)` breaks that
;; gate for the most-queried predicates there are.
;;
;; The predicate position reaches DOWN (a constraint on a super binds its
;; specializations — `constraining-predicates` is the super-predicate up-walk `check`
;; uses).  A type position's direction is its variance.  An *unconditional* type reaches
;; UP (a stored subtype constraint answers its supertypes — `genl?`): `arg`/`genlArg`
;; position 3 and `interArg`'s target position 5.  `interArg`'s *trigger* position
;; 3 is the antecedent of a conditional, so it is contravariant and reaches DOWN: a
;; stored `(interArg P n animal m U)` already convicts every `mammal`-trigger fact (a
;; mammal is an animal), so it answers the narrower `(interArg P n mammal m U)` but
;; never the wider `(… n thing m U)`, which would convict the non-animals `check` never
;; touches.  Getting the trigger backwards is both unsound (the widening) and incomplete
;; (the narrowing) against what `check` enforces — the same `assert`/`ask` agreement
;; is about.  On-demand and non-materializing, so it follows belief with no cache and
;; `sentexes-matching` still shows only what was stored.  `arity` is NOT here: a
;; sub-predicate may carry a signature of its own, and the answer would need the forward
;; `arity`⇒type cycle a backward prover cannot fire; `check`'s `inherited-arity` still
;; holds a silent sub-predicate to its supers.
(def ^:private meta-constraint-shape
  "By functor: the goal-list index of the predicate, the position-number indices that
  must match a stored declaration exactly, the type indices that reach UP `genl`
  (covariant — a stored subtype answers its supertypes) and those that reach DOWN
  (contravariant — a stored supertype answers its subtypes).  Only `interArg`'s
  trigger is contravariant; its target and the unconditional `arg`/`genlArg` type are
  covariant."
  '{arg      {:pred 1 :fixed [2] :types-up [3]}
    genlArg     {:pred 1 :fixed [2] :types-up [3]}
    interArg {:pred 1 :fixed [2 4] :types-up [5] :types-down [3]}})

(defn- meta-generalizes?
  "Does a stored declaration on `goal`'s predicate or a super-predicate answer `goal`
  once each type position is read the way its variance allows — covariant positions up
  the `genl` closure, the contravariant trigger down it?"
  [kb goal context]
  (when-let [{:keys [pred fixed types-up types-down]} (meta-constraint-shape (nm/functor goal))]
    (let [tax  (:taxonomy kb)
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

(defrecord MetaConstraintProver []   ; (arg/genlArg/interArg P n T …) up the genl closure
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
  "Rules concluding the goal's predicate **or a spec of it**, restricted to the
  backward-capable ones — the consequent index is complete, so it also holds
  forward-only and inert rules.  A rule concluding a subtype answers a supertype goal
  (`res/concluding-rule-handles` intersects `specs` with the consequent index), and
  `subsuming-unify` binds the goal variable to the subtype instance.

  Each carries its `exceptWhen` guard (`parse-rule`), so a rule that would conclude
  the goal but whose exception holds is discarded *after* the argument is built —
  matching what forward chaining does before placing the conclusion.

  A rule the asking context cannot see is not a candidate (`res/rule-visible-from?`):
  a rule is a sentex, inherited by the ordinary `genlCx` up-cone like everything
  else.  Nor is a rule the KB no longer believes (`res/rule-believed?`) — the
  consequent index posts on storage, so belief is asked of the record here exactly as
  forward chaining asks it of a trigger.  Nor is one a believed visibility `except`
  hides from the asking context (`res/hidden-fn`): forward chaining sweeps the
  conclusions of a hidden rule, and a backward pass that rebuilt them through the
  same rule would answer from knowledge the context deliberately removed.  The
  predicate is built once per goal and is nil for the almost-every-KB that hides
  nothing, so the common path pays one deref.

  **In content order**, `[sentence context]` under `nm/compare-form`.  The index answers
  in handle-set order, which is assertion order, and two consumers *truncate* on this
  list: `prove-within`'s `:max-results` stops the DFS partway through the rules it would
  have expanded, and the node engine's frontier is filled from `children`, which walks it.
  So without an order here the same knowledge in two arrival orders answers a capped query
  with two different answer sets — order independence, broken by the one thing that is
  never allowed to break it (docs/nmtms.md).

  The key needs no memo, which is why there is none: the sentence **is** the key, already
  a field on the record, and `compare-form` walks two forms in place rather than printing
  either.  So the sort builds one two-element vector per candidate and allocates nothing
  else — against a `print-key` per rule, which would be a String per candidate per
  comparison were it not decorated first.  `:context` joins it because one sentence stated
  in two contexts is two rules, and a key that could not tell them apart would drop the
  tie back onto the handle."
  [kb goal context]
  (when (sequential? goal)
    (let [hidden? (res/hidden-fn kb context)]
      (->> (res/concluding-rule-handles kb (first goal) context)
           (map #(p/get-sentex (:records kb) %))
           (filter rules/backward-sentex?)
           (filter #(res/rule-believed? kb (:id %)))
           (filter #(res/rule-visible-from? kb context (:context %)))
           (remove #(and hidden? (hidden? (:id %))))
           (nm/sort-by-content-key (juxt :sentence :context))
           (map #(parse-rule kb % context))))))

;; ---- the engine ---------------------------------------------------------

(def default-provers
  [(->TransitivityProver) (->DisjointnessProver)
   (->TransitivePredicateProver) (->TransitiveInArgProver) (->SymmetricProver) (->InverseProver) (->ReflexiveProver)
   (->EvaluableProver) (->DifferentProver) (->EvaluateProver) (->QuantityProver)
   (->UnknownProver) (->ThereExistsProver) (->ForallProver) (->ClosedExtentProver)
   (->DefnSufficientProver) (->DefnNecessaryNegationProver)
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

;; ---- which provers are even worth asking ---------------------------------

(defn applicable-provers
  "The applicable provers for `goal`, in registry order.

  One function rather than three copies of the same `filterv`: `solve-goal-with`
  decides what runs, `est-goal` decides whether a complete estimate exists, and `plan`
  reports both — so a sweep that drifted between them would make the diagnostic lie
  about the dispatch it is there to explain."
  [kb provers goal context]
  (filterv #(applicable? % kb goal context) provers))

;; Membership tests for the lookup-to-query stack (vaelii.impl.levels), which runs
;; the engine over a *subset* of the registry: level 5 with the transitive provers
;; alone, level 6 with everything except backward chaining.  Knowing which record is
;; which belongs here, next to the records.

(defn transitive-prover?
  "Does this prover compute a transitive closure — genl/genlCx through the cached
  taxonomy, or a predicate declared `(transitive P)`?"
  [pr] (or (instance? TransitivityProver pr) (instance? TransitivePredicateProver pr)))

(defn fact-prover?
  "Is this *the* stored-fact prover — the one that answers by matching the store, and
  whose answers therefore each name a sentex with a context?

  `vaelii.impl.vantage` asks it of every applicable prover to decide whether a literal is
  inside post-hoc placement's domain.  A goal only this one answers is a goal every answer
  to which can be placed, because every answer came from somewhere; a goal any *other*
  prover also answers has answers computed rather than stored — a closure walk, an
  evaluable, an inferred argument type — and those name no context to place by."
  [pr] (instance? FactProver pr))

;; ---- which registered provers can say what their answer rests on ---------

(def ^:private registry-support
  "`[registry-vector {:answers #{functor} :sources #{functor}}]`, memoized against the
  registry's **identity**.

  A volatile pair rather than a map, for `qcn-kb/registered-calculi`'s reason: the
  overwhelmingly common registry is the `default-provers` vector itself, so one entry
  answers every KB that registered nothing *and* every stretch of writing on one that
  did.  A `swap!` on the registry produces a new value, so it simply misses and
  recomputes; last write wins and the pair is written as one value, so a lost race costs a
  recomputation and cannot answer wrongly."
  (volatile! nil))

(defn- support-summary
  "The registered `SupportingProver`s' functors, as `{:answers … :sources …}`: what they
  answer with support, and what they read to do it.

  A miss is an `instance?`-free `satisfies?` scan of the registry plus two set unions; a
  hit is a deref and an identity compare.  Empty on both keys for the shipped registry
  minus nothing — `QuantityProver` is in `default-provers`, so the answers set is the
  measure comparisons even for a KB that registered no prover of its own."
  [kb]
  (let [pv (registry kb)
        [reg answer] @registry-support]
    (if (identical? pv reg)
      answer
      (let [ps (filterv #(satisfies? SupportingProver %) pv)
            v  {:answers (into #{} (mapcat support-functors) ps)
                :sources (into #{} (mapcat support-sources) ps)}]
        (vreset! registry-support [pv v])
        v))))

(defn support-answered-preds
  "The functors a registered `SupportingProver` answers — the antecedents forward chaining
  discharges through `solve-goal-with-support` so the firing carries what the answer rested
  on."
  [kb]
  (:answers (support-summary kb)))

(defn support-source-preds
  "The functors a registered `SupportingProver` *reads*.  A datum on one of these moves an
  answer no antecedent of the rule names, so it re-joins the rules carrying a
  `support-answered-preds` antecedent (`chain/fire-rules-for`) rather than triggering them
  — which is what makes such a firing independent of whether the table or the facts
  arrived first."
  [kb]
  (:sources (support-summary kb)))

(defn source-contexts
  "Every context worth answering a support-carrying goal at, given `preds` — the contexts
  holding one of those facts, and the contexts where two or more of them meet
  (`tax/meet-closure`).

  A caller passes the whole registry's sources (`support-source-preds`) rather than one
  prover's, which over-approximates in the harmless direction: a context that holds only
  some *other* prover's source reads nothing here and answers nothing, and the one read is
  shared across every computed antecedent of a run.

  `qcn-kb/reader-contexts` written for a prover that is not a calculus, and the same
  argument holds it: a reading is what a **reader** sees, and a reader sees the whole
  `genlCx` cone above it — so a context inheriting two contexts closes a metric network
  neither closes alone, and that entailment exists for no other reader.  Answering the
  goal at a *wildcard* context instead would read every context's facts into one reading,
  which is not any reader's, and would license a firing on facts no context sees together.

  The contexts are read from the store rather than from belief, which over-approximates in
  the safe direction: a context whose only such fact is defeated is enumerated, reads
  nothing, and answers nothing.

  **Resident** on the KB's `:qcn` atom, stamped with the change clock, since collecting
  them is a record fetch per stored fact of every predicate named."
  [kb preds]
  (observe/cached
   (:qcn kb) [::source-contexts preds]
   (fn [_stale]
     (let [held (into #{}
                      (comp (mapcat (fn [pred] (reads/as-stored-with-functor (:index kb) pred)))
                            (keep (fn [h] (:context (p/get-sentex (:records kb) h)))))
                      preds)]
       (tax/meet-closure (:taxonomy kb) held)))))

(defn- goal-cost-rank [pr kb goal context] (cost-rank (cost pr kb goal context)))

(defn- dispatch-provers
  "The prover dispatch itself, with `run` saying what one prover's answers look like:
  raw bindings for `solve-goal-with`, `[bindings support]` pairs for
  `solve-goal-with-support`.

  One function rather than two copies, for `applicable-provers`' reason — the two must
  agree about *which* prover answers a goal, and a copied dispatch is two things to keep
  agreeing.  What differs between the callers is only the shape of an answer, which is
  exactly what `run` carries."
  [kb provers goal context run]
  (let [applicable (applicable-provers kb provers goal context)
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

  Lazy: provers are ordered by `cost` tier and expanded one at a time, so the
  cheapest first-answer prover is consulted first and an expensive one is never
  invoked at all if the consumer stops early.  (The complete-prover branch runs one
  prover, so its laziness is whatever that prover returns.)

  When several *complete* provers apply — rare, since the complete provers claim
  pairwise-disjoint goal shapes — the one with the fewest `est-bindings` runs, a
  real count rather than a constant.

  `res/lazy-mapcat`, not `mapcat`: the ordinary one would realize a whole chunk of
  the prover list and so call *every* applicable prover's `solve` before yielding
  the first solution — which is precisely the cost the cheapest-first ordering is
  there to avoid."
  [kb provers goal context]
  (dispatch-provers kb provers goal context #(solve % kb goal context)))

(defn solve-goal
  "Raw solution bindings for `goal` in `context` via the applicable provers."
  [kb goal context]
  (solve-goal-with kb (registry kb) goal context))

(defn- answers-with-support
  "One prover's answers as `[bindings support]` pairs: its own support when it implements
  `SupportingProver`, and an **empty** support otherwise.

  Empty is the honest answer for a prover that reads nothing stored — `EvaluableProver`
  compares two numbers, `EvaluateProver` computes one — and the seam's contract is what
  makes it honest rather than merely convenient: a prover whose answer *does* move with
  the store implements the protocol, so a prover that does not implement it is one whose
  answer no retraction can invalidate."
  [pr kb goal context]
  (if (satisfies? SupportingProver pr)
    (solve-with-support pr kb goal context)
    (map (fn [b] [b #{}]) (solve pr kb goal context))))

(defn solve-goal-with-support
  "`solve-goal`'s support-carrying twin: each solution as `[bindings support]`, where
  `support` is the handles of the stored sentexes the answer was read from
  (`SupportingProver`), empty for a prover that reads nothing stored.

  Forward chaining is the caller.  A backward chainer discharges an antecedent and forgets
  it; a forward firing *stores* a conclusion, and what it stored has to be withdrawable —
  so the join needs the handles the answer rested on, and needs them beside the bindings
  they came with rather than by asking a second time (a second read is a second moment,
  and the two could disagree).

  Same dispatch as `solve-goal`, so the two agree about which prover answers: the sole
  complete prover when there is one, else the applicable provers cheapest-first, lazily,
  deduped.  Deduped on the **pair**, so one binding reached by two provers with different
  support survives as both — two routes to one conclusion are two justifications, which is
  what the TMS already reads them as."
  [kb goal context]
  (dispatch-provers kb (registry kb) goal context #(answers-with-support % kb goal context)))

(def ^:private ^:dynamic *mirror-depth*
  "How many mirror delegations are on the stack.  `solve-mirrored` re-enters the
  registry, and the mirror of a mirror is the original goal — so unbounded delegation
  is a loop, and a mutual `symmetric` + `inverse` pair could ping between the two
  delegates the same way.  Two levels admit every one-mirror-plus-one-partner
  composition; past the bound the mirror falls back to the raw stored read, which is
  the whole of what it answered before it delegated at all."
  0)

(defn- solve-mirrored
  "Solutions for the mirrored spelling of the symmetric `(pred a b)` — `(pred b a)`
  through the engine minus this prover, so the mirror composes with facts, the
  closures, preservation and the partner spellings rather than reading storage alone.
  The mirror of an *inherited* claim is the case that needs it: nothing is stored, and
  a raw read answers nothing for a claim `verdict` proves."
  [kb pred a b context]
  (if (< *mirror-depth* 2)
    (binding [*mirror-depth* (inc *mirror-depth*)]
      (let [pv (remove #(instance? SymmetricProver %) (registry kb))]
        ;; realized inside the binding: the depth guard is dynamic, and a lazy answer
        ;; escaping the scope would re-enter at depth zero — the loop this bounds
        (doall (solve-goal-with kb pv (list pred b a) context))))
    (map second (res/matches-visible kb (list pred b a) context))))

(defn- solve-inverted
  "Solutions for the inverted spelling of `(pred a b)` — the partner predicate with
  the arguments swapped — through the engine over a restricted prover list:

  * minus `InverseProver`, so a mutual `(inverse P Q)` + `(inverse Q P)` declaration
    cannot re-enter P-via-Q-via-P;
  Rules concluding the partner predicate are reached when a backward search expands
  them; what the delegation buys is composition with the *other* metadata provers
  (transitive, symmetric, reflexive) and facts.

  **Every declared partner of the predicate or a sub-predicate of it, not one.**
  Nothing refuses a second `(inverse P R)` beside a standing `(inverse P Q)`, and
  answering off whichever the taxonomy happened to hold would make a goal's answer a
  function of declaration order — so each partner is asked and the solutions are
  unioned, deduped like any other multi-prover union.  A partner of a *sub-predicate*
  is in the set for the subsumption reason `inverses-under` states: its spelling holds
  sub-predicate tuples, and those answer the super-predicate's goal."
  [kb pred a b context]
  (let [qs (tax/inverses-under (:taxonomy kb) pred context)
        pv (remove #(instance? InverseProver %) (registry kb))]
    (->> qs
         (sort)                                  ; content-keyed, so the order is stable
         (res/lazy-mapcat #(solve-goal-with kb pv (list % b a) context))
         distinct)))

(defn est-goal
  "How many bindings the registry expects to produce for `goal`, or **nil** when it
  has no authoritative answer.

  Only a *complete* prover's estimate is returned, and deliberately so.  This mirrors
  `solve-goal-with`: when a complete prover exists the engine runs it *alone*, so its
  estimate is the whole cost of the goal.  When none does, the engine unions partial
  provers over the index, and their estimates are guesses about a fan-out the index
  models better — so nil, and `vaelii.impl.plan` uses its own count-aware model
  instead.  Returning a partial prover's number here would replace a measurement with
  a constant (`ArgTypeProver` answers 3 for everything)."
  [kb goal context]
  (let [applicable (applicable-provers kb (registry kb) goal context)]
    (when-let [complete (sole-prover kb applicable goal context)]
      (est-bindings complete kb goal context))))

(defn registry-est-override
  "`est-goal` as the `:est-override` a backward chainer plans with (`res/prove-from`,
  `res/initial-prove-stack`) — for an executor whose **leaf is the registry**, and only
  such an executor.

  The index is the wrong cost model for that leaf: a `genl` conjunct is answered from the
  cached closure, so what it costs is the closure's size, not the handful of stored edges
  the trie can count — and the index model would rank the literal that fans out over a
  whole type hierarchy as the *cheapest* in the conjunction.  A chainer whose leaf is the
  stored facts passes nothing here, because for that leaf the index model is right.

  Memoized on the goal, which is sound in both directions: `est-goal` reads only the
  goal (kb and context are fixed for the run, and its `bound` argument is ignored — a
  complete prover's estimate is the whole cost of the goal, not of a partial binding),
  and a query mutates nothing that could make an entry stale.  Without the memo
  `plan/order` re-estimates every remaining literal on every pick, so a k-antecedent
  rule pays a full registry `applicable?` sweep plus a candidate-rule re-parse O(k²)
  times."
  [kb context]
  (let [est (memoize (fn [goal] (est-goal kb goal context)))]
    (fn [goal _bound] (est goal))))

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

(defn- condition-normalizer
  "A `ground-goal -> ground-goal` rewriting a block condition's substituted conjunct to
  the normal form `context` answers under — every symbol to the representative that
  context elects, then the schematic equations it can see — or nil when the KB holds no
  merge and no equation and there is nothing to rewrite.
  `vaelii.impl.levels/engine-goal` does this for a level-6 read and `kb/rewrite-goal`
  for a query; a block condition is the same question and takes the same preparation.

  Both halves of the condition need it, and for the same reason.  The **bindings** a
  firing substitutes in are what it matched when it fired, and a merge does not go back
  and edit a justification — so a firing that bound `?c` to `C3` still says `C3` after
  `(sameAs C2 C3)` has retired that spelling, and the conjunct asks about a term the KB
  no longer answers under.  The conjunct's **own constants** are stored as the rule was
  written, and a rule is held back from an individual-only rewrite migration, so
  `(exceptWhen (mskip MOne) …)` keeps naming `MOne` after the merge.  Either way what
  comes back is the honest empty that reads as *not excepted* and *not derivable* — the
  loudest way this can go wrong, since an unanswerable exception does not hold and the
  rule fires, and an `unknown` about a term with an answer under its representative
  reports absent.

  Scoped to `context`, the scoping every other class read takes: a merge that context
  cannot see must not rename what its own condition asks about.  One predicate for the
  whole conjunction, since deciding visibility costs a record fetch per equality
  supporter.  `different` is exempt exactly as it is in `kb/rewrite-goal` — mapping its
  arguments onto one representative is the question it exists to answer, and the prover
  normalizes them itself."
  [kb context]
  (let [tx (:taxonomy kb)]
    (when-not (and (nil? (tax/merged-term-pred tx)) (empty? (tax/rewrite-rules tx)))
      (let [visible? (res/visible-supporter-fn kb context)
            rules    (cond->> (tax/rewrite-rules tx)
                       visible? (filterv #(visible? (:handle %))))]
        (fn [goal]
          (if (and (sequential? goal) (= 'different (nm/functor goal)))
            goal
            (rewrite/normalize-sentence rules (res/representative-term kb visible? goal))))))))

(defn exception-holds?
  "Does `except` — a rule's `exceptWhen` query, a vector of literals — hold under
  `bindings`, evaluated in `context`?

  Three properties make this cheap, and each is load-bearing:

  * **Closed.**  Every exception variable is bound by an antecedent (enforced in the
    `sentex` constructor), so substitution leaves a *ground* question and the conjuncts
    share nothing.  They are still run through `conjunction-solutions`, the joined
    evaluator an `unknown`'s query takes: on a ground conjunction a join *is* the
    independent existence check, and one evaluator is what keeps the two from drifting.
  * **One answer suffices.**  `conjunction-solutions` is lazy throughout, so `take 1`
    stops the query at its first result instead of enumerating an extent.
  * **No backchaining.**  Nothing in the registry expands a rule, so an exception can
    reach through genl specificity, the genlCx closure, the transitive / symmetric
    / inverse metadata, disjointness and the evaluables — but never invokes an unbounded
    proof search from inside the relabel loop.

  **An unanswerable exception does not hold**, and the rule fires.  That is the
  open-world reading, and it matches `arg`, where an argument whose type is unknown
  cannot violate a constraint: blocking on \"cannot tell\" would let a missing fact
  silently suppress knowledge.  An empty or absent exception never holds, so an ordinary
  rule pays nothing here.  See docs/exceptions.md."
  [kb except bindings context]
  (conjunction-derivable? kb except bindings context (condition-normalizer kb context)))

(defn rule-exceptions
  "The exceptWhen exceptions currently in force for the rule at `handle` — a seq of
  **conjunctions** (each a vector of literals), evaluated block-if-**any**-holds.

  An exception is a separate belief-following meta-sentex `(exceptWhen Q (sentexHandle
  handle))`: the rule and its exceptions are distinct assertions, so a rule and its
  unexcepted twin share one handle and asserting or retracting an exception amends the
  rule in place.  Each such meta-sentex contributes one conjunction; multiple ones are
  independent \"unless\" clauses (birds fly unless penguins, unless ostriches — block
  if either holds), while the conjuncts *within* one exception all must hold.  The
  query is stored in the rule's canonical variable names (aligned when the exception
  was asserted), so a firing's bindings substitute straight in.

  Believed only: a defeated or retracted `exceptWhen` stops blocking, exactly as a
  cached relation follows belief.  Gated on the exception-rule roster by the callers,
  so an ordinary rule never reaches the term-index lookup."
  [kb handle]
  (into []
        (comp (map #(p/get-sentex (:records kb) %))
              (filter some?)
              (filter #(sx/exceptWhen-meta? (:sentence %)))
              (filter #(= handle (sx/exceptWhen-rule-handle (:sentence %))))
              (filter #(jtms/in? (:tms kb) (:id %)))
              (map #(sx/exception-query-conjuncts (:sentence %))))
        (reads/as-stored-with-term (:index kb) (sx/sentex-handle handle))))

(defn exceptions-block?
  "Is a firing of rule `handle` blocked by any of its exceptWhen exceptions under
  `bindings`, evaluated in `context`?  Block-if-**any**-conjunction-holds.  An ordinary
  rule (no exception) yields no conjunctions and pays nothing past the roster gate."
  [kb handle bindings context]
  (boolean (some #(exception-holds? kb % bindings context) (rule-exceptions kb handle))))

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
    (when (and h (reads/watched-rule? (:index kb) h) (seq (rule-exceptions kb h)))
      (fn [bindings] (not (exceptions-block? kb h bindings context))))))

(defn parse-rule
  "A rule sentex as the chainers' parsed map — antecedents, consequent, the `exceptWhen`
  guard if it has one, and the rule's own `:handle`, which is what an executor
  accumulating supports records (`vaelii.impl.inference`)."
  [kb rule-sentex context]
  (assoc (rules/parse (:sentence rule-sentex))
         :guard  (rule-guard kb rule-sentex context)
         :handle (:id rule-sentex)))

(defn- goal-vars [goal] (set (filter pvar? (tree-seq sequential? seq goal))))

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
                                      {:type :unknown-option :max-cost max-cost
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
  A goal answerable only by a dropped tier yields nothing — the honest effect of the
  qualitative bound.  Lazy, for `vaelii.core/ask-within` to `budget/collect`."
  [kb goal context max-cost]
  (project goal (solve-goal-with kb (cost-capped-provers kb goal context max-cost) goal context)))

(defn plan
  "The applicable provers for a goal, their estimates, and — the part a reader
  debugging a missing answer needs first — **which of them actually run**.

  Applicable is not the same as consulted.  When one prover may answer the goal alone
  every other applicable prover is *shadowed*: reported, never invoked, contributing
  nothing.  A plan that listed them without saying so reads as a union that is not
  happening.  So each entry carries `:runs?`, and a shadowed one carries
  `:shadowed-by` naming the prover that displaced it.

  The converse case is reported too, and from outside it is the one that looks like a
  bug.  A prover can claim `completeness` 100 and still not run alone, because a source
  none of the applicable provers reads bears on this goal — so every claimant runs in
  the union instead.  Those entries carry `:guarded-by` naming the channels
  (`shadowing-channels`), which is the difference between *the union is happening* and
  *the union is happening for this reason*.

  Entries are in the order the engine would consult them: a single complete prover,
  else cheapest `cost` tier first."
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

(caches/register-cache
 {:cache    :closure-answers
  :label    "Closure answers"
  :scope    :kb
  :unit     "closures"
  :limit    (fn [] *closure-answer-limit*)
  :counters nil
  :note     (str "One declared-transitive predicate's reach from one node, in one "
                 "direction, seen from one context — the answer an open-argument ask "
                 "computes. The whole map carries one change clock, so any mutation "
                 "(a relabel included, which is what makes it follow belief) retires "
                 "every entry at once. Bounded by total MEMBERS rather than entries, "
                 "since an entry is a whole reach set: a reach larger than the bound is "
                 "never stored, and a total that reaches it drops the map wholesale.")
  :read     (fn [kb] {:entries (some-> (:closures kb) deref :entries count)})
  :clear    (fn [kb] (let [a (:closures kb)
                           n (if a (count (:entries @a)) 0)]
                       (some-> a (reset! {}))
                       n))})
