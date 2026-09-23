;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.assert-cost-test
  "What one assert costs the index, as **counted operations** — the gate for the class of
  regression `lein perf` is structurally blind to.

  `bench/vaelii/bench/perf.clj` asserts a ratio and never a millisecond, which is what
  makes it survive a loaded laptop.  The price of that is stated in its own preamble: **a
  ratio cannot see a constant.**  An unconditional read added to the assert path moves the
  reading at both sizes by the same amount and divides out, so every one of its checks
  passes untouched.  One regression has already shipped through that gap —
  `inter-args-problem` ran its `interArg` declaration retrieval unconditionally, on
  every assert of every KB, and nothing declares `interArg` — ~11% per assert of a
  declaration-carrying predicate.  It was found by hand, against a worktree at the
  parent commit.

  This gate closes that gap from the other side.  It runs seventeen fixed workloads with
  `vaelii.impl.profile` collecting and pins the **exact** index-operation counts each one
  costs: every `IndexStore` read by family, every `index-sentex` batch op by family, and
  every `unindex-sentex!` batch op by family.  Twelve of the seventeen assert and five retract,
  so a constant added to either write path lands here.

  **Eight of the twelve write a fact and four write the vocabulary**, which is the split to
  read the assert half by.  A definitional check that grows costs a fact nothing and a
  `genl` edge or an `(arity P n)` everything: the arity descension runs its walk when a
  binding arrives, and the retroactive report is triggered by a binding and never by a
  fact.  `:taxonomy-edge` and `:arity-declaration` are the two that price that path.

  ## Why a count and not a duration

  The quantity is an integer the engine computes, not a measurement of the machine, so
  there is no warm-up, no tail mean, no noise floor and no tolerance.  It is bit-identical
  across runs, across machines and across a loaded box — which is the standing complaint
  against the ratio gate and the reason this one can live in the suite rather than behind
  a command somebody has to remember.  It costs a few seconds.

  It is also *more sensitive than a duration in the region that matters*.  The regression
  above is one read against the plain workload's twenty-five per assert — 4% of its total
  reads, which no wall-clock gate would separate from noise — and 20% of the five
  `:argument-root` reads it lands beside, which this one fails on.  Counting per family
  is what buys that: a constant hides in a total and stands out in the family it lands
  on.

  ## Why exact, and not a ceiling

  A ceiling would let a change spend anything already budgeted, and the budget is not a
  design target — it is a record of what the engine does today.  Exact equality means any
  movement, in either direction, is a diff somebody has to look at and either explain or
  fix, and the number that lands beside the explanation is the change's own cost.  That is
  the whole product: an index change proposing a new family becomes a line saying how many
  operations per assert it added.

  So a legitimate optimization **fails this gate**, and that is correct.  Re-pin the
  number, and the commit that does so carries the improvement as data.

  ## What it does not catch

  - **Work that is not an index operation.**  Computation, allocation, a record-store
    read, a taxonomy walk.  The counted calls are `IndexStore`'s, so a constant added between two
    of them is invisible here.
  - **A more expensive version of the same operation.**  One `sentexes-with-arg` counts
    once whether it returns four handles or four million.  `lein perf`'s
    `intersect-selectivity` is the check that holds *that*, and this gate does not
    subsume it.
  - **A retraction cost read as a per-retraction constant.**  `unindex-sentex!` reports
    what it cost (`:retracts`, docs/profile.md), so a teardown is budgeted the same way —
    except `:dead`, the trie nodes a removal emptied, which is decided by what else is
    still stored under the same prefix rather than by the sentex.  It is exact for a
    fixed corpus torn down in a fixed order, which is what a workload is, and it is not a
    figure another corpus reproduces.  So a moved `:dead` is read against the workload
    that produced it: change `n` or the structure of the facts and it moves for that reason
    alone, where every other family scales with `n`.
  - **A durable index.**  Every workload runs twice, on `:memory` and on
    `:memory-columnar` — the KV index and the columnar trie — and one budget holds both:
    the columnar store tallies its trie families under `KvIndexStore`'s labels and
    delegates the other families to an embedded `KvIndexStore`.  `:fan`, the node-probe
    count only `KvIndexStore`'s walk keeps, is in no budget.  The durable backends are not
    run: the KB is pinned rather than inherited from `scripts/test-backends.sh`, so the
    gate says the same thing on all eight backend runs rather than eight different things.
  - **A configuration other than the shipped one.**  `with-shipped-retrieval` pins every
    switch that decides which family answers a read (`tu/shipped-defaults`), so the
    budgets are a claim about the defaults and about nothing else.  The reference retrieval path
    (`VAELII_HIER=0`) really does cost differently — two reads per sentex off
    `:argument-root` and onto `:trie-lookup` — and it carries no budget here.
  - **Anything that scales.**  A cost that grows with the KB is `lein perf`'s subject and
    it is a ratio for good reason.  The two gates are complements: that one holds the
    *shape*, this one holds the *constant*, and neither sees the other's regressions."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

;; The instrument is process-wide, so a test that threw while collecting would hand the
;; next namespace a running tally.
(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(def ^:private n
  "Operations per workload — asserts in the twelve assert workloads, retractions in the five
  teardowns.  Large enough that a per-operation constant lands as a three-digit difference
  rather than a rounding one, small enough that seventeen workloads are a few seconds."
  100)

(def ^:private ^:dynamic *index*
  "The in-RAM index representation a workload runs on — `:memory` or `:memory-columnar`."
  :memory)

(defn- cost-space
  "The KB every workload runs on: in-RAM, its own space, the reference TMS.

  Pinned rather than inherited, and each half has its own reason.  The **backend**,
  because a budget is exact and the two in-RAM index representations are the ones it is
  held on (`*index*`).  The **TMS**, because a budget is a claim about one configuration and
  `VAELII_TEST_TMS=dense` is a different one.  Derived from `tu/plain-memory-space` so it
  follows `VAELII_TEST_SPACE` when a parallel run moves the block, with one more segment
  per index so it shares a store with nothing."
  []
  (-> tu/plain-memory-space
      (update :space conj ::cost *index*)
      (assoc :backend *index* :tms :reference)))

(defn- fresh []
  ;; through `tu/clear-kb!` rather than the two protocol calls it wraps, so a wipe here
  ;; is the wipe every other suite takes and cannot drift from it
  (doto (v/open-kb (cost-space)) (tu/clear-kb!)))

(defn- ind [prefix i] (symbol (str prefix i)))

;; ---- the workloads -------------------------------------------------------
;;
;; Each returns a **thunk**, and the split is the whole reason the counts are stable:
;; everything the workload needs in place — the KB, its taxonomy, its declarations, its
;; rule — is built by the time the thunk is called, so `measure` starts the instrument
;; over the asserts being priced and nothing else.  Building the KB inside would count
;; `open-kb`'s coverage-gate read, which is one op and differs on the first call in a
;; process.

(defn- plain
  "A binary fact of fresh individuals: no declaration, no membership, no rule.  The floor,
  and the workload the shipped `interArg` regression is clearest on, because a KB with
  nothing to check should be paying for nothing."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acPlain (ind "AcA" i) (ind "AcB" i)) 'CxPerf {})))))

(defn- membership
  "A type membership into a declared taxonomy — the arriving fact `settle` does real work
  for, since the disjointness arm reads the term's own argument-1 root."
  []
  (let [kb (fresh)]
    (v/assert kb '(genl acm_t thing) 'CxPerf {:strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acm_t (ind "AcM" i)) 'CxPerf {})))))

(defn- deep-membership
  "The `membership` workload with eight predicates stacked above it instead of one, and
  the only budget here that is a claim about a **shape** rather than a constant.

  `inherited-arity` asks the `variable_arity` release of every super-predicate, and that
  question is a membership retrieval the arity table cannot answer.  So the cost of
  asserting one type membership is proportional to how deep in the hierarchy its
  predicate sits — which the `membership` workload one screen up cannot see, because at
  depth 1 a per-super cost and a constant are the same number.  Two budgets at two depths
  are what separate them: this one should exceed `membership` by seven supers' worth of
  reads and by nothing else, and if some later change makes the descension flat in the
  depth, this is the budget that moves and `membership` is the one that does not.

  None of the eight declares an arity, which is the case the walk runs to the end on.  A
  predicate declaring either spelling is answered by `own-arity` before the walk starts."
  []
  (let [kb (fresh)
        t  (fn [i] (symbol (str "acdm_t" i)))]
    (v/assert kb (list 'genl (t 8) 'thing) 'CxPerf {:strength :monotonic})
    (dotimes [i 8]
      (v/assert kb (list 'genl (t i) (t (inc i))) 'CxPerf {:strength :monotonic}))
    (fn [] (dotimes [i n]
             (v/assert kb (list (t 0) (ind "AcDM" i)) 'CxPerf {})))))

(defn- declared
  "A fact of a predicate carrying an `arg` declaration at both positions, over
  individuals that already hold the type.  **The historical regression's form**: the
  argument-constraint checks are the reads `assert` names as its dominant per-fact cost,
  so a fourth declaration kind read unconditionally lands here first."
  []
  (let [kb (fresh)]
    (v/assert kb '(genl acd_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(arg acDecl 1 acd_t) 'CxPerf {:strength :monotonic})
    (v/assert kb '(arg acDecl 2 acd_t) 'CxPerf {:strength :monotonic})
    (dotimes [i n] (v/assert kb (list 'acd_t (ind "AcD" i)) 'CxPerf {}))
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acDecl (ind "AcD" i) (ind "AcD" i)) 'CxPerf {})))))

(defn- functional-in-arg-arity-2
  "A fact of a predicate carrying `(functionalInArg P 2)` — the shape 06ae8613 narrowed
  from an O(extent) `subtree-facts` sweep to the O(1) shared-determinant read `functional`
  already gets, by folding it into `settle/partner-contexts`' existing fun/asym/anti case
  instead of leaving it in the budgeted sweep beside the truly-empty (arity 1) and
  composite (arity > 2) shapes.

  **What `lein perf` cannot see here.**  b3bfb23b already caps the sweep at
  `*exposure-instance-budget*`, so a ratio between a small and a large extent reads flat
  whether an arity-2 assert pays the O(1) determinant read or the capped sweep — both are
  independent of extent past the cap.  Only the exact operation count tells the two apart:
  the narrow read costs `plain`'s own reads plus one `:argument-root` shared-determinant
  probe, where the sweep it replaced cost `subtree-facts` over the predicate's whole
  extent, batched into far more.  A regression that re-widens the `(not= 2 k)` guard moves
  this budget off `plain`'s neighborhood by exactly that."
  []
  (let [kb (fresh)]
    (v/assert kb '(functionalInArg acFnArg 2) 'CxPerf {:strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acFnArg (ind "AcFA" i) (ind "AcFV" i)) 'CxPerf {})))))

(defn- negative
  "A negative fact with no positive twin.  Its own workload because the `:false` node is a
  separate trie subtree and the polarity checks are a separate read path — a constant
  added to the negation arm shows up here and in none of the others."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'not (list 'acNeg (ind "AcN" i) 'AcNval)) 'CxPerf {})))))

(defn- compound
  "A fact carrying a compound argument, which is the write side of the structural trie and
  the term index at once: the compound linearizes into extra trie levels and its interior
  atoms each earn a term posting."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acCmp (ind "AcC" i) (list 'acFn (ind "AcC" i) 'AcUnit))
                       'CxPerf {})))))

(defn- rule-fired
  "A fact arriving through one forward rule, so each assert indexes **two** sentexes — the
  datum and the conclusion.  The derived half is where an index cost is easiest to add
  without noticing, since nothing a caller wrote is on that path."
  []
  (let [kb (fresh)]
    (v/assert kb (rules/rule-sentence ['(acSrc ?x ?y)] '(acDst ?x ?y))
              'CxPerf {:direction :forward :strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acSrc (ind "AcR" i) (ind "AcS" i)) 'CxPerf {})))))

(defn- taxonomy-edge
  "A `genl` edge under a predicate whose arity is declared — the vocabulary write, where
  the six above are all content writes.

  **The shape none of them reaches.**  Every other workload here builds its taxonomy during
  the *build* and asserts facts under it in the thunk, so a cost added to the edge write
  itself is priced nowhere: the retroactive arity report is triggered by a binding and a
  `genl` edge is one, the argument-type entailment draws what the predicates above the edge
  say about the facts below it, and the chaining path reads the subtree an edge newly makes
  matchable.  All three run per edge and none of them runs on a fact.

  Each edge is its own fresh sub-predicate under the one declared root, so the subtree
  beneath an arriving edge is the edge's own end of it and the count is a per-edge constant
  rather than a function of how many edges came first.  `lein perf`'s
  `arity-reach-under-subtree` holds the other shape — the same write over a subtree that
  grows — and the two are the usual complements: the shape there, the constant here."
  []
  (let [kb (fresh)]
    (v/assert kb '(binary_predicate acteRoot) 'CxPerf {:strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'genl (ind "acteSub" i) 'acteRoot)
                       'CxPerf {:strength :monotonic})))))

(def ^:private declaration-relatives
  "Predicates stacked above the one each `arity-declaration` names, none of them declaring
  a length.  Its own knob rather than `n`, because it is the quantity that workload's read
  budget is proportional to while `n` counts declarations — separating them is what lets a
  re-pin say which of the two moved.

  Four rather than one because the cost is per relative: at one relative a per-relative read
  and a constant are the same number, which is the trap `deep-membership` exists to keep
  `membership` out of."
  4)

(defn- arity-declaration
  "An `(arity P 2)` declaration over a predicate carrying `declaration-relatives`
  super-predicates.

  The entry point refuses a declaration that disagrees with what the predicates above or below it
  are declared with, so an arity arriving iterates `genls(P) ∪ specs(P)` and asks each
  relative for its own length.  The `(arity P n)` table answers that as a map read for a
  relative it names and says nothing about one it does not — and the second spelling, the
  predicate-type membership, is a retrieval.  So the cost is one retrieval per relative the
  table is silent about, which is a constant on the assert path and exactly the kind a
  ratio divides out.

  None of the four declares a length, which is the case the walk pays for in full.  A KB
  whose hierarchy is declared throughout pays the map read and stops, so this is the
  expensive end rather than the ordinary one — and the expensive end is what a budget is
  for."
  []
  (let [kb (fresh)
        s  (fn [i] (symbol (str "acadB" i)))]
    (dotimes [i (dec declaration-relatives)]
      (v/assert kb (list 'genl (s i) (s (inc i))) 'CxPerf {:strength :monotonic}))
    (dotimes [i n]
      (v/assert kb (list 'genl (ind "acadPred" i) (s 0)) 'CxPerf {:strength :monotonic}))
    (fn [] (dotimes [i n]
             (v/assert kb (list 'arity (ind "acadPred" i) 2) 'CxPerf {:strength :monotonic})))))

;; ---- the retraction workloads --------------------------------------------
;;
;; The same shape with one difference: the thunk **retracts**, and everything it retracts
;; was asserted during the build.  So the instrument covers the teardowns and none of the
;; asserts that set them up, exactly as the six above cover asserts and not the taxonomy
;; behind them.
;;
;; What a retraction costs is countable because `unindex-sentex!` reports it
;; (`:retracts`, docs/profile.md).  What it is **not** is quotable per retraction, and
;; `:dead` is why: how many trie nodes a removal empties is decided by what else is still
;; stored under the same prefix, so the number below is a property of *this corpus torn
;; down in this order* and not of a fact of this shape.  Every other family is decided by
;; the sentex and is indistinguishable from an assert budget.

(def ^:private nat-population
  "Reified NATs standing in the KB for the two NAT workloads.  Its own knob rather than
  `n`, because it is the quantity the bystander read budget is currently proportional to
  while `n` counts retractions — separating them is what lets a re-pin say which of the
  two moved."
  100)

(defn- plain-teardown
  "The `plain` workload's n facts, retracted in the order they arrived.  The floor for a
  teardown, and the one an unconditional read added to the retraction path is clearest
  on, for the reason `plain` is the clearest on the assert path: a KB with nothing to
  check should be paying for nothing."
  []
  (let [kb (fresh)
        hs (mapv (fn [i] (v/assert kb (list 'acPlain (ind "AcA" i) (ind "AcB" i))
                                   'CxPerf {}))
                 (range n))]
    (fn [] (doseq [h hs] (v/retract! kb h)))))

(defn- rule-derived-teardown
  "The `rule-fired` workload's n premises, retracted.  Each teardown unindexes **two**
  sentexes — the datum and the conclusion it solely supported — so this is the workload
  that prices the dependency-directed sweep's own removals rather than only the ones a
  caller asked for."
  []
  (let [kb (fresh)]
    (v/assert kb (rules/rule-sentence ['(acSrc ?x ?y)] '(acDst ?x ?y))
              'CxPerf {:direction :forward :strength :monotonic})
    (let [hs (mapv (fn [i] (v/assert kb (list 'acSrc (ind "AcR" i) (ind "AcS" i))
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(defn- nat-bystander-teardown
  "n plain facts retracted on a KB carrying `nat-population` **live** reified NATs that
  none of them names.

  A teardown runs the reified-NAT orphan collection, since a constant whose last use has
  just gone would leave its `termOfUnit` map dangling a raw `nat/` symbol
  (docs/nat.md).  Here it has nothing to collect at any point: every constant is named by
  its own `(acNatUse …)` fact and no retraction touches one, so the population is the same
  after the workload as before it and every read the sweep takes is a read that changed
  nothing.

  So its read budget is a reading of the sweep's **candidate set** rather than of the
  retraction, and it tracks `nat-population`.  A sweep whose candidates are the constants
  the retracted sentexes named prices out near `plain-teardown` and breaks this budget on
  the way, which is the gate doing its job: re-pin from the failure report, where the
  delta is what the narrowing bought."
  []
  (let [kb (fresh)]
    (v/assert kb '(reifiable_function AcNatFn) 'CxUniverse {:strength :monotonic})
    (dotimes [i nat-population]
      (v/assert kb (list 'acNatUse (ind "AcNU" i) (list 'AcNatFn (ind "AcNA" i)))
                'CxPerf {}))
    (let [hs (mapv (fn [i] (v/assert kb (list 'acBystand (ind "AcBy" i) 'AcByVal)
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(defn- nat-orphan-teardown
  "n facts retracted, each the **last use** of one reified NAT, so every teardown orphans
  a constant and unindexes its `termOfUnit` bookkeeping alongside the fact.

  The twin of `nat-bystander-teardown`, and the two fail for opposite reasons.  That one
  says the sweep must not read the population it is not about; this one says it must
  still collect the constant it *is* about — a narrowing that stops finding the orphan
  turns this workload's unindexed count from 2n into n, which is a correctness bug
  wearing a performance win's clothes."
  []
  (let [kb (fresh)]
    (v/assert kb '(reifiable_function AcOrphFn) 'CxUniverse {:strength :monotonic})
    (let [hs (mapv (fn [i] (v/assert kb (list 'acOrphUse (ind "AcOU" i)
                                              (list 'AcOrphFn (ind "AcOA" i)))
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(def ^:private merge-population
  "Standing `sameAs` merges in the merge workload — its own knob rather than `n`, for
  `nat-population`'s reason: it is the quantity the reconcile's read budget could be
  proportional to while `n` counts retractions, and separating them is what lets a re-pin
  say which of the two moved."
  100)

(defn- merge-bystander-teardown
  "n plain facts retracted on a KB carrying `merge-population` standing `sameAs` merges
  that none of them names.

  The equality twin of `nat-bystander-teardown`, and it prices the same kind of thing.
  Every settle reconciles the superseded set against the equality closure, because a
  supersession is derived state that must not outlive the merge behind it
  (docs/equality.md).  Re-examining an entry means fetching its record, rewriting its
  sentence through the closure and probing the store for the restatement — so a
  reconcile that walks the whole displaced set puts `merge-population` store probes on
  every retraction of every KB that has merged anything.

  Here it has nothing to reconcile at any point: each merge displaces one `(mergeBorn
  AcMHi_i AcMPlace)` fact, no timed retraction names a merged term, and the closure is
  the same after the workload as before it.  So the budget is a reading of the
  reconcile's **scope**, and it tracks `merge-population` if the scope is the whole set
  and `n` if it is the moved region."
  []
  (let [kb (fresh)]
    (dotimes [i merge-population]
      (v/assert kb (list 'acMergeBorn (ind "AcMHi" i) 'AcMPlace) 'CxPerf {})
      (v/assert kb (list 'sameAs (ind "AcMAa" i) (ind "AcMHi" i)) 'CxPerf {}))
    (let [hs (mapv (fn [i] (v/assert kb (list 'acMergeBystand (ind "AcMBy" i) 'AcMByVal)
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(defn- preserved-edges
  "A `genl` edge between two fresh types, on a KB holding `k` predicates preserved along
  `genl`, each with a claim on its own type and a forward rule over it.  No claim reaches
  either end of the edge, so the edge moves no predicate and re-joins no rule: what it
  costs above `:taxonomy-edge`'s shape is the narrowing's own reads.

  **The pair of these is the claim**, as `:membership` and `:deep-membership` are:
  `inherit/crossing-claim?` reads the slot roster once per closure term and looks the
  declarations up by relation, so the index reads an edge costs do not depend on `k`.  A
  narrowing that read per declaration makes `:preserved-edges-32` read eight times what
  `:preserved-edges-4` does in the families it reads."
  [k]
  (let [kb (fresh)]
    (dotimes [j k]
      (let [pr (symbol (str "acPres" j))
            w  (symbol (str "acpw_t" j))]
        (v/assert kb (list 'genl w 'thing) 'CxPerf {:strength :monotonic})
        (v/assert kb (list 'transitiveInArg pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr w 'thing) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'acPresNoted '?x '?y)))
                  'CxPerf {})))
    (fn [] (dotimes [i n]
             (v/assert kb (list 'genl (symbol (str "acpe_t" i)) (symbol (str "acpf_t" i)))
                       'CxPerf {})))))

(defn- preserved-edges-4 [] (preserved-edges 4))
(defn- preserved-edges-32 [] (preserved-edges 32))

;; ---- the budgets ---------------------------------------------------------
;;
;; Measured, not designed.  Each is what the engine does today at `n` = 100; the point of
;; writing them down is that the next change to any of these numbers is visible.  A
;; failure prints the delta per family, so re-pinning is reading the report.
;;
;; **`:functor-root` counts no visibility gate, and that is worth knowing before reading
;; it as high.**  Every assert runs a settle and a settle asks `res/excepted-handles`,
;; whose gate is the KB's own `:excepted` roster being empty (`kb/note-excepted!`) — a
;; deref, and no index read.  A gate keyed on the `except` functor root instead would add
;; three reads per assert to every workload here and seven to `rule-fired`, on a KB that
;; excepts nothing; none of that is in these numbers.
;;
;; **`:argument-root` and `:argument-slot` carry the small-side lead (`res/*lead-side*
;; :auto`), which is why they read near-equal.**  A scoped clash retrieval leads from the
;; term's own postings — one predicate-agnostic `:argument-slot` read plus its count —
;; rather than one predicate-scoped `:argument-root` bucket per sub-predicate, whenever the
;; term is the smaller side.  That trades per-spec `:argument-root` reads for `:argument-
;; slot` ones and keeps a deep hierarchy's closure walk at O(term); these workloads are
;; deliberately shallow, so the closure is nothing to collapse and what lands here is the
;; small constant the trade costs — carried as data, per the "a legitimate optimization
;; fails this gate" rule above.  `matches_hierarchical_test` holds the set the three lead
;; sides must agree on and `lead_side_cost_test` holds the shape (`:auto` flat in the
;; hierarchy width, the scoped lead not) — the win this constant buys, so a re-pin here
;; cannot hide its regression.

(def ^:private budgets
  [{:name    :plain
    :build   plain
    :sentexes 100
    :reads   {:argument-root 100 :argument-slot 100 :exception-index 100
              :functor-root 800 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 400 :roots 400 :roster 202 :slots 200}}

   ;; **One membership read per assert above `plain`, and it is the arity descension's.**
   ;; `acm_t` declares no arity of its own and sits under `thing`, so `inherited-arity`
   ;; asks what `thing` is declared with: the `(arity P n)` table answers that as a map
   ;; read and adds no work, and the predicate-type membership — the second spelling,
   ;; which a KB loaded without CxCore's rules is the only one to have — costs the
   ;; retrieval counted here. It is paid per **super the table says nothing about**, so
   ;; it is proportional to hierarchy depth on a predicate that declares no arity, and
   ;; free on one that declares either spelling: `own-arity` answers first and the walk
   ;; never runs. Every type in the shipped starter carries `(unary_predicate t)`, which is
   ;; why this is the workload that shows it and the `declared` one is unmoved.
   ;; **Two slot writes per assert, not one, and the second is what makes the read above
   ;; flat.**  A unary fact enters the `[:unary-slot term]` roster beside the
   ;; `[:argument-slot 1 term]` one, unconditionally rather than reference-counted
   ;; (`kv/slot-adds` says why), so a membership costs one extra `:add-to-set` and no
   ;; extra read.  In exchange `kb/types-of` — the retrieval every definitional
   ;; check bottoms out on — reads the term's *memberships* instead of every fact holding
   ;; it at argument 1: the `:reads` above are unchanged because the read is the same two
   ;; key shapes, and the records behind them are the types rather than the whole posting.
   ;; A KB of binary facts pays neither: `:plain`'s slots are unmoved.
   {:name    :membership
    :build   membership
    :sentexes 100
    :reads   {:argument-root 300 :argument-slot 300 :exception-index 100
              :functor-root 800 :rule-index 200 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 400 :terms 300 :roots 300 :roster 100 :slots 200}}

   ;; **The same reading at depth 8, and the pair is the point.**  Whatever this costs
   ;; above `:membership` is what seven more super-predicates cost, so the two budgets
   ;; together say whether the descension is flat in the depth of the hierarchy or
   ;; proportional to it.  Today it is proportional; a change that makes it flat drops
   ;; this one to `:membership`'s numbers and is the improvement carried as data.
   ;; Read against `:membership`: 300 -> 1100 in each of `:argument-root` and
   ;; `:argument-slot`, for eight more supers over a hundred asserts.  That is **one
   ;; `:argument-root` and one `:argument-slot` per super per assert**, exactly, and the
   ;; writes do not move at all — the depth buys reads and stores nothing.
   {:name    :deep-membership
    :build   deep-membership
    :sentexes 100
    :reads   {:argument-root 1100 :argument-slot 1100 :exception-index 100
              :functor-root 800 :rule-index 1000 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 400 :terms 300 :roots 300 :roster 100 :slots 200}}

   ;; **The workload the entailment moves most.**  Every predicate is declared, so the
   ;; shipped default reads each declaration and tests the argument against the type it
   ;; names — the `:argument-root`/`:argument-slot` jump over `plain` — where the
   ;; constraint-only reading (`VAELII_ASSERTIVE_ARG_TYPES=0`) reads one dynamic var and
   ;; stops.  This is the per-assert declaration cost `lein perf` divides out and this gate
   ;; makes visible; it is the whole reason the entailment stays measured, not pinned off.
   ;; The arguments already hold the type, so each mint dedups to a stored handle and adds
   ;; the declaration's justification without re-querying the minted type's own declarations:
   ;; `special/entail-arg-type` recurs the entailment cascade only on a transition to
   ;; believed, and an already-believed dedup target is not one. That skip is the −2 in each
   ;; of `:argument-root`, `:argument-slot` and `:functor-root` against the pre-skip budget.
   ;;
   ;; Every minted type is a functor no sentence declares `arg` or `genlArg` of, so deriving
   ;; its own entailments no longer probes the argument index for declarations it lacks:
   ;; `res/constraining-predicates` filters a mint's functor against the declaration roster,
   ;; which is the −1,400 `:argument-root` and −1,300 `:argument-slot` this workload stopped
   ;; reading when the filter landed.
   ;;
   ;; And each mint's admissibility is checked once, not twice.  `checks/entailment-check`
   ;; runs `constraint-problem` over every prospective mint before the trigger is stored and
   ;; refuses the trigger if one fails, so the materializer's own `constraint-violation` over
   ;; the same first-level mints (`special/inadmissible`, `pre-checked?`) asks a question
   ;; already answered — storing the trigger only adds memberships, which convict on an absent
   ;; type and never a present one.  Skipping it is the −600 `:argument-root`, −600
   ;; `:argument-slot` and −400 `:functor-root` here; the retroactive and chaining mints, which
   ;; no pre-store check covers, still pay it.
   {:name    :declared
    :build   declared
    :sentexes 100
    :reads   {:argument-root 600 :argument-slot 500 :exception-index 100
              :functor-root 1100 :rule-index 100 :trie-counts 100 :trie-lookup 300}
    :writes  {:levels 500 :terms 300 :roots 400 :roster 0 :slots 200}}

   ;; **No `:rule-index` family at all, and only a negative workload reads that way.**  An
   ;; arriving negation triggers the `[:not q]` keys for the specs `q` of its body's
   ;; predicate (`rules/trigger-keys`), and those are enumerated from the live
   ;; `:rule-antecedents` roster rather than from the spec closure — so a KB whose rules read
   ;; no negation, which is this one, names no key at all and never probes the rule index.
   ;; A positive assert cannot reach zero the same way: its keys are `genls(pred)`, which is
   ;; never empty, so every other workload here carries the family.
   {:name    :negative
    :build   negative
    :sentexes 100
    :reads   {:argument-root 100 :argument-slot 100 :exception-index 200
              :functor-root 700 :trie-counts 200 :trie-lookup 100}
    :writes  {:levels 400 :terms 400 :roots 400 :roster 103 :slots 101}}

   ;; **Seven `:argument-root` and seven `:argument-slot` reads per assert above `plain`**
   ;; — the shared-determinant probe on argument 1, its `marks-above?`/mark-reach checks,
   ;; and the constraint-nogood vocabulary gate, none of which `plain` pays for since it
   ;; declares no predicate property at all.  What this pins is that it stays a per-assert
   ;; *constant*: a regression back to the pre-06ae8613 extent sweep would not add a fixed
   ;; seven per assert, it would add a term proportional to the predicate's own growing
   ;; extent (`subtree-facts` over up to `n` stored tuples, batched into the sweep's own
   ;; read family) — which this exact-count gate catches on the very first re-pin attempt,
   ;; where `lein perf`'s ratio check cannot (see the docstring above).
   {:name    :functional-in-arg-arity-2
    :build   functional-in-arg-arity-2
    :sentexes 100
    :reads   {:argument-root 800 :argument-slot 800 :exception-index 100
              :functor-root 800 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 400 :roots 400 :roster 200 :slots 200}}

   {:name    :compound
    :build   compound
    :sentexes 100
    :reads   {:argument-root 100 :argument-slot 100 :exception-index 100
              :functor-root 800 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 800 :terms 600 :roots 400 :roster 104 :slots 200}}

   ;; 200 indexed sentexes for 100 asserts — the rule concludes one apiece
   ;;
   ;; **This workload pays nothing for the forward-chain authority probe, and that is the
   ;; point of the frontier gate.**  `perf(chain)` skips the novelty trie-walk for a functor
   ;; the store held nothing under when a run began, decided by one `count-with-functor`
   ;; probe (`kb/functor-cache-authoritative?`).  The probe is worth taking only over a bulk
   ;; fixpoint that concludes the functor many times; over a run of one conclusion it never
   ;; amortizes.  So the memo is armed only when the seed frontier clears
   ;; `kb/chain-authority-min-frontier`, and each assert here seeds its own one-fact run —
   ;; below the floor.  The memo stays nil, `find-sentex-handle` walks the trie exactly as
   ;; it did before the optimization, and these numbers are the pre-perf ones unchanged: a
   ;; `forward-chain` over a wide seed is where the skip is priced, and `lein perf`'s join
   ;; workloads hold that shape where this micro-workload cannot.
   {:name    :rule-fired
    :build   rule-fired
    :sentexes 200
    :reads   {:argument-root 200 :argument-slot 200 :exception-index 300
              :functor-root 1100 :rule-index 200 :trie-counts 200 :trie-lookup 200}
    :writes  {:levels 1000 :terms 800 :roots 800 :roster 200 :slots 400}}

   ;; **The vocabulary write, and the first budget here that is not about a fact.**  What it
   ;; prices is everything a `genl` edge sets off that a fact does not: the arity report's
   ;; trigger, the argument-type entailment's two gates, and the subtree read that puts the
   ;; facts under the edge back on the chaining agenda.
   ;;
   ;; **Both ends' own declarations, where a clash needs only one of them to exist.**
   ;; `edge-arity-problem` reads the super's length even when the sub declares none, because
   ;; that is the gate deciding whether the sub is worth walking at all — an undeclared sub
   ;; under a declared super is exactly the pair an endpoint-only reader misses.  One
   ;; membership read per edge, so 100 edges is the +100 `:argument-root` and +100
   ;; `:argument-slot`, and it is a constant: the closure walk behind the gate runs on the
   ;; *other* end and only once a length is there to disagree with, which is why
   ;; `lein perf`'s `taxonomy-depth` — edges down one chain, neither end declared — stays
   ;; flat rather than going quadratic in the chain.
   {:name    :taxonomy-edge
    :build   taxonomy-edge
    :sentexes 100
    :reads   {:argument-root 300 :argument-slot 300 :exception-index 300
              :functor-root 1200 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 400 :roots 400 :roster 101 :slots 101}}

   ;; **One retrieval per relative the arity table does not name**, which is what the entry point
   ;; costs an arity declaration, and `declaration-relatives` is the number to read it
   ;; against.  Measured at both: four relatives cost 600 `:argument-root` and 600
   ;; `:argument-slot`, two cost 400 and 400, so the per-relative term is **one of each per
   ;; relative per assert** and everything else here is the constant.  That is the same
   ;; pair, in the same proportion, that `:membership` and `:deep-membership` read off the
   ;; descension's other walk — the two questions are one membership retrieval apiece and
   ;; neither has anywhere cheaper to go.
   ;;
   ;; A change that answers the second spelling off the taxonomy drops the per-declaration
   ;; term to nothing and re-pins here; one that widens the walk raises it.  `lein perf`
   ;; sees neither: a constant on a linear term is what this file is for.
   {:name    :arity-declaration
    :build   arity-declaration
    :sentexes 100
    :reads   {:argument-root 600 :argument-slot 600 :exception-index 100
              :functor-root 600 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 300 :roots 300 :roster 1 :slots 100}}

   ;; **Two workloads, one budget, and the equality is the claim.**  A `genl` edge on a KB
   ;; preserving 4 predicates along `genl` and one preserving 32 read exactly the same, so
   ;; nothing the narrowing reads is per declaration.  Read against `:taxonomy-edge`, the
   ;; narrowing is the +600 `:argument-slot` — the edge's two closure terms at the one
   ;; preserved position, asked by the chainer, the re-check trigger and the settle — and
   ;; the +1,200 `:functor-root`, the four permuting-mark postings those three calls stamp
   ;; the mark cache with.  The +2 `:argument-root` is the declarations on `genl` read once,
   ;; on the first edge, and cached on the `:preserving` roster after it.  A narrowing that
   ;; read one argument root per declaration per closure term read 4,500 and 29,700
   ;; `:argument-root` here.  The narrowing is asked only when it can change the caller's
   ;; answer, and asking costs one read that stops at the first predicate it clears: the
   ;; +200 `:rule-index` is the chainer's and the re-check trigger's rule read on one
   ;; preserved predicate, and the +100 `:functor-root` the settle's extent read on one.
   {:name    :preserved-edges-4
    :build   preserved-edges-4
    :sentexes 100
    :reads   {:argument-root 302 :argument-slot 900 :exception-index 300
              :functor-root 2500 :rule-index 300 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 400 :roots 400 :roster 200 :slots 200}}

   {:name    :preserved-edges-32
    :build   preserved-edges-32
    :sentexes 100
    :reads   {:argument-root 302 :argument-slot 900 :exception-index 300
              :functor-root 2500 :rule-index 300 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 400 :roots 400 :roster 200 :slots 200}}])

;; The retraction half.  `:unindexed` is the retraction budgets' `:sentexes` — how many
;; sentexes left the index — and it is checked first for the same reason: a budget
;; compared against a different number of teardowns is comparing two workloads.
;;
;; `:dead` inside `:retracts` is the one number here that is **not** a per-operation
;; constant, and it is budgeted anyway because it is exactly reproducible for a fixed
;; corpus torn down in a fixed order.  Read it as a property of this workload, never as
;; what a fact of this shape costs: the same fact retracted out of a corpus that shares
;; more prefix kills fewer nodes, and moving `n` moves this number non-proportionally
;; while every other family scales with it.
(def ^:private retraction-budgets
  [{:name    :plain-teardown
    :build   plain-teardown
    :sentexes 0
    :unindexed 100
    :reads   {:exception-index 100 :functor-root 500 :trie-counts 100}
    :writes  {}
    :retracts {:levels 500 :terms 400 :roots 400 :roster 202 :slots 200 :dead 302}}

   ;; 200 unindexed for 100 retractions — each premise solely supported one conclusion
   {:name    :rule-derived-teardown
    :build   rule-derived-teardown
    :sentexes 0
    :unindexed 200
    :reads   {:exception-index 200 :functor-root 500 :trie-counts 200}
    :writes  {}
    :retracts {:levels 1000 :terms 800 :roots 800 :roster 200 :slots 400 :dead 602}}

   ;; **`:functor-root` and `:term-index` are the two a narrowing of the orphan sweep
   ;; **The workload the orphan sweep's scope is priced by, and the numbers below are the
   ;; second pinning.**  The first read 10,800 functor-root and 10,000 term-index for 100
   ;; retractions — 108 and 100 per retraction, one pair per standing reified NAT, on a
   ;; teardown naming none of them and collecting none of them, because the sweep read what
   ;; the KB held rather than what the retraction reached.  Narrowed to the removed region
   ;; it is 5 functor-root and 0 term-index per retraction, which is `plain-teardown`'s own
   ;; cost: a bystander NAT population now costs a teardown nothing at all.  `:trie-lookup`
   ;; goes to 0 for the same reason.  The other five families are the same removal either
   ;; way and did not move.
   ;;
   ;; `:term-index` and `:trie-lookup` are **absent rather than pinned at 0**: a family the
   ;; workload never reads is a key the tally never emits, and under exact equality an
   ;; absent key is the stronger claim of the two — one read of either fails this budget.
   {:name    :nat-bystander-teardown
    :build   nat-bystander-teardown
    :sentexes 0
    :unindexed 100
    :reads   {:exception-index 100 :functor-root 500 :trie-counts 100}
    :writes  {}
    :retracts {:levels 500 :terms 400 :roots 400 :roster 102 :slots 101 :dead 301}}

   ;; 200 unindexed for 100 retractions — the use, plus the `termOfUnit` its removal
   ;; orphaned.  **That count is the workload's point and is not a number to re-pin
   ;; downward**: a sweep that stops finding the orphan unindexes 100 here and leaves a raw
   ;; `nat/` symbol behind, so the narrowing is admissible only while this stays 200.  It
   ;; did.  The reads fell with the scope, exactly as the bystander's did — the first
   ;; pinning read 11,800 functor-root and 10,100 term-index, off a *declining* population
   ;; the sweep walked twice per retraction (`:term-index` was 2·(100+99+…+1)).  What is
   ;; left is the region: 10 functor-root and 3 term-index per retraction, for a constant
   ;; the population no longer enters.
   ;;
   ;; The orphan question itself settles on the `termOfUnit` clause here — a collected
   ;; constant has its map and nothing else left — so it reads neither the expression nor
   ;; the declarations to find out what the mint wrote about it (`nat/minted-for`, held
   ;; behind a delay).  That is the whole of the difference between this budget and one
   ;; that asks those questions unconditionally: three functor-root reads and one
   ;; trie-lookup per retraction, on the path every teardown of a NAT-bearing KB takes.
   {:name    :nat-orphan-teardown
    :build   nat-orphan-teardown
    :sentexes 0
    :unindexed 200
    :reads   {:exception-index 200 :functor-root 1000 :term-index 300
              :trie-counts 200}
    :writes  {}
    :retracts {:levels 1200 :terms 1000 :roots 800 :roster 303 :slots 400 :dead 802}}

   ;; **The workload the supersession reconcile's scope is priced by**, and `:trie-lookup`
   ;; is the family that reads it: the reconcile probes the store for each displaced
   ;; spelling's restatement, so a pass over the whole displaced set costs one lookup per
   ;; standing merge per retraction.  A reconcile scoped to the KB reads **10,000** of them
   ;; here — 100 merges × 100 retractions, on a teardown that names none of them and
   ;; un-merges nothing — and one scoped to the moved region reads **none**.
   ;;
   ;; Everything else is `plain-teardown` exactly: 500 `:functor-root`, 100
   ;; `:exception-index`, 100 `:trie-counts`.  The three retract families that differ from
   ;; it (`:roster`, `:slots`, `:dead`) differ because the *victims* are a different shape
   ;; of fact, not because the merges are there.
   ;;
   ;; `:term-index` and `:trie-lookup` are **absent rather than pinned at 0**, and that is
   ;; the stronger claim: a family the workload never reads is a key the tally never emits,
   ;; so one read of either fails this budget.
   {:name    :merge-bystander-teardown
    :build   merge-bystander-teardown
    :sentexes 0
    :unindexed 100
    :reads   {:exception-index 100 :functor-root 500 :trie-counts 100}
    :writes  {}
    :retracts {:levels 500 :terms 400 :roots 400 :roster 102 :slots 101 :dead 301}}])

;; ---- measuring -----------------------------------------------------------

(defmacro ^:private with-shipped-retrieval
  "Run `body` under every switch that decides where a read goes, each bound to its
  **shipped default** rather than to whatever the run inherited.

  A budget is a claim about one configuration, and these are the vars that change which
  family answers.  `scripts/test-sweeps.sh` runs the whole suite under `VAELII_HIER=0`,
  which routes context-scoped matching through the reference nested fan-out instead of the
  set-algebra path: measured here, that moves two reads per sentex off `:argument-root`
  and onto `:trie-lookup` — the trade the two paths exist to make, and a budget written for
  one of them is simply false about the other.  Pinning is the same argument that pins the
  backend, and it is preferred to standing aside, since a gate that skips under a sweep is
  a gate that is not running on the configuration somebody is currently changing.

  The set is `tu/shipped-defaults` rather than a list of vars named here, and the
  difference is which switches a local list omits without anybody noticing.
  `chain/*matcher*` is the standing example: it is reached from `join-matches` and
  nowhere else, and none of the workloads below joins a second antecedent, so a pin that
  left it out would read exactly like one that did not.  A roster the sweeps and the
  gates share is what stops the next workload from finding that out."
  [& body]
  `(tu/with-shipped-config ~@body))

(defn- by-family
  "One functor-keyed tally totalled across functors, with the operation count dropped.
  `{}` and not nil for a tally nothing wrote, since an absent family and an empty one are
  the same claim here and only one of them compares equal to a budget."
  [rows op-key]
  (reduce #(merge-with + %1 %2) {} (map #(dissoc % op-key) rows)))

(defn- measure
  "Run one workload under the instrument and total its tallies by family.  `:writes` and
  `:retracts` are keyed by functor in the snapshot, which is a diagnostic the *profile*
  wants and a distinction a budget does not: what a family costs an operation is the same
  question whichever predicate arrived.

  The KB is built inside the pinned configuration too: a taxonomy or a declaration laid
  down under one retrieval path and priced under another would be a workload nobody runs."
  [build]
  (with-shipped-retrieval
    (tu/with-entailing                              ; the shipped default; budgets below are on-path
      (let [thunk (build)
            _     (prof/start)
            _     (thunk)
            snap  (prof/stop)
            wrows (vals (:writes snap))
            rrows (vals (:retracts snap))]
        {:reads     (into {} (:reads snap))
         :writes    (by-family wrows :asserts)
         :retracts  (by-family rrows :retracts)
         :sentexes  (reduce + 0 (map :asserts wrows))
         :unindexed (reduce + 0 (map :retracts rrows))}))))

(defn- delta-report
  "The families whose count moved, as a table.  Every family either side names is listed,
  so a family that appeared from nowhere reads as `0 -> 300` rather than going missing."
  [expected actual]
  (->> (sort (into (set (keys expected)) (keys actual)))
       (keep (fn [k]
               (let [e (get expected k 0), a (get actual k 0)]
                 (when (not= e a)
                   (format "    %-16s %6d -> %-6d  (%+d)" (name k) e a (- a e))))))
       (str/join "\n")))

(defn- check-tally [what wl expected actual]
  (is (= expected actual)
      (format (str "%s: the %s budget moved.\n%s\n"
                   "  If this change is intended, re-pin the number in its budget — the diff "
                   "is the change's own index cost.\n"
                   "  If it is not, a constant was added to the path this workload drives "
                   "and `lein perf` cannot see it.")
              (name (:name wl)) what (delta-report expected actual))))

;; ---- the gate ------------------------------------------------------------

(defn- check-workload
  "One workload measured and held to its whole budget.  The two counts come first,
  because a budget compared against a different number of indexed or unindexed sentexes
  is comparing two workloads; the three tallies follow.  A workload that declares no
  `:writes` or `:retracts` budget is claiming the empty one, which is a claim worth
  making in both directions — an assert workload that started unindexing something, or a
  teardown that started writing, is a change somebody has to explain."
  [{:keys [name build sentexes unindexed] :as wl}]
  (testing (str "the " (clojure.core/name name) " workload")
    (let [got (measure build)]
      (is (= sentexes (:sentexes got))
          (str (clojure.core/name name) ": the workload indexed a different number of "
               "sentexes, so its budgets are about something else now"))
      (is (= (or unindexed 0) (:unindexed got))
          (str (clojure.core/name name) ": the workload unindexed a different number of "
               "sentexes, so its budgets are about something else now"))
      (check-tally "read"    wl (get wl :reads {})    (:reads got))
      (check-tally "write"   wl (get wl :writes {})   (:writes got))
      (check-tally "retract" wl (get wl :retracts {}) (:retracts got)))))

(def ^:private indexes [:memory :memory-columnar])

(deftest assert-cost-is-what-it-was
  (doseq [ix indexes wl budgets]
    (binding [*index* ix] (testing (name ix) (check-workload wl)))))

(deftest retraction-cost-is-what-it-was
  (doseq [ix indexes wl retraction-budgets]
    (binding [*index* ix] (testing (name ix) (check-workload wl)))))

;; ---- the frontier gate: armed for a bulk run, silent for an incremental one ----
;;
;; The read budgets above pin what an *incremental* assert costs, and `rule-fired`'s
;; `:functor-root`/`:trie-lookup` are the pre-optimization numbers precisely because a
;; one-fact run does not arm the forward-chain authority memo
;; (`kb/chain-authority-min-frontier`).  This is the other half of that claim, and it is a
;; shape rather than a constant — the way `lein perf` holds a ratio the exact budgets
;; cannot.  Over a **bulk** frontier the memo *is* armed, and its whole purpose — skipping
;; `find-sentex-handle`'s novelty trie-walk for a functor the store never held — shows up
;; as a `:trie-lookup` count that does **not** grow with the conclusions.  Both halves are
;; a standing regression risk: a change that stops arming the memo silently loses the skip
;; (and `:trie-lookup` goes back to O(conclusions) on every bulk load), and one that arms
;; it for every run silently puts the probe back on the incremental assert path that
;; `rule-fired` guards.

(defn- bulk-chain-trie-walks
  "Forward-chain a KB of `n` `vSrc` facts through one rule concluding a fresh `vDst` the
  store never held, and return what it concluded and the run's novelty-walk count.  The
  facts load with `:chain? false`, so the timed run is a single `forward-chain` whose seed
  is the whole datum set — armed exactly when `n` (plus the rule) clears the frontier."
  [n]
  (with-shipped-retrieval
    (let [kb (fresh)]
      (v/assert kb (rules/rule-sentence ['(vSrc ?x ?y)] '(vDst ?x ?y))
                'CxPerf {:direction :forward :strength :monotonic})
      (dotimes [i n]
        (v/assert kb (list 'vSrc (ind "Va" i) (ind "Vb" i)) 'CxPerf {:chain? false}))
      (prof/start)
      (v/forward-chain kb)
      (let [snap (prof/stop)]
        {:concluded   (count (v/sentexes-with-functor kb 'vDst))
         :trie-lookup (get-in snap [:reads :trie-lookup] 0)}))))

(deftest the-frontier-gate-arms-the-authority-skip-for-a-bulk-run
  (let [floor       kb/chain-authority-min-frontier
        below       (bulk-chain-trie-walks (quot floor 2))     ; seed under the floor: not armed
        armed-small (bulk-chain-trie-walks (+ floor 20))       ; over the floor: armed
        armed-large (bulk-chain-trie-walks (+ floor 120))]     ; and again, larger
    (testing "each run concluded one vDst per vSrc — the workloads are real and equal-shaped"
      (is (= (quot floor 2) (:concluded below)))
      (is (= (+ floor 20)   (:concluded armed-small)))
      (is (= (+ floor 120)  (:concluded armed-large))))
    (testing "armed, the novelty walk is skipped: trie-lookups are flat in n and far below the conclusions"
      (is (= (:trie-lookup armed-small) (:trie-lookup armed-large))
          "the skip makes the walk count independent of n; if it grew, the memo stopped arming")
      (is (< (:trie-lookup armed-large) (:concluded armed-large))
          "one probe answers for the whole run, so a bulk fixpoint walks O(1), not O(conclusions)"))
    (testing "below the floor the memo is not armed — every novel conclusion still walks"
      (is (>= (:trie-lookup below) (:concluded below))
          "an unarmed run walks at least once per conclusion, exactly as it did pre-optimization")
      (is (> (:trie-lookup below) (:trie-lookup armed-large))
          "so the smaller unarmed run out-walks the larger armed one — the skip is what closes the gap"))))

(deftest instrument-is-silent-when-off
  ;; The budgets above are only meaningful if the protocols added no work when nobody is
  ;; collecting — a gate on an instrument that is always running measures the instrument.
  (testing "a workload outside `start`/`stop` records nothing"
    (is (false? (prof/profiling?)))
    ((plain))
    (is (nil? (prof/snapshot)))))
