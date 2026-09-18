;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.label
  "Brave/cautious classification of a settled tie, and materializing one labeling as
  a specialization context.

  ## What this adds over `in?`

  The TMS answers *what do I believe*. After `settle` arbitrates a default/default
  tie, one side is IN and the other OUT — but that answer flattens two very different
  situations. A belief can be IN because every consistent way of resolving the
  contradictions keeps it, or because the solver had two equally good options and
  picked one. `in?` cannot tell them apart; both read as \"believed\".

  Brave/cautious classification separates them by asking the solver for *all* optimal
  answer sets rather than one:

  | class | in every optimum | in some optimum | meaning |
  |---|---|---|---|
  | `:true` | yes | yes | forced — no consistent labeling gives it up |
  | `:supportable` | no | yes | arbitrary — the current belief is one of several |
  | `:false` | no | no | excluded — no consistent labeling holds it |

  `:supportable` is the interesting one, and it is invisible from the TMS alone. In a
  Nixon diamond both sides are `:supportable`: whichever the TMS committed to, the
  other was equally available.

  ## Concert with the TMS

  Two rules keep these from drifting apart from belief.

  **Classification reads the recorded program, never a recomputed one.** Resolving a
  tie erases its own evidence — the defeated side stops matching, so the nogood is no
  longer derivable from the KB. The `:program` atom on the KB holds what the solver was
  actually asked (see the KB record); `vaelii.core/last-program` is the public read of it.

  **Labeling reads the TMS, not a fresh solve.** `label-context` materializes the
  labeling the engine *committed to*, taken from `jtms/in?`, rather than re-solving
  and hoping for the same answer set back. A re-solve would usually agree, and
  \"usually\" is not a property worth building on.

  So the invariants hold by construction, and `asp_label_test` pins them:

      :true        ⊆ believed        (cautious holds in the committed model)
      :false       ∩ believed = ∅    (excluded holds in no model, including that one)
      :supportable — either way, by definition

  ## Requirements

  Classification needs a real ASP backend; `local-solver` produces one labeling and
  cannot enumerate optima. With no backend reachable, `classify` reports every
  contested assumption as `:supportable` — honest (each *is* one of several options)
  and never overclaims `:true`."
  (:require
   [vaelii.impl.asp.edge :as edge]
   [vaelii.impl.asp.solver :as solver]
   [vaelii.impl.config :as config]
   [vaelii.impl.jtms :as jtms]
   [vaelii.impl.kb :as kb]
   [vaelii.impl.naming :as nm]
   [vaelii.impl.protocols :as p]
   [vaelii.impl.settle :as settle]
   [vaelii.impl.solve :as solve]
   [vaelii.impl.types.reasoning :as reasoning]
   [vaelii.impl.types.solve :as solve-types]
   [vaelii.impl.wiring :as wiring]))

;; `classify-program` lives in `asp.edge` (below core), so `settle` can stamp the
;; classification onto the TMS as belief settles.  Re-exported here for the KB-level
;; callers, which reach it at this layer.
(def classify-program edge/classify-program)

(defn classify
  "Classify the tie `kb` last settled — which of its beliefs were forced, which were
  an arbitrary pick, and which were excluded.

  Returns `{:true #{handle} :supportable #{handle} :false #{handle}}`, all empty when
  no tie has been arbitrated (nothing contested means nothing to be uncertain about)."
  [kb]
  (if-let [program @(reasoning/program kb)]
    (classify-program program)
    {:true #{} :supportable #{} :false #{}}))

;; ---- the dilemma bridge -------------------------------------------------
;;
;; Everything above classifies a tie the engine *arbitrated*.  The engine does not
;; arbitrate a plain rebuttal: a coexisting P/¬P pair at :default is a represented
;; dilemma, both sides stay IN, and `settle` builds no Program (docs/exceptions.md).
;; So `last-program` is nil in exactly the cases classification is interesting for.
;;
;; What `contradictions` reports is nevertheless the material a Program is made from —
;; that is the point of handing back both sides with their justifications rather than
;; picking one.  `dilemma-program` turns it back into that shape, for a caller who asks.

(defn- sides-content
  "What each side of each dilemma asserts, keyed by handle."
  [dilemmas]
  (into {} (mapcat (fn [d] (map (juxt :handle #(select-keys % [:sentence :context]))
                                (:sides d))))
        dilemmas))

(defn dilemma-program
  "One `Program` covering **every** dilemma `kb` currently reports, or nil if it
  reports none.

  All of them together rather than one at a time, because dilemmas can share a datum:
  a handle contested in two nogoods must be given up (or kept) once, consistently, and
  only a solver holding both constraints at once can do that.  Solving them
  separately would let the same datum be believed by one answer and not the other,
  which is not a labeling of anything."
  [kb]
  (when-let [ds (seq (settle/ranked (settle/contradictions-of kb)))]
    (solve/program (into #{} (mapcat :nogood) ds)
                   (mapv #(select-keys % [:nogood :priority :sentence]) ds)
                   (sides-content ds))))

(defn- cluster-indices
  "Partition `[0 n)` into connected components under `edges` — a seq of `[i j]` index pairs
  to union — returned as a seq of index sets.  Union-find, so two nogoods joined by any edge,
  directly or through a chain, land in one cluster and are enumerated together."
  [n edges]
  (let [^ints parent (int-array n)]
    (dotimes [i n] (aset parent i i))
    (letfn [(root [i] (let [p (aget parent i)]
                        (if (= p i) i (let [r (root p)] (aset parent (int i) (int r)) r))))]
      (doseq [[i j] edges]
        (aset parent (root i) (int (root j))))
      (->> (range n) (group-by root) vals (map set)))))

(defn- k-subsets
  "The size-`k` subsets of `coll` (a vector), each a seq — a plain combinations generator."
  [coll k]
  (cond
    (zero? k)    (list ())
    (< (count coll) k) nil
    :else        (let [[x & xs] coll]
                   (concat (map #(cons x %) (k-subsets (vec xs) (dec k)))
                           (k-subsets (vec xs) k)))))

(defn- binomial
  "C(`n`, `k`), exact: each step's product is divisible by the step's divisor."
  [n k]
  (reduce (fn [acc i] (/ (*' acc (- n i)) (inc i))) 1 (range k)))

(defn- min-resolutions
  "Every minimum-cardinality subset of `members` whose forcing OUT satisfies every nogood in
  `ngs` (each a member set) — a nogood is satisfied once not all its members remain believed
  under the forcing.  `holds?` reads belief under a forced-out set: `(holds? s m)` is true
  while member `m` is believed with `s` forced OUT.

  Iterated by increasing size, so the first size with a satisfying subset yields every
  optimal resolution — genuinely tied optima all return.  Iterating whole subsets rather than
  branching on one nogood's members is what makes it **belief-faithful**: a member a defeat
  drops by cascade counts as forced OUT and needs no defeat of its own, so a subset that
  forces no member of a nogood can still satisfy it — forcing `pb` OUT satisfies `pa`'s nogood
  when `¬pa` is derived from `pb`.  Returns nil when the subsets examined would exceed
  `VAELII_CLASSIFY_RESOLUTION_BUDGET` (the caller then leaves the cluster `:supportable`).
  Each size's count is computed as a binomial before its subsets are generated, so the
  enumeration never generates a size that would cross the budget."
  [members ngs holds?]
  (let [members (vec members)
        m       (count members)
        budget  (config/classify-resolution-budget)
        sat?    (fn [s] (not-any? (fn [ng] (every? #(holds? s %) ng)) ngs))]
    (loop [k 1, seen (num 0)]                        ; boxed: a binomial can pass Long/MAX_VALUE
      (if (> k m)
        []                                           ; forcing every member out always satisfies
        (let [seen' (+' seen (binomial m k))]
          (if (> seen' budget)
            nil
            (let [sols (into [] (comp (map set) (filter sat?)) (k-subsets members k))]
              (if (seq sols) sols (recur (inc k) seen')))))))))

(defn classify-local
  "A skeptical/credulous classification of the KB's current dilemmas, read from the JTMS
  dependency graph — **no answer-set enumeration, no backend**.  Returns the `classify`
  shape `{:true #{} :supportable #{} :false #{}}`, or nil when the KB reports no dilemma.

  A **resolution** forces OUT a minimum-cardinality set of dilemma members that satisfies
  every nogood (leaves no nogood with all its members still believed); the resolutions are a
  dilemma set's optimal labelings.  A believed datum is classified by which resolutions
  keep it, read through `jtms/grounded-in-region` (belief recomputed with a set forced OUT):

  - `:true` — believed under **every** resolution (skeptical/cautious);
  - `:supportable` — believed under **some** but not every resolution (credulous/brave);
  - `:false` — believed under **no** resolution: currently believed only because base belief
    holds conflicting dilemma sides at once, which no single resolution does.  A
    `(weird N)` drawn from `(and (pac N) (not (pac N)))` is that case.

  `(hasEthicalStance N)` drawn from **both** the pacifist and non-pacifist side is `:true` —
  every resolution keeps one side, so one support survives.  `(opposesWar N)` resting on the
  pacifist side alone is `:supportable`.  It covers derived conclusions, not only the
  dilemma members a `Program` holds — where the member-only `classify-program` leaves a
  derived conclusion to base belief (which believes both sides and so overclaims it
  cautious).

  **Coupled dilemmas are enumerated together, independent ones apart.**  Nogoods that share
  a member, or move a member of each other, form one cluster (`cluster-indices`); a cluster's
  resolutions come from `min-resolutions`.  A datum is classified by the joint resolutions of
  the clusters that move it — the cartesian product of those clusters' optima, since a cluster
  that does not move the datum leaves it at base whatever it resolves to.  A `(f N)` from
  `(and (e1 N) (e2 N))`, where `e1` and `e2` are each `:true` in a separate diamond, is `:true`:
  it survives every combination.  A datum whose product of clusters exceeds
  `VAELII_CLASSIFY_MAX_JOINT_OPTIMA`, or that touches a cluster larger than
  `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS`, is left `:supportable` — sound,
  and a backend is the tool for a large interacting set.  So the cost is the clusters'
  consequence closures: linear in the number of **independent** dilemmas
  (`grounded_forcing_out_test`), exponential only inside one interacting cluster or across the
  clusters one datum joins, and capped at both.  See docs/labeling.md."
  [kb]
  (let [tms     (reasoning/tms kb)
        nogoods (into []
                      (keep (fn [ng]
                              (let [ms (into #{}
                                             (filter #(= :default (jtms/defeat-class tms %)))
                                             (:nogood ng))]
                                (when (seq ms) ms))))
                      (settle/contradictions-of kb))]
    (when (seq nogoods)
      (let [n           (count nogoods)
            max-members (config/classify-max-cluster-members)
            max-optima  (config/classify-max-joint-optima)
            in?    #(jtms/in? tms %)
            gir    (memoize #(jtms/grounded-in-region tms %))
            ;; does `d` stay believed when `extra` is forced OUT?  Region-local: a datum the
            ;; forcing does not reach keeps its live belief.
            holds? (fn [extra d]
                     (let [{:keys [region in]} (gir extra)]
                       (if (contains? region d) (contains? in d) (in? d))))
            ;; the believed datums a set of forced-out members moves
            moved  (fn [extra]
                     (let [{:keys [region in]} (gir extra)]
                       (into #{} (filter #(and (in? %) (not (contains? in %)))) region)))
            ;; every believed datum some dilemma moves, and the datums each dilemma moves
            dependent (moved (reduce into #{} nogoods))
            dep       (mapv moved nogoods)
            ;; datum -> the nogood indices whose forcing moves it (a nogood's own members
            ;; among them, since forcing a nogood OUT moves its members)
            touch     (persistent!
                       (reduce (fn [m i]
                                 (reduce (fn [m d] (assoc! m d (conj (get m d #{}) i)))
                                         m (dep i)))
                               (transient {}) (range n)))
            ;; two nogoods couple when a member of one is moved by forcing the other — shared
            ;; members and derivation coupling both.  Union through `touch` rather than
            ;; comparing every pair, so clustering is linear in the members, not quadratic in
            ;; the nogoods.
            edges     (for [j (range n), m (nogoods j), i (touch m)] [i j])
            clusters  (cluster-indices n edges)
            cluster-of (into {} (mapcat (fn [c] (map (fn [i] [i c]) c))) clusters)
            ;; a cluster's optimal resolutions, or nil when too large / over budget
            optima    (into {}
                            (map (fn [c]
                                   (let [ms (reduce into #{} (map nogoods c))]
                                     [c (when (<= (count ms) max-members)
                                          (min-resolutions ms (mapv nogoods c) holds?))])))
                            clusters)
            ;; the joint resolutions of `cs` — the clusters that move a datum — as forced
            ;; sets: the cartesian product of their optima, each combination unioned into one
            ;; set.  A cluster that does not move the datum leaves it at base whatever it
            ;; resolves to, so ranging over `cs` alone reaches the datum's every joint optimum.
            ;; nil when a cluster is unenumerated or the product exceeds `max-optima`.
            joint  (fn [cs]
                     (reduce (fn [acc c]
                               (let [opt (optima c)]
                                 (when (and acc opt
                                            (<= (* (count acc) (count opt)) max-optima))
                                   (vec (for [a acc, s opt] (into a s))))))
                             [#{}] cs))
            classify-one
            (fn [d]
              (let [cs (into #{} (map cluster-of) (get touch d #{}))]
                (if-let [combos (and (seq cs) (joint cs))]
                  (let [hs (map (fn [s] (holds? s d)) combos)]
                    (cond (every? true? hs) :true
                          (some true? hs)   :supportable
                          :else             :false))
                  ;; touches no dilemma alone (only the joint forcing), or a cluster too large
                  ;; to enumerate: its class needs joint resolutions a backend enumerates
                  :supportable)))
            grouped (group-by classify-one dependent)]
        {:true        (into #{} (:true grouped))
         :supportable (into #{} (:supportable grouped))
         :false       (into #{} (:false grouped))}))))

(defn classify-dilemmas
  "Classify the KB's current dilemmas into `:true`/`:supportable`/`:false` — through the
  ASP backend when one is reachable (exact: `classify-program` over `dilemma-program`),
  and otherwise the solve-free JTMS bracket (`classify-local`).  nil when there is no
  dilemma to classify.  The `(bravely S)` / `(cautiously S)` prover reads this."
  [kb]
  (if (solver/available?)
    (some-> (dilemma-program kb) classify-program)
    (classify-local kb)))

(defn- labeling-solver
  "The solver the labeling solve must use: the **ASP edge solver whenever a backend is
  reachable**, and only otherwise the one installed on the KB.

  This deliberately bypasses `(:solver kb)`, and the reason is that a labeling and its
  classification are two answers about one program that have to agree.  Classification
  needs to enumerate optimal answer sets, which only ASP does, so `classify-program`
  goes straight to the backend and ignores the installed solver.  If the labeling then
  came from `local-solver`, the two would be answering from different search
  procedures — and they diverge in practice, not just in principle.  Measured on two
  nogoods sharing a member, where greedy spends two defeats and the optimum spends
  one:

      stub  defeats {1,3} -> labels {2}      classification {:true {1,3} :false {2}}
      ASP   defeats {2}   -> labels {1,3}

  The stub's labeling keeps an assumption that holds in *no* optimum and drops two
  that hold in *every* one.  Committing to that would materialize an impossible world
  and globally defeat the atoms classification calls forced.

  With no backend the two degrade together and stay consistent for free:
  `classify-program` reports every contested assumption `:supportable` and claims
  nothing, so any labeling the stub produces satisfies a classification that asserts
  no `:true` and no `:false`.

  **With a backend the pairing is all-or-nothing**, which is what makes the reasoning
  above sound in both directions: `edge-solver` answers from the backend or decides
  nothing (`asp.edge`, \"A result that is not an answer\"), so a labeling solve that ran
  out of budget can never be silently answered by the stub while the classification
  beside it came from ASP."
  [kb]
  (if (solver/available?) edge/edge-solver @(:solver kb)))

(defn- check-agrees
  "Throw unless `labeled` is consistent with `classification` — the invariant that
  makes a labeling *of* a classification rather than merely alongside one:

      :true  ⊆ labeled          (holds in every optimum, so it must be kept)
      :false ∩ labeled = ∅      (holds in no optimum, so it must not be)

  Checked rather than assumed because the two come from separate solves, and a
  disagreement is exactly the failure this design is most exposed to.  `:fixed` is
  excluded from the first: it is known-true background that is assumed by every model
  and never an assumption the labeling chooses over."
  [program labeled classification]
  (let [forced   (remove (:fixed program) (:true classification))
        missing  (remove labeled forced)
        excluded (filter labeled (:false classification))]
    (when (or (seq missing) (seq excluded))
      (throw (ex-info (str "labeling disagrees with its own brave/cautious classification,"
                           " which two solves over one program produced: "
                           (pr-str (vec missing)) " holds in every optimum and the"
                           " labeling drops it, " (pr-str (vec excluded))
                           " holds in no optimum and the labeling keeps it")
                      {:type :labeling-inconsistent
                       :missing-true (vec missing)
                       :kept-false   (vec excluded)
                       :labeled      (vec labeled)
                       :classification classification})))))

(defn- solved-labeling
  "The assumptions one optimal answer set keeps — `program`'s assumptions minus what
  the labeling solver gives up.

  **Sourced from the solve, not from the TMS**, which is the opposite of
  `label-context` below and for a reason that is the same principle either way:
  report what actually decided it.  A tie `settle` arbitrated was decided by the
  engine, so the TMS holds the answer and re-solving risks disagreeing with the
  engine's own belief.  A dilemma `settle` declined was decided by nobody — **both
  sides are IN** — so reading current belief would copy both halves of the
  contradiction into the labeling and recreate the dilemma one level down.  Here the
  solve is the only thing that decides.

  So a solve that decided nothing is refused rather than read.  `edge-solver` hands an
  interrupted or failed solve back as `{:defeat #{} … :error e}` instead of degrading or
  throwing, and an empty defeat set is otherwise a perfectly good answer — *keep
  everything* — which is precisely the reading that would materialize both halves of a
  dilemma into one world.  `:error` is the bit that tells the two apart, and raising it
  here is what makes an imperative refuse with `:solver-failed`."
  [kb program]
  (let [{:keys [defeat error]} (solve-types/solve (labeling-solver kb) program)]
    (when error (throw error))
    (let [given-up (set defeat)]
      (into #{} (remove given-up) (:assumptions program)))))

(defn label-dilemmas
  "Classify the dilemmas `kb` currently holds, then materialize one optimal labeling
  of them into `ctx`.  Returns
  `{:context ctx :handles [h ...] :classification {...} :program p}`; the handles are
  empty when the KB holds no dilemma.

  The four steps run in an order this fixes so a caller cannot get it wrong — in
  particular **classification is taken before materialization**, because materializing
  entrenches.  What it writes are ordinary assertions, and an assertion is evidence:
  the recorded side lands in a second nogood against its rival, so a tie that
  classifies `:supportable` on both sides classifies `:true`/`:false` once labeled.
  That is what recording a choice means, not a bug — but it means the classification
  has to be read first, and making one call do both is how that stops being something
  to remember.

  The Program is recorded in `kb`'s `:program` slot, so `last-program` and `classify`
  answer about this labeling afterwards.  `settle` never writes that slot for a
  dilemma (it builds no Program for one), so nothing is being overwritten.

  **`ctx` sees `base`, and the labeling is recorded by strengthening.**  Each kept
  assumption is re-asserted inside `ctx` at `:monotonic`, so `ctx` is a real world: the
  uncontested background is inherited through `genlCx` (reachable with `ask` / `lookup`
  at level 3 and above — note `sentexes-matching` is context-exact and will not show
  it), and the contested atoms are decided within it.  Nothing needs to be said about
  the side that lost: the strengthened copy out-ranks it, and `decide-nogood` defeats
  the strictly weaker member.

  **This commits, and the commitment is scoped to `ctx`.**  The strengthened copy and
  the losing side form a nogood whose vantage is `ctx`, so the losing side is defeated at
  `ctx` and below and nowhere else (docs/nmtms.md, \"A defeat is scoped to its
  vantage\").  The base keeps believing both sides and reporting its dilemma.  The
  engine's refusal to arbitrate holds: it still refuses *on its own*, and commits inside
  `ctx` only when a caller writes the imperative (docs/labeling.md).

  So rival labelings stand **side by side**, as sibling contexts: each labeling decides
  the dilemma in its own context, and retracting the returned handles revives the
  dilemma inside that context.

  Additive, so no `!`: this creates a context and asserts into it, and retracting the
  returned handles undoes it — including the commitment."
  [kb ctx base]
  (if-let [program (dilemma-program kb)]
    (let [classification (classify-program program)
          keep-set       (solved-labeling kb program)]
      ;; the two came from separate solves; refuse to commit if they disagree
      (check-agrees program keep-set classification)
      (reset! (reasoning/program kb) program)
      (wiring/assert-sentence kb (list 'genlCx ctx base) base {:strength :monotonic})
      {:context ctx
       :program program
       :classification classification
       :handles (into [] (keep (fn [h]
                                 (when-let [s (p/get-sentex (:records kb) h)]
                                   ;; :monotonic is the whole mechanism — a copy at
                                   ;; :default would merely tie with the side it is
                                   ;; supposed to beat, and report a second dilemma
                                   ;; instead of deciding the first
                                   (wiring/assert-sentence kb (:sentence s) ctx {:strength :monotonic})
                                   (kb/find-sentex-handle kb (:sentence s) ctx))))
                      ;; sorted by content, never by handle: handles are allocated in
                      ;; assertion order, so iterating them would make *which* copy is
                      ;; created first depend on the order the knowledge arrived — the
                      ;; content-key built once per member, not per comparison
                      (nm/sort-by-content-key #(solve/content-key program %) compare keep-set))})
    ;; nothing contested: no program, no context, nothing to record.  Minting an empty
    ;; labeling context would assert that a choice was made where none was.
    {:context ctx :program nil :handles []
     :classification {:true #{} :supportable #{} :false #{}}}))

(defn label-context
  "Mint `ctx` as a specialization of `base` holding the labeling the engine committed
  to, and return `ctx`.

  The labeling is read from the TMS — the contested assumptions it currently believes
  — not from a fresh solve, so the context is guaranteed to say what the engine
  actually decided rather than what a second solve might have chosen.

  `ctx` sees `base` through `genlCx`, so it inherits the whole KB; what it adds
  is an explicit, queryable record of one arbitration. Two labelings of the same tie
  can therefore be built as sibling contexts and compared.

  **This entrenches the labeling, so classify before you label.** What it writes are
  ordinary assertions, and an assertion is evidence: the recorded side now sits in a
  second nogood against its rival, which makes defeating the rival strictly cheaper
  than defeating the record. A tie that classified as `:supportable` on both sides
  will classify as `:true`/`:false` afterwards. Belief does not move — the losing
  side was already OUT — but it stops *looking* arbitrary, because it no longer is:
  something now asserts the choice. Retracting the returned handles restores the
  open tie.

  **The context is minted whether or not there was a tie**, and `label-dilemmas` is
  deliberately the other way round. With no recorded `Program` — a KB the engine never
  arbitrated in, or a dilemma it declined — the `genlCx` edge is written and `:handles`
  comes back empty: a specialization that sees its base and records nothing is what \"the
  engine committed to nothing\" materializes as, and it is the honest shape for a caller
  that asked to see one arbitration. `label-dilemmas` *makes* a choice rather than
  reporting one, so minting a context for a choice it did not make would assert that one
  happened.

  Additive, so no `!`: this creates a context and asserts into it. The labeling is
  undone by retracting the returned handles; the `genlCx` edge is a premise of its own
  and is retracted as one."
  [kb ctx base]
  (let [tms (reasoning/tms kb)
        program @(reasoning/program kb)
        ;; content order, as `label-dilemmas` orders the same set: `:assumptions` is
        ;; a handle set, and hash iteration would mint the copies — and return the
        ;; `:handles` a caller retracts — in an order that tracks assertion order
        believed (nm/sort-by-content-key #(solve/content-key program %) compare
                                         (filter #(jtms/in? tms %) (:assumptions program)))]
    (wiring/assert-sentence kb (list 'genlCx ctx base) base {:strength :monotonic})
    {:context ctx
     :handles (into [] (keep (fn [h]
                               (when-let [s (p/get-sentex (:records kb) h)]
                                 (wiring/assert-sentence kb (:sentence s) ctx nil))))
                    believed)}))
