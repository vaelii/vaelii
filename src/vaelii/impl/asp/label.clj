;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.label
  "Brave/cautious classification and the two labeling writers.  `classify` reads the
  `Program` the KB last recorded; `classify-local` and `classify-datum` classify the
  current dilemmas from the JTMS dependency graph with no backend.  `label-context`
  records the labeling the engine committed to; `label-dilemmas` (`do/labeling`) commits
  one inside a context.  See docs/asp.md and docs/labeling.md."
  (:require
   [vaelii.impl.asp.edge :as edge]
   [vaelii.impl.asp.solver :as solver]
   [vaelii.impl.clashes :as clashes]
   [vaelii.impl.config :as config]
   [vaelii.impl.except :as exc]
   [vaelii.impl.jtms :as jtms]
   [vaelii.impl.kb :as kb]
   [vaelii.impl.naming :as nm]
   [vaelii.impl.observe :as observe]
   [vaelii.impl.protocols :as p]
   [vaelii.impl.solve :as solve]
   [vaelii.impl.types.reasoning :as reasoning]
   [vaelii.impl.types.solve :as solve-types]
   [vaelii.impl.wiring :as wiring]))

;; `asp.edge`'s, re-exported for the KB-level callers
(def classify-program edge/classify-program)

(defn classify
  "Classify the program `kb` last recorded (`last-program`): `{:true #{handle}
  :supportable #{handle} :false #{handle}}`, all empty when none is recorded.  The
  classification `label-dilemmas` recorded on the program is read back, not recomputed."
  [kb]
  (if-let [program @(reasoning/program kb)]
    (or (:classification program) (classify-program program))
    {:true #{} :supportable #{} :false #{}}))

;; ---- the dilemma bridge -------------------------------------------------
;; A `Program` built from what `contradictions` reports (docs/labeling.md, "Why a caller
;; has to ask").

(defn- sides-content
  "What each side of each dilemma asserts, keyed by handle."
  [dilemmas]
  (into {} (mapcat (fn [d] (map (juxt :handle #(select-keys % [:sentence :context]))
                                (:sides d))))
        dilemmas))

(defn- dilemmas-program
  "One `Program` over the dilemmas `ds` (`clashes/contradictions-of` entries)."
  [ds]
  (solve/program (into #{} (mapcat :nogood) ds)
                 (mapv #(select-keys % [:nogood :priority :sentence]) ds)
                 (sides-content ds)))

(defn dilemma-program
  "One `Program` covering every dilemma `kb` currently reports, or nil if it reports
  none: one program, so a handle contested in two dilemmas is kept or given up once."
  [kb]
  (some-> (seq (clashes/ranked (clashes/contradictions-of kb))) dilemmas-program))

(defn- cluster-indices
  "Partition `[0 n)` into the connected components of `edges`, a seq of `[i j]` index pairs,
  returned as a seq of index sets (union-find)."
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
  optimal resolution (docs/labeling.md, \"The solve-free bracket\").  Returns nil when the
  subsets examined would exceed `VAELII_CLASSIFY_RESOLUTION_BUDGET`; each size's binomial
  count is checked before its subsets are generated."
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

(defn- local-analysis
  "The JTMS reading of the dilemma reports `ds` behind `classify-local` and
  `label-dilemmas`, or nil when no member of `ds` is `:default`: `:classification`
  (`classify-local`'s answer), `:holds?` (is a datum believed with a set forced OUT),
  `:optima` (each enumerated cluster's optimal resolutions) and `:unenumerated` (the
  members of the clusters it could not enumerate)."
  [kb ds]
  (let [tms     (reasoning/tms kb)
        nogoods (into []
                      (keep (fn [ng]
                              (let [ms (into #{}
                                             (filter #(= :default (jtms/defeat-class tms %)))
                                             (:nogood ng))]
                                (when (seq ms) ms))))
                      ds)]
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
            ;; every believed datum some dilemma moves, and the datums each dilemma moves;
            ;; a sentex placed for a nogood records the dilemma and is classified with none
            placed?   (fn [d] (let [ss (jtms/supports tms d)]
                                (and (seq ss)
                                     (every? #(= exc/nogood-informant
                                                 (:informant (jtms/justification tms %)))
                                             ss))))
            dependent (into #{} (remove placed?) (moved (reduce into #{} nogoods)))
            dep       (mapv moved nogoods)
            ;; datum -> the nogood indices whose forcing moves it (a nogood's own members
            ;; among them, since forcing a nogood OUT moves its members)
            touch     (persistent!
                       (reduce (fn [m i]
                                 (reduce (fn [m d] (assoc! m d (conj (get m d #{}) i)))
                                         m (dep i)))
                               (transient {}) (range n)))
            ;; two nogoods couple when forcing one moves a member of the other; the union
            ;; runs through `touch`, linear in the members rather than quadratic in the nogoods
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
            ;; the joint resolutions of `cs`, the clusters that move a datum: the product of
            ;; their optima as forced sets, nil when a cluster is unenumerated or the product
            ;; exceeds `max-optima`
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
            grouped (group-by classify-one dependent)
            ;; members of a cluster `min-resolutions` did not enumerate
            unenumerated (into #{}
                               (comp (remove optima) (mapcat #(map nogoods %)) cat)
                               clusters)
            ;; ... of which those whose cluster no member's forcing moves another member
            ;; of: a flat `Program` over that cluster is exact
            refinable (into #{}
                            (comp (remove optima)
                                  (map (fn [c] (reduce into #{} (map nogoods c))))
                                  (filter (fn [ms]
                                            (every? (fn [m] (every? #(or (= m %) (not (ms %)))
                                                                    (moved #{m})))
                                                    ms)))
                                  cat)
                            clusters)]
        {:classification {:true        (into #{} (:true grouped))
                          :supportable (into #{} (:supportable grouped))
                          :false       (into #{} (:false grouped))
                          :refinable   refinable}
         :holds?         holds?
         :optima         (into [] (keep optima) clusters)
         :unenumerated   unenumerated}))))

(defn- believed-classes
  "`local-analysis`' classification with each handle `hidden?` answers true for removed from
  the three classes."
  [analysis hidden?]
  (when-let [cls (:classification analysis)]
    (reduce (fn [m k] (update m k #(into #{} (remove hidden?) %)))
            cls [:true :supportable :false])))

(defn classify-local
  "The skeptical/credulous classification of the KB's current dilemmas, or with `context`
  of the dilemmas a reader there reads (`clashes/contradictions-at`), from the JTMS
  dependency graph with no backend.  Returns `{:true #{} :supportable #{} :false #{}
  :refinable #{}}`, or nil when there is no dilemma: a datum `context` believes, or with
  none its own context, is `:true` when every optimal resolution keeps it, `:supportable`
  when some do, `:false` when none do.  `:refinable` holds the members of the unenumerated
  clusters whose members move none of each other, where a `Program` is exact.  A datum
  past a cap is `:supportable`.  See docs/labeling.md, \"The solve-free bracket\"."
  ([kb] (believed-classes (local-analysis kb (clashes/contradictions-of kb))
                          #(not (exc/believed-own? kb %))))
  ([kb context] (believed-classes (local-analysis kb (clashes/contradictions-at kb context))
                                  (or (exc/belief-hidden-fn kb context) (constantly false)))))

(defn- member-components
  "The dilemmas `ds` grouped into member components: two dilemmas share one when they share
  a member, directly or through a chain.  Returns a vector of dilemma vectors, each in `ds`
  order."
  [ds]
  (let [ds    (vec ds)
        edges (second
               (reduce (fn [[first-seen es] i]
                         (reduce (fn [[first-seen es] m]
                                   (if-let [j (first-seen m)]
                                     [first-seen (conj es [i j])]
                                     [(assoc first-seen m i) es]))
                                 [first-seen es] (:nogood (ds i))))
                       [{} []] (range (count ds))))]
    (mapv #(mapv ds (sort %)) (cluster-indices (count ds) edges))))

(defn- component-classifier
  "A backend's per-component classification of the dilemmas `ds` (`member-components`,
  `classify-program`): a function of a member handle, classifying the component it is in
  once and holding the answer."
  [ds]
  (let [cs           (member-components ds)
        component-of (into {} (for [i (range (count cs)), d (cs i), m (:nogood d)] [m i]))
        classified   (atom {})]
    (fn [h]
      (when-let [i (component-of h)]
        (or (get @classified i)
            (get (swap! classified assoc i (classify-program (dilemmas-program (cs i)))) i))))))

(defn- class-of
  "`h`'s class in the classification `cls`, or nil."
  [cls h]
  (some #(when (contains? (get cls %) h) %) [:true :supportable :false]))

(defn- classification
  "What `classify-datum` reads at `context`, resident on the KB's `:qcn` atom and rebuilt
  when the change clock moves (`observe/cached`), keyed on the context and on whether a
  backend is reachable: `classify-local`'s answer over the dilemmas `context` reads, and
  with a backend a `component-classifier` for the members it leaves `:refinable`."
  [kb context]
  (let [backend? (solver/available?)]
    (observe/cached (:clock kb) (reasoning/qcn kb) [::classification context backend?]
                    (fn [_]
                      {:local   (classify-local kb context)
                       :backend (when backend?
                                  (component-classifier
                                   (clashes/ranked (clashes/contradictions-at kb context))))}))))

(defn classify-datum
  "Handle `h`'s class over the optimal labelings of the dilemmas a reader at `context`
  reads: `:true`, `:supportable` or `:false`, or nil when no such dilemma classifies it.
  `classify-local`'s answer, with a backend's member-component classification for a
  `:refinable` member.  The `(bravely S)` / `(cautiously S)` prover reads it."
  [kb h context]
  (let [{:keys [local backend]} (classification kb context)]
    (if (and backend (contains? (:refinable local) h))
      (class-of (backend h) h)
      (class-of local h))))

(defn- labeling-solver
  "The solver a labeling solve uses: `edge/edge-solver` whenever a backend is reachable,
  else the one installed on the KB (docs/labeling.md, \"The labeling and its
  classification must agree\")."
  [kb]
  (if (solver/available?) edge/edge-solver @(:solver kb)))

(defn- check-agrees
  "Throw `:labeling-inconsistent` unless `:true ⊆ labeled` and `:false ∩ labeled = ∅`,
  `program`'s `:fixed` handles excepted from the first."
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

(defn- solved-defeat
  "The assumptions one optimal answer set of `program` gives up, from `labeling-solver`;
  `label-dilemmas` reads it for the clusters `classify-local` does not enumerate.  A solve
  that decided nothing returns an `:error`, which this throws."
  [kb program]
  (let [{:keys [defeat error]} (solve-types/solve (labeling-solver kb) program)]
    (when error (throw error))
    (set defeat)))

(defn- local-labeling
  "One optimal labeling of the dilemmas `ds`, read through `local-analysis`: `{:keep
  #{h} :classification {...}}` over `program`'s assumptions.

  Each enumerated cluster contributes the optimal resolution whose members sort first by
  content (`solve/content-key`), so the choice is order-independent; a cluster
  `classify-local` did not enumerate contributes the defeat set of a solve over its
  dilemmas (`solved-defeat`).  An assumption is kept when it is believed with that union
  forced OUT, so a member a defeat drops by cascade is dropped with it.  The
  classification is `classify-local`'s over the assumptions, a `:refinable` member's
  from one backend classification of the refinable dilemmas when a backend is reachable,
  and `program`'s `:fixed` background `:true`."
  [kb ds program]
  (let [{:keys [classification holds? optima unenumerated]}
        (or (local-analysis kb ds)
            ;; no `:default` member anywhere: nothing to enumerate, the solve decides all
            (let [tms (reasoning/tms kb)]
              {:holds?       (fn [forced h] (and (not (forced h)) (jtms/in? tms h)))
               :unenumerated (into #{} (mapcat :nogood) ds)}))
        refinable (:refinable classification)
        ;; one classification over every refinable dilemma, before the labeling solve: the
        ;; two solves docs/asp.md counts, whatever the number of components
        refined  (when (solver/available?)
                   (some->> (seq (filterv #(some refinable (:nogood %)) ds))
                            dilemmas-program
                            classify-program))
        grouped  (group-by #(or (when (contains? refinable %) (class-of refined %))
                                (class-of classification %))
                           (:assumptions program))
        content  (fn [s] (into [] (sort (map #(solve/content-key program %) s))))
        chosen   (into #{} (mapcat #(first (nm/sort-by-content-key content compare %))) optima)
        residual (filterv #(some unenumerated (:nogood %)) ds)
        forced   (cond-> chosen
                   (seq residual) (into (solved-defeat kb (dilemmas-program residual))))]
    {:keep           (into #{} (filter #(holds? forced %)) (:assumptions program))
     :classification {:true        (into (set (:fixed program)) (:true grouped))
                      :supportable (into #{} (:supportable grouped))
                      :false       (into #{} (:false grouped))}}))

(defn label-dilemmas
  "`do/labeling`: classify the dilemmas `kb` holds and commit one optimal labeling of them
  inside `ctx`, both read off `local-labeling`.  Records the program, carrying the
  classification and the kept assumptions (`:keep`), in `kb`'s `:program` slot; writes
  `(genlCx ctx base)` and a `:monotonic` copy in `ctx` of each kept assumption, in content
  order.  Throws `:labeling-inconsistent` when the two disagree.  Returns `{:context ctx
  :handles [h ...] :classification {...} :program p}`, the handles empty and nothing
  written when the KB holds no dilemma.  See docs/labeling.md, \"`(do/labeling Ctx)`\"."
  [kb ctx base]
  (if-let [ds (seq (clashes/ranked (clashes/contradictions-of kb)))]
    (let [program (dilemmas-program ds)
          {keep-set :keep classification :classification} (local-labeling kb ds program)]
      (check-agrees program keep-set classification)
      (reset! (reasoning/program kb)
              (assoc program :classification classification :keep keep-set))
      (wiring/assert-sentence kb (list 'genlCx ctx base) base {:strength :monotonic})
      {:context ctx
       :program program
       :classification classification
       :handles (into [] (keep (fn [h]
                                 (when-let [s (p/get-sentex (:records kb) h)]
                                   (wiring/assert-sentence kb (:sentence s) ctx {:strength :monotonic})
                                   (kb/find-sentex-handle kb (:sentence s) ctx))))
                      ;; content order, never handle order
                      (nm/sort-by-content-key #(solve/content-key program %) compare keep-set))})
    {:context ctx :program nil :handles []
     :classification {:true #{} :supportable #{} :false #{}}}))

(defn label-context
  "Write `(genlCx ctx base)` and, in `ctx`, a `:monotonic` copy of each assumption
  `label-dilemmas` kept in the recorded `Program` (`:keep`) that its own context believes,
  in content order.
  Returns `{:context ctx :handles [h ...]}`, the handles empty with no recorded program;
  the edge is written either way.  See docs/asp.md, \"Labeling contexts\"."
  [kb ctx base]
  (let [program @(reasoning/program kb)
        ;; content order, never the handle set's hash order
        believed (nm/sort-by-content-key #(solve/content-key program %) compare
                                         (filter #(exc/believed-own? kb %) (:keep program)))]
    (wiring/assert-sentence kb (list 'genlCx ctx base) base {:strength :monotonic})
    {:context ctx
     :handles (into [] (keep (fn [h]
                               (when-let [s (p/get-sentex (:records kb) h)]
                                 (wiring/assert-sentence kb (:sentence s) ctx
                                                         {:strength :monotonic}))))
                    believed)}))
