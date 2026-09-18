;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.caches
  "What the rebuildable caches hold, and what a KB says about its own content — the two
  measurements a large corpus is needed for, taken in one JVM because both of them are
  behind the same expensive load.

  **The cache side.**  A running KB holds four kinds of derived structure that could in
  principle be evicted, and they are not equally interesting.  Every one of them except
  two is bounded by a *fixed cap* — the hot-record LRU at `vaelii.disk.cache`, `observe`
  at 256, the literal cache at 4,096, the STP closure at 256, the QCN passes at 256, its
  decode table at 8,192, its compiled algebras at 64, and the taxonomy's *scoped* closure
  level at `*scoped-memo-budget*`.  A fixed cap makes the resident bytes a function of the
  cap and the entry size, never of the corpus, so it is computable without a corpus at
  all.  The `memoize`d closures are not caches in this sense either: every call site
  builds its memo inside a function body and drops it on return, so nothing survives the
  call that made it.

  That leaves exactly two structures whose population grows with what is loaded, and they
  are what this harness measures:

  * `taxonomy` `:closure-memo`, **unscoped** level — one reach set per `[relation
    direction node]` ever read, invalidated by a `:gen` bump rather than by size.  Its
    population is bounded by the vocabulary and its *bytes* by the structure of the
    hierarchy, since a memo of sets retains the sets.
  * `taxonomy` `:vis-index` — one interned visible-context set per `[relation context]`,
    so it is bounded by the context census rather than by the read count.

  Retained size, not shallow: a map of sets whose shallow size is a few hundred bytes can
  retain megabytes, and reporting the shallow figure would understate exactly the
  structure the question is about.

  **The content side.**  Four questions about the knowledge rather than the engine —
  which rules never fire, how skewed the predicate extents are, how deep the rule graph
  reaches, and how much of the taxonomy is connected to anything.  The firing count reads
  the JTMS `:consequences` adjacency filtered by `:informant`, which is the same walk
  `restrength-informant*` does and costs O(rules + firings); nothing scans `:justs`.

  One thing the firing count means and is easy to misread: it counts **currently
  supported** firings, not firings-ever.  On a backward-heavy corpus almost nothing is
  supported until something asks a question, so the number before a query workload
  describes the workload's absence rather than the rules.  Both readings are reported.

  Run: `lein bench-caches quick`            — the starter ontology, to check the harness
       `lein bench-caches <corpus-dir>`     — a converted corpus (`:cyc-corpus`)
       `lein bench-caches <corpus-dir> full`— the same at the `:full` profile

  A corpus run wants a heap, and `:bench` pins `-Xmx6g` that an environment `JVM_OPTS`
  loses to outright.  `scripts/run-bench-caches.sh` is the driver: it edits the option
  vector on the way past and logs the run."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.core :as v]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.host.starter :as starter]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- reporting ----------------------------------------------------------

(defn- ms [t0] (/ (- (System/nanoTime) t0) 1e6))

(defn- mb [^long bytes] (/ bytes 1048576.0))

(defn- banner [s]
  (println)
  (println (str "── " s " " (apply str (repeat (max 0 (- 76 (count s))) "─")))))

(defn- heap-live
  "Post-GC live heap, summed over the pools' collection usage.  Not
  `getHeapMemoryUsage().getUsed()`, which under a lazy collector counts uncollected
  floating garbage and sits far above the live set."
  ^long []
  (reduce + 0 (for [^java.lang.management.MemoryPoolMXBean p
                    (java.lang.management.ManagementFactory/getMemoryPoolMXBeans)
                    :when (= java.lang.management.MemoryType/HEAP (.getType p))
                    :let [u (.getCollectionUsage p)]
                    :when u]
                (.getUsed u))))

(defn- settle-heap! []
  (System/gc)
  (Thread/sleep 200)
  (System/gc)
  (Thread/sleep 200))

;; ---- the two structures whose population is not capped -------------------

(defn- closure-memo [kb] @(:closure-memo @(reasoning/taxonomy kb)))
(defn- vis-index    [kb] @(:vis-index    @(reasoning/taxonomy kb)))

(defn- memo-census
  "Entry counts inside the closure memo, split by level.  The unscoped level is the one
  with no cap; the scoped level is capped per relation by `*scoped-memo-budget*`."
  [kb]
  (let [m (closure-memo kb)]
    (reduce (fn [acc [rel e]]
              (-> acc
                  (update :relations conj rel)
                  (update :unscoped + (count (:fwd e)) (count (:rev e)))
                  (update :vissets + (count (:scoped e)))
                  (update :scoped + (reduce + 0 (for [[_ lv] (:scoped e)]
                                                  (+ (count (:fwd lv)) (count (:rev lv))))))))
            {:relations #{} :unscoped 0 :scoped 0 :vissets 0}
            m)))

(defn- cache-sizes
  "Retained bytes per uncapped structure, plus the capped ones for scale."
  [kb]
  (settle-heap!)
  {:closure-memo (postings/retained [(closure-memo kb)])
   :vis-index    (postings/retained [(vis-index kb)])
   :literal      (:size (lc/stats kb))
   :heap-live    (heap-live)})

;; ---- reading 1: what the caches hold after a read workload ---------------

(defn- report-sizes [kb label]
  (let [c (cache-sizes kb)
        n (memo-census kb)]
    (println (format "  %-22s closure-memo %8.2f MB (%,d unscoped / %,d scoped over %,d vissets, %d relations)"
                     label (mb (:closure-memo c)) (:unscoped n) (:scoped n)
                     (:vissets n) (count (:relations n))))
    (println (format "  %-22s vis-index    %8.2f MB   literal-cache %,d entries   live heap %8.2f MB"
                     "" (mb (:vis-index c)) (:literal c) (mb (:heap-live c))))
    (assoc c :census n)))

;; ---- reading 2: does anything grow with the query count? ----------------

(defn- taxonomy-sweep!
  "A read workload that is all taxonomy: `genls` and `specs` for `n` terms, from `ctx`.
  This is the workload that populates the closure memo, so it is the one that would
  expose an unbounded level."
  [kb terms ctx]
  (doseq [t terms]
    (v/genls kb t ctx)
    (v/specs kb t ctx)))

(defn- growth-probe
  "Sample the memo's population and retained bytes over a lengthening query stream.  A
  level bounded by the vocabulary plateaus once the vocabulary is covered; a level
  bounded by nothing keeps climbing as the same terms are re-read from more contexts."
  [kb terms ctxs rounds]
  (banner "ops-5 reading 2 — growth over a query stream")
  (println (format "  %,d terms × %,d contexts × %d rounds" (count terms) (count ctxs) rounds))
  (println)
  (println (format "  %-8s %-14s %-14s %-14s %s" "round" "unscoped" "scoped" "vissets" "retained MB"))
  (doseq [r (range 1 (inc rounds))]
    (doseq [ctx ctxs] (taxonomy-sweep! kb terms ctx))
    (let [n (memo-census kb)
          _ (settle-heap!)
          b (postings/retained [(closure-memo kb)])]
      (println (format "  %-8d %-14s %-14s %-14s %.2f"
                       r (format "%,d" (:unscoped n)) (format "%,d" (:scoped n))
                       (format "%,d" (:vissets n)) (mb b))))))

;; ---- reading 3: what a full clear costs to rebuild -----------------------

(defn- rebuild-cost
  "Time the same taxonomy sweep warm, then after clearing the memo cold.  A governor that
  evicts something costing seconds to rebuild has made the pause it was avoiding."
  [kb terms ctx]
  (banner "ops-5 reading 3 — rebuild cost after a full clear")
  (taxonomy-sweep! kb terms ctx)                        ; warm
  (let [t0 (System/nanoTime)
        _  (taxonomy-sweep! kb terms ctx)
        warm (ms t0)
        _  (reset! (:closure-memo @(reasoning/taxonomy kb)) {})
        t1 (System/nanoTime)
        _  (taxonomy-sweep! kb terms ctx)
        cold (ms t1)]
    (println (format "  warm sweep %8.1f ms      cold sweep %8.1f ms      ratio %.1f×"
                     warm cold (if (pos? warm) (/ cold warm) 0.0)))
    (println (format "  %,d terms, so %.3f ms/term cold — the pause a wholesale clear buys back"
                     (count terms) (/ cold (max 1 (count terms)))))
    {:warm warm :cold cold}))

;; ---- ops-6: which rules never fire --------------------------------------

(defn- rule-handles
  "Every stored rule's handle, in one pass over the record store."
  [kb]
  (let [recs (:records kb)]
    (into [] (filter #(some-> (p/get-sentex recs %) rules/rule?)) (p/sentex-ids recs))))

(defn- firing-census
  "Per rule handle: how many currently-supported justifications name it as informant.
  Reads the node's `:consequences` adjacency — the same candidate set
  `restrength-informant*` uses — and never scans `:justs`."
  [kb handles]
  (let [state @(reasoning/tms kb)
        justs (:justs state)
        nodes (:nodes state)
        in    (:in state #{})]
    (reduce (fn [acc h]
              (let [jids  (filter #(= h (:informant (get justs %)))
                                  (get-in nodes [h :consequences] #{}))
                    n     (count jids)
                    live  (count (filter #(contains? in (:consequence (get justs %))) jids))]
                (cond
                  (zero? n)     (update acc :never conj h)
                  (zero? live)  (update acc :all-defeated conj h)
                  :else         (-> acc (update :fired conj h)
                                    (update :firings + n)))))
            {:never [] :all-defeated [] :fired [] :firings 0}
            handles)))

(defn- report-firings [kb handles label]
  (let [c (firing-census kb handles)
        t (count handles)]
    (println (format "  %-24s %,d rules — %,d never fired, %,d fired but every conclusion defeated, %,d live (%,d firings)"
                     label t (count (:never c)) (count (:all-defeated c))
                     (count (:fired c)) (:firings c)))
    c))

;; ---- ops-6: extent skew --------------------------------------------------

(defn- gini
  "Gini over the extent sizes.  0 when every predicate is the same size, → 1 when one
  holds everything."
  [counts]
  (let [xs (vec (sort counts))
        n  (count xs)
        s  (reduce + 0 xs)]
    (if (or (zero? n) (zero? s))
      0.0
      (double (/ (- (* 2 (reduce + 0 (map-indexed (fn [i x] (* (inc i) x)) xs)))
                    (* (inc n) s))
                 (* n s))))))

(defn- extent-skew
  "Stored counts per predicate, off the count-aware trie — one O(1) read each, so this is
  O(predicates) and not O(sentexes).  Believed counts would make it the latter."
  [kb]
  (banner "ops-6 — predicate extent skew")
  (let [preds  (into [] (filter #(#{:predicate :type} (v/term-role %))) (v/terms kb))
        counts (into {} (map (fn [p] [p (v/count-with-functor kb p)])) preds)
        vals*  (vec (remove zero? (vals counts)))
        total  (reduce + 0 vals*)
        bucket (fn [n] (if (zero? n) 0 (int (Math/floor (Math/log10 (double n))))))
        hist   (frequencies (map bucket vals*))
        top    (take 15 (sort-by (comp - val) counts))]
    (println (format "  %,d predicates, %,d with an extent, %,d stored facts, Gini %.4f"
                     (count preds) (count vals*) total (gini vals*)))
    (println "  order-of-magnitude buckets (10^k ≤ extent < 10^k+1):")
    (doseq [k (sort (keys hist))]
      (println (format "    10^%-2d  %,8d predicates" k (get hist k))))
    (println "  the heaviest:")
    (doseq [[p n] top]
      (println (format "    %,10d  %s" n p)))
    {:gini (gini vals*) :predicates (count preds) :with-extent (count vals*) :total total}))

;; ---- ops-6: taxonomy coverage -------------------------------------------

(defn- taxonomy-coverage
  "Two numbers, not one: the fraction of terms with any `genl` edge, and the fraction
  reachable from a root.  A term with an edge into a disconnected island is covered by
  the first and not the second, and the gap between them is the finding.

  The root is **found, not assumed** — `thing` is this engine's, and a converted corpus
  brings its own.  Whatever type the most others reach is the one reported against, so
  the number means the same on a corpus that never heard of `thing`."
  [kb ctx]
  (banner "ops-6 — taxonomy coverage")
  (let [terms  (vec (v/types kb))
        n      (count terms)
        ups    (into {} (map (fn [t] [t (set (v/genls kb t ctx))])) terms)
        edged  (into [] (filter #(or (seq (rest (get ups %)))
                                     (seq (rest (v/specs kb % ctx))))) terms)
        reach  (frequencies (mapcat #(disj (get ups %) %) terms))
        [root cnt] (or (first (sort-by (comp - val) reach)) [nil 0])]
    (println (format "  %,d types — %,d with a genl edge (%.1f%%)"
                     n (count edged) (* 100.0 (/ (count edged) (max 1 n)))))
    (println (format "  most-reached type is `%s`, reached by %,d (%.1f%%)"
                     root cnt (* 100.0 (/ cnt (max 1 n)))))
    (println (format "  the gap — edged but not reaching it — is %,d types in disconnected islands"
                     (max 0 (- (count edged) cnt))))
    {:types n :edged (count edged) :root root :rooted cnt}))

;; ---- ops-6: chain depth over the rule graph ------------------------------

(defn- rule-graph
  "consequent functor → the antecedent functors, over every stored rule."
  [kb handles]
  (let [recs (:records kb)]
    (reduce (fn [g h]
              (let [sx (p/get-sentex recs h)
                    c  (some-> (:consequent sx) nm/functor)
                    as (into #{} (keep nm/functor) (:antecedent sx))]
                (if c (update g c (fnil into #{}) as) g)))
            {} handles)))

(defn- sccs
  "Tarjan, iterative — the rule graph of a real KB is cyclic in the ordinary case
  (`genl` transitivity alone makes it so), so the depth pass must treat a component as
  one node.  Memoizing the node and not the path is what keeps this from re-exploring a
  reachable subgraph along every path."
  [g]
  (let [nodes (into #{} (concat (keys g) (mapcat val g)))]
    (loop [stack (vec nodes), idx {}, low {}, on #{}, s [], out [], counter 0, work []]
      (cond
        (seq work)
        (let [[v state] (peek work)]
          (case state
            :enter
            (if (contains? idx v)
              (recur stack idx low on s out counter (pop work))
              (recur stack (assoc idx v counter) (assoc low v counter) (conj on v)
                     (conj s v) out (inc counter)
                     (into (conj (pop work) [v :exit])
                           (map (fn [w] [w :enter])) (get g v #{}))))
            :exit
            (let [lo (reduce (fn [a w] (if (contains? on w) (min a (get low w (get idx w))) a))
                             (get low v) (get g v #{}))
                  low (assoc low v lo)]
              (if (= lo (get idx v))
                (let [[comp s'] (split-with #(not= % v) (reverse s))
                      comp      (conj (vec comp) v)]
                  (recur stack idx low (reduce disj on comp)
                         (vec (reverse (rest s'))) (conj out (set comp)) counter (pop work)))
                (recur stack idx low on s out counter (pop work))))))
        (seq stack)
        (recur (pop stack) idx low on s out counter [[(peek stack) :enter]])
        :else out))))

(defn- chain-depth
  "Depth per condensed component, then the distribution over rules.  Bounded and
  cancellable — the failure this guards against is not incorrectness, it is five hours."
  [kb handles]
  (banner "ops-6 — chain depth over the rule graph")
  (let [t0   (System/nanoTime)
        g    (rule-graph kb handles)
        comps (sccs g)
        of   (into {} (for [c comps, n c] [n c]))
        cg   (reduce (fn [m c]
                       (assoc m c (into #{} (comp (mapcat #(get g % #{}))
                                                  (keep of)
                                                  (remove #(= % c)))
                                        c)))
                     {} comps)
        ;; Longest path over the condensation, on an **explicit** stack.  The recursive
        ;; spelling is the natural one and it stack-overflows just past a thousand-deep
        ;; chain — measured, not feared — which a rule graph is entitled to have.
        ds   (loop [todo (vec comps), depths {}]
               (if-let [c (peek todo)]
                 (cond
                   (contains? depths c) (recur (pop todo) depths)
                   :else
                   (let [ss    (get cg c)
                         undone (into [] (remove #(contains? depths %)) ss)]
                     (if (seq undone)
                       (recur (into todo undone) depths)
                       (recur (pop todo)
                              (assoc depths c (if (seq ss)
                                                (inc (reduce max 0 (map depths ss)))
                                                0))))))
                 depths))
        hist (frequencies (vals ds))
        cyc  (count (filter #(> (count %) 1) comps))]
    (println (format "  %,d functors, %,d components (%,d cyclic, largest %,d), computed in %.0f ms"
                     (count (into #{} (concat (keys g) (mapcat val g))))
                     (count comps) cyc (reduce max 0 (map count comps)) (ms t0)))
    (println "  depth distribution over components:")
    (doseq [d (sort (keys hist))]
      (println (format "    depth %-3d  %,8d components" d (get hist d))))
    {:components (count comps) :cyclic cyc :depths hist :ms (ms t0)}))

;; ---- the run ------------------------------------------------------------

(defn- load-corpus! [kb dir profile]
  (banner (str "loading " dir " at :" (name profile)))
  (let [reader (foreign/reader! :cyc-corpus)
        t0     (System/nanoTime)
        seen   (atom 0)
        r      ((:load-dir! reader) kb dir
                                    {:profile profile
                                     :on-progress (fn [{:keys [done note]}]
                                                    (when (zero? (mod (long done) 100000))
                                                      (swap! seen (constantly done))
                                                      (println (format "    %,10d sentences … %s"
                                                                       done (or note "")))
                                                      (flush)))})]
    (println (format "  asserted %,d, refused %,d over %,d contexts in %.0f s"
                     (:asserted r) (:refused r) (:contexts r) (/ (ms t0) 1000)))
    (when (seq (:refusals r))
      (println "  refusals by reason:")
      (doseq [[k n] (sort-by (comp - val) (:refusals r))]
        (println (format "    %-28s %,d" k n))))
    r))

(defn -main [& [target profile-arg chain-arg]]
  (let [quick?  (or (nil? target) (= "quick" target))
        profile (keyword (or profile-arg "ontology"))
        kb      (v/open-kb {})]
    (println (format "vaelii bench-caches — %s, max heap %.1f GB"
                     (if quick? "starter ontology (harness check)" target)
                     (/ (.maxMemory (Runtime/getRuntime)) 1073741824.0)))
    (if quick?
      (do (banner "loading the starter ontology")
          (let [t0 (System/nanoTime)]
            (starter/load-into kb)
            (println (format "  %,d sentexes in %.0f ms" (v/sentex-count kb) (ms t0)))))
      (load-corpus! kb target profile))

    (let [all-ctx (vec (v/contexts kb))
          ;; the busiest context, not an arbitrary one: a read scoped to a context nobody
          ;; asserts into sees no edges and would measure the empty case.
          ctx     (if quick?
                    'CxUniverse
                    (first (sort-by #(- (v/count-in-context kb %)) all-ctx)))
          types   (vec (v/types kb))
          sample  (vec (take (if quick? 500 10000) types))
          ctxs    (vec (take (if quick? 4 10) all-ctx))
          handles (do (banner "enumerating rules") (rule-handles kb))]
      (println (format "  reads scoped to %s" ctx))
      (println (format "  %,d types, %,d contexts, %,d rules"
                       (count types) (count (v/contexts kb)) (count handles)))

      (banner "ops-5 reading 1 — what the caches hold")
      (report-sizes kb "cold (nothing read)")
      (taxonomy-sweep! kb sample ctx)
      (report-sizes kb "after a taxonomy sweep")

      (growth-probe kb sample ctxs (if quick? 3 4))
      (rebuild-cost kb sample ctx)

      (banner "ops-6 — which rules never fire")
      (report-firings kb handles "as loaded:")
      ;; A chain over a corpus's whole rule set is its own measurement and can run long,
      ;; so it is asked for rather than assumed: `chain` as the third argument.
      (when (or quick? (= "chain" chain-arg))
        (let [t0 (System/nanoTime)
              r  (v/forward-chain kb)]
          (println (format "  forward-chain derived %,d in %.0f s%s"
                           (:derived r) (/ (ms t0) 1000)
                           (if (:truncated? r) " (TRUNCATED)" "")))
          (report-firings kb handles "after forward-chain:")))

      (extent-skew kb)
      (taxonomy-coverage kb ctx)
      (chain-depth kb handles)

      (banner "done")
      (println (format "  live heap %.2f MB" (mb (heap-live))))
      (flush))))
