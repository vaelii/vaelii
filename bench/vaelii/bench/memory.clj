;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.memory
  "The load + scale benchmark against the **in-memory backend**
  (`vaelii.impl.memory`): Zipfian synthetic facts through the real
  `kb/create-sentex` load path, then the query shapes measured at the protocol
  level.  Two metrics:

  - **Latency.**  A RAM index issues no round trips, so the number to watch is
    wall-clock.  The headline is the **leading-variable fan**
    (`(hotPred ?x hotInd)` — the after-a-variable trie fan), which walks a node per
    fanned value; the argument-root path answers the same shape in one lookup and
    sits beside it for comparison.

  - **RAM, measured as JVM heap.**  Split into index and records: load, measure
    retained heap, `clear-index!`, measure again — the difference is the index's
    footprint, the remainder the records'.


  Run: `lein bench-memory [facts] [rules] [iters]`  (defaults 200000 20000 200).
  Uses space 10 in the in-memory registry — no server, no
  external dependency."
  (:require [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]))

;; ---- generation (the reference load bench's fact shape) -----------------

(defn- gen-fact
  "One synthetic fact `[sentence context]`: a Zipf predicate, 2-3 Zipf-individual
  arguments, and — with probability `compound-frac` — a compound last argument
  `(qtyFn <int> <unit>)`, so the structural trie is exercised."
  [^java.util.Random rng {:keys [preds inds units ctxs pred-cum ind-cum compound-frac]}]
  (let [pred    (nth preds (zipf-sample pred-cum rng))
        ctx     (nth ctxs (.nextInt rng (count ctxs)))
        arity   (+ 2 (.nextInt rng 2))
        a       (nth inds (zipf-sample ind-cum rng))
        rest-as (repeatedly (dec arity) #(nth inds (zipf-sample ind-cum rng)))
        rest-as (if (< (.nextDouble rng) compound-frac)
                  (concat (butlast rest-as)
                          [(list 'qtyFn (.nextInt rng 1000)
                                 (nth units (.nextInt rng (count units))))])
                  rest-as)]
    [(apply list pred a rest-as) ctx]))

(defn- load-facts! [kb ^java.util.Random rng {:keys [n] :as cfg}]
  (let [sample (java.util.ArrayList.)
        t0     (System/nanoTime)]
    (dotimes [i n]
      (let [[s c] (gen-fact rng cfg)]
        (kb/create-sentex kb s c)
        (when (zero? (mod i 200)) (.add sample [s c]))
        (when (and (pos? i) (zero? (mod i 50000)))
          (println (format "  … %,d facts (%.0f/s)" i
                           (/ i (/ (- (System/nanoTime) t0) 1e9)))))))
    {:secs (/ (- (System/nanoTime) t0) 1e9) :sample (vec sample)}))

(defn- load-rules! [kb ^java.util.Random rng {:keys [r preds pred-cum]}]
  (let [ix (:index kb), t0 (System/nanoTime)]
    (dotimes [i r]
      (let [antes (distinct (repeatedly (inc (.nextInt rng 3))
                                        #(nth preds (zipf-sample pred-cum rng))))
            conc  (nth preds (zipf-sample pred-cum rng))]
        (rules/index-rule ix (+ 1000000000 i) antes conc #{p/var-consequent-key} (quote CxBench))))
    {:secs (/ (- (System/nanoTime) t0) 1e9)}))

;; ---- measurement --------------------------------------------------------

(defn- gc!
  "Encourage the heap into a stable state before a `heap-used` reading — a few GC
  rounds, since one is only a hint."
  []
  (dotimes [_ 5] (System/gc) (System/runFinalization) (Thread/sleep 40)))

(defn- heap-used []
  (.getUsed (.getHeapMemoryUsage (java.lang.management.ManagementFactory/getMemoryMXBean))))

(defn- latency
  "Run `thunk` `iters` times after a warmup (so the JIT has compiled the path — at
  microsecond scale the first calls are interpreted and would dominate).  Report the
  average wall-clock and the average realized result size."
  [label iters thunk]
  (dotimes [_ (min iters 50)] (thunk))                 ; warmup / JIT
  (let [t0    (System/nanoTime)
        sizes (mapv (fn [_] (count (thunk))) (range iters))
        ms    (/ (- (System/nanoTime) t0) 1e6)]
    {:label label
     :avg-ms   (/ ms (max 1 iters))
     :avg-size (double (/ (reduce + sizes) (max 1 iters)))}))

(defn- path [kb sentence] (sx/path (res/kb-sentex kb sentence '?ctx)))

(defn- run-benches [kb {:keys [preds inds iters]} sample]
  (let [ix        (:index kb)
        hot-pred  (first preds)
        rare-pred (last preds)
        hot-ind   (first inds)
        rare-ind  (last inds)
        hot2      (second inds)
        few       (max 3 (quot iters 4))]              ; the fan shapes still run plenty in RAM
    [(latency "ground exact (hit)" iters
              #(p/lookup ix (path kb (first (rand-nth sample)))))

     ;; the two ways to answer a leading-variable, ground-hot-arg pattern:
     (latency "(hotPred ?x hotInd) — trie fan" few
              #(p/lookup ix (path kb (list hot-pred '?x hot-ind))))
     (latency "(hotPred ?x hotInd) — arg root" iters
              #(p/sentexes-with-args ix hot-pred [[2 hot-ind]]))

     (latency "functor extent (hotPred)" few
              #(p/sentexes-with-functor ix hot-pred))

     (latency "find-sentexes hotInd" iters
              #(reads/as-stored-with-term ix hot-ind))
     (latency "find-sentexes rareInd" iters
              #(reads/as-stored-with-term ix rare-ind))
     (latency "intersect hotInd ∩ hotInd2" iters
              #(p/sentexes-with-terms ix [hot-ind hot2]))
     (latency "intersect hotInd ∩ rareInd" iters
              #(p/sentexes-with-terms ix [hot-ind rare-ind]))

     (latency "structural (pred ?o (qtyFn ?n unit0))" few
              #(p/lookup ix (path kb (list hot-pred '?o (list 'qtyFn '?n 'unit0)))))

     (latency "rules-by-antecedent hotPred" iters
              #(reads/as-stored-rules-by-antecedent-global ix hot-pred))
     (latency "rules-by-antecedent rarePred" iters
              #(reads/as-stored-rules-by-antecedent-global ix rare-pred))

     (latency "planner order (3-literal join)" iters
              #(do (plan/order kb [(list hot-pred '?x '?y)
                                   (list (nth preds 2) '?y hot-ind)
                                   (list (nth preds 3) '?x '?z)]
                               'CxCtx0)
                   [1]))]))

;; ---- report -------------------------------------------------------------

(defn- print-benches [rows]
  (println)
  (println (format "%-42s %12s %14s" "shape" "avg µs" "avg result"))
  (println (apply str (repeat 70 \-)))
  (doseq [{:keys [label avg-ms avg-size]} rows]
    (println (format "%-42s %12.2f %14.0f" label (* 1000.0 avg-ms) avg-size))))

(defn -main [& args]
  (let [[facts rules iters] (map #(when % (Long/parseLong %)) args)
        n      (or facts 200000)
        r      (or rules 20000)
        iters  (or iters 200)
        P      (max 50 (quot n 400))
        M      (max 1000 (quot n 4))
        preds  (u/terms "pr" P)
        inds   (u/terms "Ind" M)
        cfg    {:n n :r r :iters iters
                :preds preds :inds inds
                :units (u/terms "unit" 10)
                :ctxs  (mapv #(symbol (str "CxCtx" %)) (range 8))
                :pred-cum (u/zipf-cumulative P 1.2)
                :ind-cum  (u/zipf-cumulative M 1.0)
                :compound-frac 0.15}
        kb     (kb/open-kb {:backend :memory :space 10 :recover? false}
                           (fn [_] nil) (fn [_] nil))]
    (println (format "vaelii index benchmark — IN-MEMORY backend — %,d facts, %,d rules, %d preds, %,d individuals"
                     n r P M))
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (let [rng    (java.util.Random. 42)
          _      (gc!)
          base   (heap-used)
          {fsecs :secs sample :sample} (load-facts! kb rng cfg)
          {rsecs :secs} (load-rules! kb rng cfg)
          _      (gc!)
          full   (heap-used)
          total  (- full base)]
      (println)
      (println (format "loaded %,d facts in %.1fs (%,.0f/s), %,d rules in %.1fs"
                       n fsecs (/ n fsecs) r rsecs))
      ;; the latency battery runs while the whole index is live …
      (print-benches (run-benches kb cfg sample))
      ;; … then split the retained heap: clear the index, and what is freed was the
      ;; index; what remains is the records.
      (gc!)
      (let [pre-clear (heap-used)]
        (p/clear-index! (:index kb))
        (gc!)
        (let [recs   (- (heap-used) base)
              idx    (- pre-clear (+ base recs))
              bpf    #(double (/ % (max 1 n)))
              gb     #(/ (* (bpf %) 1e8) (* 1024.0 1024 1024))]
          (println)
          (println (format "retained JVM heap (records + index): %.1f MB   ≈ %.0f bytes/fact"
                           (/ total 1048576.0) (bpf total)))
          (println (format "  records: %.1f MB (≈ %.0f bytes/fact)   index: %.1f MB (≈ %.0f bytes/fact)"
                           (/ recs 1048576.0) (bpf recs) (/ idx 1048576.0) (bpf idx)))
          (println (format "extrapolated to 100M facts: ≈ %.1f GB total  (records %.1f GB + index %.1f GB), linear"
                           (gb total) (gb recs) (gb idx)))))
      (shutdown-agents))))
