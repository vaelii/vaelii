;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.walk
  "What a declared-transitive predicate's closure walk costs, and where the cost sits.

  `(transitive ancestorOf)` over a chain is answered by walking believed facts one hop at
  a time (`provers/reach`), and every hop is a `matches-visible` whose surviving candidate
  handle is turned back into a term by **one record fetch** (`resolution.clj`, the
  per-candidate `get-sentex`).  Three readings, and they answer three different questions:

  * **Where the per-edge cost is.**  The walk is timed against the *same* records fetched
    directly, on the same mount, so the fetch is reported as a share of the walk rather
    than assumed to be it.  `:memory` reads a record out of a map; `:disk` pages it — two
    positional reads and a nippy thaw — and re-interns every field.  If the fetch were the
    walk, the two mounts would be far apart and the share would be most of it.
  * **Whether the index half matters.**  `:disk-memory` is the durable record store under
    the **in-RAM** index.  The index half of `:disk-log` keeps its whole key→value map in
    RAM (`docs/indexing.md`), so the two should land together, and a `:disk-log` row apart
    from `:disk-memory` would retire that reading.
  * **What a repeat costs.**  The same closure asked again with nothing changed between.
    Two caches can serve it and they answer at different layers: `matches-visible` is
    cached per literal (`vaelii.impl.literal-cache`), which removes the walk's store reads
    but not the walk, and the reach set itself is cached per `[direction predicate node
    context]` on the KB (`provers/*closure-answer-limit*`), which removes both.  Both are
    stamped with the change clock, so one mutation anywhere retires either.  The fetch
    counts are the evidence: a repeat that fetches nothing walked nothing.  The small-class
    block below separates the two by running the repeat with the literal cache off, and
    prints the closed one-hop ask beside them — the dispatch every ask pays, and the floor
    no cache above it can go under.

  Wall-clock is untrustworthy under load, so the mounts are **interleaved** — one timed
  ask each, round-robin, medians reported — and every row prints beside the row it is to
  be read against.  Read the ratios and the counts.

  Run: `lein bench-walk [n] [big-n]`  (default 2000 8000)."
  (:require [vaelii.core :as v]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- a record store that counts what is asked of it ---------------------

(defn- counting-records
  "`store`, with every `get-sentex` tallied into `n`.  A `reify` rather than a redef of
  the protocol method: the engine's internal calls dispatch on the store's *type* and
  never go through the var, so a `with-redefs` on `p/get-sentex` would count nothing."
  [store ^java.util.concurrent.atomic.AtomicLong n]
  (reify p/RecordStore
    (put-sentex [_ sx] (p/put-sentex store sx))
    (get-sentex [_ id] (.incrementAndGet n) (p/get-sentex store id))
    (delete-sentex! [_ id] (p/delete-sentex! store id))
    (put-justification [_ d] (p/put-justification store d))
    (get-justification [_ id] (p/get-justification store id))
    (delete-justification! [_ id] (p/delete-justification! store id))
    (next-id [_] (p/next-id store))
    (put-provenance [_ id prov] (p/put-provenance store id prov))
    (get-provenance [_ id] (p/get-provenance store id))
    (delete-provenance! [_ id] (p/delete-provenance! store id))
    (sentex-ids [_] (p/sentex-ids store))
    (justification-ids [_] (p/justification-ids store))
    (mark-premise [_ id s] (p/mark-premise store id s))
    (unmark-premise! [_ id] (p/unmark-premise! store id))
    (premise-ids [_] (p/premise-ids store))
    (premise-strength [_ id] (p/premise-strength store id))
    (clear-records! [_] (p/clear-records! store))))

;; ---- the corpus ---------------------------------------------------------

(defn- scratch-dir [suffix]
  (let [d (str (System/getProperty "java.io.tmpdir") "/vaelii-walk-" suffix)]
    (doseq [f (reverse (file-seq (java.io.File. d)))] (.delete ^java.io.File f))
    d))

(def ^:private ctx 'CxUniverse)
(defn- node [i] (symbol (str "Node" i "Individual")))

(defn- chain-kb
  "A KB on `backend` holding `(transitive ancestorOf)` and a chain of `n` nodes.
  `{:chain? false}` throughout: the corpus is the point, not what loading it cost, and
  nothing here concludes anything forward."
  [backend n]
  (let [kb (if (= :memory backend)
             (doto (v/open-kb {:backend :memory :space 31 :recover? false}) (v/clear!))
             (v/open-kb {:backend backend :dir (scratch-dir (str (name backend) "-" n))
                         :recover? false}))]
    (v/assert kb '(transitive ancestorOf) ctx {:strength :monotonic :chain? false})
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'ancestorOf (node (dec i)) (node i)) ctx {:chain? false})))
    kb))

(defn- ancestor-ask
  "The open-argument closure ask — the walk this whole namespace is about."
  [kb]
  (count (v/ask kb (list 'ancestorOf (node 0) '?y) ctx)))

(defn- computed-ask
  "The same ask with the KB's held reach dropped first, so it is **computed** rather than
  read back.  The attribution rows are about what a closure costs; the repeat rows below
  are about what reading one back costs, and running the first against a warm answer cache
  would measure the second twice.  Only that cache is dropped — clearing the literal cache
  or the hot-record LRU here would move the very costs being attributed."
  [kb]
  (reset! (reasoning/closures kb) {})
  (ancestor-ask kb))

(defn- ms [f] (let [t (System/nanoTime)] (f) (/ (- (System/nanoTime) t) 1e6)))
(defn- median [xs] (nth (sort xs) (quot (count xs) 2)))

;; ---- one mount's state --------------------------------------------------

(defn- mount
  "Everything a mount's rows are measured against: the KB, a counting view of it, and the
  handles of the chain's own facts — the very records the walk fetches, so timing a sweep
  over them is the fetch half of the walk and not a different question."
  [backend n]
  (let [kb    (chain-kb backend n)
        tally (java.util.concurrent.atomic.AtomicLong. 0)]
    {:backend backend :n n :edges (dec n) :kb kb :tally tally
     :counting (assoc kb :records (counting-records (:records kb) tally))
     :ids (vec (sort (p/sentex-ids (:records kb))))}))

(defn- fetch-sweep
  "Milliseconds to fetch every one of the chain's records once, directly — the walk's
  fetch half, read with nothing else in the way."
  [{:keys [kb ids]}]
  (let [store (:records kb)]
    (ms #(reduce (fn [^long a id] (if (p/get-sentex store id) (inc a) a)) 0 ids))))

(defn- counted
  "`[ms fetches]` for one ask through the counting store."
  [m]
  (let [^java.util.concurrent.atomic.AtomicLong t (:tally m)]
    (.set t 0)
    [(ms #(ancestor-ask (:counting m))) (.get t)]))

(defn- measure
  "Interleave `reps` timed rounds across `mounts`, so a slow minute on the box lands on
  every mount rather than on whichever one happened to be running through it."
  [mounts reps f]
  (reduce (fn [a _] (reduce (fn [a m] (update a (:backend m) conj (f m))) a mounts))
          (zipmap (map :backend mounts) (repeat []))
          (range reps)))

;; ---- the rows -----------------------------------------------------------

(defn- print-attribution [mounts walk fetch n]
  (println (format "\n══ a %,d-node chain: one closure ask, per mount ══" n))
  (println (format "  %-14s %10s %11s %12s %12s %10s"
                   "mount" "walk ms" "µs/edge" "fetch µs/ed" "fetch share" "edges"))
  (println (str "  " (apply str (repeat 74 \-))))
  (doseq [m mounts
          :let [e  (:edges m)
                w  (median (get walk (:backend m)))
                fs (median (get fetch (:backend m)))]]
    (println (format "  %-14s %10.1f %11.2f %12.2f %11.0f%% %,10d"
                     (name (:backend m)) w (/ (* 1000.0 w) e) (/ (* 1000.0 fs) e)
                     (* 100.0 (/ fs w)) e))))

(defn- print-repeats [mounts rows n]
  (println (format "\n══ the same %,d-node ask again, nothing changed between ══" n))
  (println (format "  %-14s %12s %11s %11s %13s %13s"
                   "mount" "cleared ms" "repeat ms" "repeat/1st" "1st fetches" "2nd fetches"))
  (println (str "  " (apply str (repeat 80 \-))))
  (doseq [m mounts
          :let [{:keys [cold cold-n warm warm-n]} (get rows (:backend m))]]
    (println (format "  %-14s %12.1f %11.1f %10.2f× %,13d %,13d"
                     (name (:backend m)) cold warm (/ warm cold) cold-n warm-n))))

(defn- print-growth [small big walk-s walk-b]
  (println "\n══ growth: the same walk at two sizes ══")
  (println (format "  %-14s %11s %11s %10s %12s" "mount" "small ms" "big ms" "×size" "×time"))
  (println (str "  " (apply str (repeat 62 \-))))
  (doseq [[s b] (map vector small big)
          :let [ws (median (get walk-s (:backend s)))
                wb (median (get walk-b (:backend b)))]]
    (println (format "  %-14s %11.1f %11.1f %9.1f× %11.1f×"
                     (name (:backend s)) ws wb
                     (/ (double (:edges b)) (:edges s)) (/ wb ws)))))

(defn- repeat-rows
  "Per mount: the ask on a cleared literal cache, then the same ask again.  The fetch
  counts are what say whether the cache served the second one."
  [mounts]
  (into {} (for [m mounts]
             (do (v/clear-caches (:kb m))
                 (let [[c cn] (counted m)
                       [w wn] (counted m)]
                   [(:backend m) {:cold c :cold-n cn :warm w :warm-n wn}])))))

(defn- print-small-repeat
  "The form a repeated closure ask actually takes in a benchmark: a **small** class,
  asked over and over in one process with nothing changed between.  Three readings of the
  same ask — the first after a cache clear, the steady-state repeat, and the repeat with
  the literal cache off — which between them say what the cache already buys and what is
  left for anything above it to win."
  [n reps]
  (let [m       (mount :memory n)
        kb      (:kb m)
        one     (fn [] (ms #(ancestor-ask kb)))
        ;; the closed one-hop goal: the same dispatch, the same projection, and a walk
        ;; that stops at the first sighting — so what it costs is everything an ask pays
        ;; *before* the closure, and the floor anything caching the closure must beat
        near    (fn [] (ms #(v/ask kb (list 'ancestorOf (node 0) (node 1)) ctx)))
        _       (dotimes [_ 50] (ancestor-ask kb) (near))
        _       (v/clear-caches kb)
        [c cn]  (counted m)
        warm    (median (repeatedly reps one))
        [_ wn]  (counted m)
        bare    (binding [lc/*enabled* false] (median (repeatedly reps one)))
        floor   (median (repeatedly reps near))]
    (println (format "\n══ a %,d-node closure asked %,d times over, on :memory ══" n reps))
    (println (format "  %-36s %10s %12s" "" "µs/ask" "fetches"))
    (println (str "  " (apply str (repeat 62 \-))))
    (println (format "  %-36s %10.1f %,12d" "first ask, literal cache cleared" (* 1000.0 c) cn))
    (println (format "  %-36s %10.1f %,12d" "repeat, cache warm" (* 1000.0 warm) wn))
    (println (format "  %-36s %10.1f %12s" "repeat, cache off" (* 1000.0 bare) "—"))
    (println (format "  %-36s %10.1f %12s" "closed one-hop ask (dispatch floor)" (* 1000.0 floor) "—"))
    (println (format "  → turning the literal cache off moves a repeat by %.2f×, and %.0f%% of"
                     (/ bare warm) (* 100.0 (/ floor warm))))
    (println "    what a repeat costs is the per-ask dispatch rather than the closure.")))

(defn -main [& args]
  (let [n     (if (seq args) (Long/parseLong (first args)) 2000)
        bn    (if (second args) (Long/parseLong (second args)) 8000)
        names [:memory :disk-memory :disk-log]
        small (mapv #(mount % n) names)
        big   (mapv #(mount % bn) names)]
    (println "vaelii transitive-closure walk cost")
    (println "mounts interleaved, medians reported; read the ratios and the counts.")
    (doseq [m (concat small big)] (dotimes [_ 3] (ancestor-ask (:kb m))))   ; JIT + pages
    (let [walk-s  (measure small 5 #(ms (fn [] (computed-ask (:kb %)))))
          fetch-s (measure small 5 fetch-sweep)
          walk-b  (measure big 5 #(ms (fn [] (computed-ask (:kb %)))))
          fetch-b (measure big 5 fetch-sweep)]
      (print-attribution small walk-s fetch-s n)
      (print-attribution big walk-b fetch-b bn)
      (print-growth small big walk-s walk-b))
    (print-repeats small (repeat-rows small) n)
    (print-repeats big (repeat-rows big) bn)
    (print-small-repeat 40 200)
    (println "\n  Reading:")
    (println "  - `fetch µs/ed` is a sweep over the chain's own records on that mount —")
    (println "    the walk's fetch half, timed with nothing else in the way. `fetch share`")
    (println "    is therefore the ceiling on anything that makes fetching cheaper.")
    (println "  - `:disk-memory` is the durable record store under the RAM index. Landing")
    (println "    beside `:disk-log` says the index half is not the difference; landing beside")
    (println "    `:memory` would say the opposite.")
    (println "  - a repeat that fetches **nothing** walked nothing: the reach came out")
    (println "    of the KB's closure cache, above the per-literal one.")
    (shutdown-agents)))
