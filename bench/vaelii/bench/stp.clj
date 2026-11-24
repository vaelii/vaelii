;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.stp
  "Metric-temporal closure scaling — what a `temporalDistance` answer costs, and what an
  *arriving* constraint costs the answer after it.

  The closure is all-pairs shortest paths over the distance graph a network describes, so
  one pass is cubic in the **instant** count.  It is memoized on the network value, which
  makes a query loop over one belief state free after the first ask — and makes an arriving
  constraint a different network, so the pass would run again.  Loading a KB one fact at a
  time is therefore a cubic pass per fact unless the pass is warm-started, and this harness
  is what says how much that is worth at the sizes a KB reaches.

  Seven readings per instant count, and they answer different questions:

    - **scratch** — one `stp/close` over the whole network, from nothing.  The cost of the
      first answer in a context, and the floor a cold pass cannot get under.
    - **add → close** / **add → warm** — the pure-data loop, both routes: narrow one more
      constraint between instants already there, then either close the whole network again
      or relax the constraint into the state the last close reached.  No KB, no belief, no
      measures — the algorithm alone.  The constraint spans a long stretch of the chain and
      is far tighter than the chain implies, so most of the network moves: this is the
      **dense** case for the warm start, where what it saves is the pass and not the
      read-back.
    - **grow → close** / **grow → warm** — the same pair where each arriving constraint
      names an instant the network has never held, which is what loading a timeline does.
      Only that instant's own bounds are new, so the read-back is linear and the warm start
      shows what it is worth when the answer moves as much as an arriving fact usually
      moves it.
    - **KB read** — `stp/problem` alone: the believed-fact read and the magnitude
      normalization behind every answer, with no closure at all.  What the per-add readings
      below carry that the pure ones do not.
    - **add → query (KB)** — the dense add through the engine: assert one more
      `temporalDistance` fact, then ask for the closed network.
    - **memo hit (KB)** — the same ask with *nothing* changed.  The network is resident on
      the KB and the closure is keyed on its value, so this is what a query loop pays per
      question once the first one is answered.

  The last two are the pair a decision about warm-starting turns on: an add that costs many
  times a memo hit is a recompute, and one that costs a memo hit is not.

  Every network here is a **chain** — instant `i` some distance after instant `i-1` — which
  is the form a sequence of events produces and the dense case for the read-back: a chain
  determines a bound between every pair, so the closed network holds n² of them however few
  were written.  Magnitudes are integers and every generated constraint contains the true
  gap of a fixed assignment, so nothing measured here is the inconsistency path.

  Run: `lein bench-stp [instant counts…]`  (default 25 100 400)."
  (:require [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.stp :as stp]))

;; ---- the network under test ---------------------------------------------

(def ^:private step
  "The true gap between consecutive instants.  Every generated constraint brackets the gap
  the assignment `t(i) = step·i` gives, so the network is satisfiable by construction."
  10)

(defn- instant [i] (symbol (str "Tp" i)))

(defn- chain-net
  "`n` instants in a row, each one bracketed against the last.  n-1 constraints, and a
  closure that bounds all n² pairs."
  [n]
  (reduce (fn [net i] (stp/narrow net (instant i) (instant (inc i)) (- step 2) (+ step 2)))
          {}
          (range (dec n))))

(defn- cross-constraints
  "`k` constraints between instants the chain does not join directly, drawn from a fixed
  seed so two runs measure the same work.  Each brackets the true gap, so it tightens the
  network without ever contradicting it — an arriving fact, not an arriving clash."
  [n k]
  (let [rng (java.util.Random. 20260824)]
    (into []
          (for [_ (range k)
                :let [a (.nextInt rng (int n))
                      b (.nextInt rng (int n))
                      [p q] (if (< a b) [a b] [b a])
                      q     (if (= p q) (min (dec n) (inc q)) q)
                      gap   (* step (- q p))]]
            [(instant p) (instant q) (- gap 3) (+ gap 3)]))))

;; ---- timing --------------------------------------------------------------

(defn- ms [f] (let [t (System/nanoTime) r (f)] [(/ (- (System/nanoTime) t) 1e6) r]))

(defn- ms-min
  "`ms`, taking the **fastest** of `reps` runs.  Wall-clock on a shared box is contended and
  noise only ever adds time, so the smallest observation is the closest reading to the cost
  with the machine to itself."
  [reps f]
  (first (reduce (fn [best _] (let [[t r] (ms f)] (if (< t (first best)) [t r] best)))
                 [Double/MAX_VALUE nil]
                 (range reps))))

(defn- mean [xs] (/ (double (reduce + xs)) (max 1 (count xs))))

;; ---- the pure-data readings ----------------------------------------------

(defn- scratch-ms
  "One closure of the whole chain, from nothing."
  [net nodes]
  (ms-min 5 #(stp/close net nodes)))

(defn- add-close-loop
  "Narrow each of `adds` into `net` in turn, closing after every one and reading the pair
  back — the per-add milliseconds, one reading each.  Reading the pair is what makes the
  close a real one: `constraint` is a map lookup on the answer, and without it a caller
  could be measuring a pass nothing consumed."
  [net nodes adds]
  (second
   (reduce (fn [[net' times] [p q lo hi]]
             (let [net'' (stp/narrow net' p q lo hi)
                   [t c] (ms #(stp/close net'' nodes))]
               (stp/constraint c p q)
               [net'' (conj times t)]))
           [net []]
           adds)))

(defn- add-close-ms
  "Per-add milliseconds for the pure loop, the first pass discarded so the reading is taken
  on a JIT-warm one."
  [net nodes adds]
  (add-close-loop net nodes adds)
  (mean (add-close-loop net nodes adds)))

(defn- add-warm-loop
  "The same loop warm-started: each close starts from the state the last one reached."
  [net nodes adds]
  (loop [net' net, state (stp/close-state net nodes), [c & more] adds, times []]
    (if (nil? c)
      times
      (let [[p q lo hi] c
            net''       (stp/narrow net' p q lo hi)
            [t state']  (ms #(stp/close-state-from net'' state nodes))]
        (stp/constraint (:net state') p q)
        (recur net'' state' more (conj times t))))))

(defn- add-warm-ms
  "Per-add milliseconds for the warm-started loop, the first pass discarded."
  [net nodes adds]
  (add-warm-loop net nodes adds)
  (mean (add-warm-loop net nodes adds)))

(defn- grow-loop
  "The chain **growing**: each step states a gap to an instant the network has never held,
  which is what loading a timeline one fact at a time does.  The instant count rises with
  the loop, so the node set is read off the network each step.  `warm?` picks the route."
  [net n adds warm?]
  (loop [net'  net
         state (stp/close-state net (stp/nodes net))
         i     0
         times []]
    (if (= i adds)
      times
      (let [p     (instant (+ n i -1))
            q     (instant (+ n i))
            net'' (stp/narrow net' p q (- step 2) (+ step 2))
            nodes (stp/nodes net'')
            [t s] (ms #(if warm?
                         (stp/close-state-from net'' state nodes)
                         (stp/close-state net'' nodes)))]
        (stp/constraint (:net s) p q)
        (recur net'' s (inc i) (conj times t))))))

(defn- grow-ms
  "Per-add milliseconds for the growing chain, the first pass discarded."
  [net n adds warm?]
  (grow-loop net n adds warm?)
  (mean (grow-loop net n adds warm?)))

;; ---- the KB arm ----------------------------------------------------------

(def ^:private C 'CxUniverse)

(defn- fresh-kb
  "The upper layer (the grammar, the measure vocabulary and unit table, the temporal
  vocabulary) and the metric prover registered — the configuration a KB reasoning about
  gaps is in."
  []
  (let [kb (v/open-kb {:backend :memory :space 45 :recover? false})]
    (v/clear! kb)
    (core-context/load-into kb)
    (v/add-prover kb (stp/stp-prover))
    kb))

(defn- state-gap!
  "One `(temporalDistance P Q (QuantityIntervalFn lo hi Second))` fact."
  [kb p q lo hi]
  (v/assert kb (list 'temporalDistance p q (list 'QuantityIntervalFn lo hi 'Second)) C))

(defn- kb-readings
  "`{:memo-hit-ms :query-ms :kb-read-ms}` — a KB holding the chain, then `adds` more
  constraints arriving one at a time with the closed network asked for after each.  The
  assert sits outside the timed region, so the per-add reading is what the *answer* costs
  once a constraint has moved and not what the write costs."
  [kb n adds]
  (doseq [i (range (dec n))]
    (state-gap! kb (instant i) (instant (inc i)) (- step 2) (+ step 2)))
  ;; the first ask pays for everything; every ask after it is the memo hit being measured
  (stp/closed-network kb C)
  (let [hits (mapv (fn [_] (first (ms #(stp/closed-network kb C)))) (range 200))
        asks (mapv (fn [[p q lo hi]]
                     (state-gap! kb p q lo hi)
                     (first (ms #(stp/closed-network kb C))))
                   adds)]
    {:memo-hit-ms (mean hits)
     :query-ms    (mean asks)
     :kb-read-ms  (let [rs (mapv (fn [_] (observe/note-change (:clock kb))
                                   (first (ms #(stp/problem kb C))))
                                 (range 10))]
                    (mean rs))}))

;; ---- the report ----------------------------------------------------------

(def ^:private adds-per-size
  "How many constraints arrive one at a time.  Enough that the mean is not one reading, few
  enough that four hundred instants finish."
  20)

(defn- warm!
  "Drive the closure hard enough that the readings below are of compiled code.  A cold
  cubic loop reads several times its warm cost, and at the smallest size that is most of
  the number — which would flatter every larger one by comparison."
  []
  (let [net   (chain-net 40)
        nodes (stp/nodes net)]
    (dotimes [_ 40] (stp/constraint (stp/close net nodes) (instant 0) (instant 39)))))

(defn- row [n]
  (let [net    (chain-net n)
        nodes  (stp/nodes net)
        adds   (cross-constraints n adds-per-size)
        scr    (scratch-ms net nodes)
        pure   (add-close-ms net nodes adds)
        warm   (add-warm-ms net nodes adds)
        gcold  (grow-ms net n adds-per-size false)
        gwarm  (grow-ms net n adds-per-size true)
        kb     (fresh-kb)
        kbr    (try (kb-readings kb n adds) (finally (v/clear! kb)))]
    (merge {:instants n :constraints (dec n) :scratch-ms scr :add-close-ms pure :add-warm-ms warm
            :grow-close-ms gcold :grow-warm-ms gwarm} kbr)))

(defn -main [& args]
  (let [sizes (if (seq args) (mapv #(Long/parseLong %) args) [25 100 400])]
    (warm!)
    (println)
    (println "vaelii metric-temporal closure — chain networks, integer magnitudes")
    (println)
    (println (format "%9s %7s %9s %10s %9s %10s %9s %8s %10s %9s"
                     "instants" "stated" "scratch" "add→close" "add→warm"
                     "grow→close" "grow→warm" "KB read" "add→query" "memo hit"))
    (println (format "%9s %7s %9s %10s %9s %10s %9s %8s %10s %9s"
                     "" "" "ms" "ms/add" "ms/add" "ms/add" "ms/add" "ms" "ms/add" "ms/ask"))
    (doseq [n sizes]
      (let [{:keys [instants constraints scratch-ms add-close-ms add-warm-ms
                    grow-close-ms grow-warm-ms kb-read-ms query-ms memo-hit-ms]} (row n)]
        (println (format "%9d %7d %9.3f %10.3f %9.3f %10.3f %9.3f %8.3f %10.3f %9.4f"
                         instants constraints scratch-ms add-close-ms add-warm-ms
                         grow-close-ms grow-warm-ms kb-read-ms query-ms memo-hit-ms))))
    (println)
    (shutdown-agents)))
