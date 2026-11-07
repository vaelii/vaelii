;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stp-test
  "`vaelii.impl.stp` (docs/stp.md): the algorithm alone first, then the prover, the
  reports and the interval bridge over a KB."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.duration :as dur]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.point :as pt]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu])
  (:import [vaelii.impl.stp TemporalDistanceProver]))

;; A fresh KB per test with the upper layer and the opt-in prover registered.
;; The KB is built per test because a test registers a prover of its own, which a KB
;; shared across tests would keep.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/empty-kb)
                        (tu/load-core!)
                        (v/add-prover (stp/stp-prover)))))

(def ^:private C 'CxUniverse)

(defn- inconsistent?
  "Do the `temporalDistance` constraints visible from `context` contradict each other?"
  [kb context]
  (= :inconsistent (stp/closed-network kb context)))

(defn- endpoints-of [kb i context] (first (stp/endpoints-with-support kb i context)))

(defn- load-time-units
  "Second, Minute and Hour, each converting direct to Second."
  [kb]
  (v/assert kb '(dimensionOf Second Duration)   C)
  (v/assert kb '(dimensionOf Minute Duration)   C)
  (v/assert kb '(dimensionOf Hour Duration)     C)
  (v/assert kb '(conversionFactor Second Second 1)  C)
  (v/assert kb '(conversionFactor Minute Second 60) C)
  (v/assert kb '(conversionFactor Hour Second 3600) C))

(defn- bound [kb goal] (get (tu/sole-answer (v/ask kb goal C)) '?d))

;; ---- the algorithm, without a KB ----------------------------------------

(deftest a-chain-of-gaps-composes-by-addition
  (let [net (-> {} (stp/narrow 'A 'B 10 20) (stp/narrow 'B 'C 5 5))
        pc  (stp/close net (stp/nodes net))]
    (testing "10-to-20 then exactly 5 is 15-to-25, which nobody wrote down"
      (is (= [15 25] (stp/constraint pc 'A 'C))))
    (testing "and the converse bound is the same interval reflected"
      (is (= [-25 -15] (stp/constraint pc 'C 'A))))
    (testing "a stated bound no path improves on survives unchanged"
      (is (= [10 20] (stp/constraint pc 'A 'B))))
    (testing "the diagonal is no gap at all"
      (is (= [0 0] (stp/constraint pc 'A 'A))))
    (testing "and an instant the network never mentions is unbounded against everything"
      (is (= stp/unbounded (stp/constraint pc 'A 'Z))))))

(deftest intersection-is-order-independent
  (is (= (-> {} (stp/narrow 'A 'B 0 10) (stp/narrow 'A 'B 5 20))
         (-> {} (stp/narrow 'A 'B 5 20) (stp/narrow 'A 'B 0 10))))
  (is (= [5 10] (get (-> {} (stp/narrow 'A 'B 0 10) (stp/narrow 'A 'B 5 20)) '[A B]))))

(deftest a-negative-cycle-is-the-contradiction
  (testing "three gaps that cannot all be closed: A to B and B to C are each 1, and A to C
            is claimed to be 1 as well"
    (let [net (-> {} (stp/narrow 'A 'B 1 1) (stp/narrow 'B 'C 1 1) (stp/narrow 'A 'C 1 1))]
      (is (= :inconsistent (stp/close net (stp/nodes net))))))
  (testing "bounds that cross are refused as written, whatever else is present"
    (is (= :inconsistent (stp/close (assoc {} '[A B] [10 5]) '#{A B})))
    (is (= '#{[A B]} (stp/unsatisfiable-pairs (assoc {} '[A B] [10 5])))))
  (testing "a non-zero gap from an instant to itself is refused the same way — no path ever
            visits the diagonal, so nothing else would report it"
    (is (= :inconsistent (stp/close (assoc {} '[A A] [5 5]) '#{A})))
    (is (= [0 0] (stp/constraint (assoc {} '[A A] [5 5]) 'A 'A))))
  (testing "and a consistent cycle is not one — the three gaps add to nothing"
    (let [net (-> {} (stp/narrow 'A 'B 1 1) (stp/narrow 'B 'C 1 1) (stp/narrow 'A 'C 2 2))]
      (is (not= :inconsistent (stp/close net (stp/nodes net)))))))

;; ---- the closure against a second implementation of it -------------------
;; The same algorithm over a persistent map keyed `[p q]`, sharing no code with `stp/close`.

(defn- reference-close
  "All-pairs shortest paths over `net` across `nodes`, keyed `[p q]` in a persistent map:
  `:inconsistent` for a crossed constraint or a negative cycle, else the closed network."
  [net nodes]
  (if (seq (stp/unsatisfiable-pairs net))
    :inconsistent
    (let [node-vec (into [] (sort-by str nodes))
          seeded   (reduce (fn [d [[p q] [_ hi]]]
                             (if (or (= p q) (not (Double/isFinite (double hi))))
                               d
                               (let [cur (get d [p q])]
                                 (if (or (nil? cur) (< hi cur)) (assoc d [p q] hi) d))))
                           (into {} (map (fn [x] [[x x] 0])) node-vec)
                           net)
          closed   (reduce
                    (fn [d k]
                      (reduce
                       (fn [d p]
                         (if-let [dpk (get d [p k])]
                           (reduce (fn [d q]
                                     (if-let [dkq (get d [k q])]
                                       (let [w (+ dpk dkq), cur (get d [p q])]
                                         (if (or (nil? cur) (< w cur)) (assoc d [p q] w) d))
                                       d))
                                   d node-vec)
                           d))
                       d node-vec))
                    seeded node-vec)
          eps      provers/*quantity-tolerance*
          cyclic   (filter (fn [x] (when-let [w (get closed [x x])] (< w (- eps)))) node-vec)]
      (if (seq cyclic)
        :inconsistent
        (into {}
              (for [p     node-vec
                    q     node-vec
                    :when (not= p q)
                    :let  [hi (get closed [p q] ##Inf)
                           lo (if-let [w (get closed [q p])] (- w) ##-Inf)]
                    :when (or (Double/isFinite (double lo)) (Double/isFinite (double hi)))]
                [[p q] [lo hi]]))))))

(defn- same-verdict?
  "Do two closures agree bound for bound, numerically — `15` and `15.0` being one answer?"
  [a b]
  (or (= a b)
      (and (map? a) (map? b)
           (= (set (keys a)) (set (keys b)))
           (every? (fn [k]
                     (let [[l1 h1] (get a k), [l2 h2] (get b k)]
                       (and (== l1 l2) (== h1 h2))))
                   (keys a)))))

(defn- random-network
  "`edges` random integer gaps over `n` instants, drawn from `rnd` around zero so that a
  negative cycle is common."
  [^java.util.Random rnd n edges]
  (let [instants (mapv #(symbol (str "Sn" %)) (range n))]
    (reduce (fn [net _]
              (let [p (nth instants (.nextInt rnd n))
                    q (nth instants (.nextInt rnd n))]
                (if (= p q)
                  net
                  (let [lo (- (.nextInt rnd 21) 10)]
                    (stp/narrow net p q lo (+ lo (.nextInt rnd 8)))))))
            {}
            (range edges))))

(deftest the-closure-agrees-with-a-map-keyed-reference-implementation
  (let [rnd  (java.util.Random. 20260823)
        runs (for [i (range 120)
                   :let [net (random-network rnd (+ 3 (mod i 8)) (+ 2 (mod i 11)))
                         ns' (stp/nodes net)]]
               [net (stp/close net ns') (reference-close net ns')])]
    (doseq [[net mine theirs] runs]
      (is (same-verdict? mine theirs)
          (str "the two closures disagree on " (pr-str net))))
    (testing "the sample reaches both verdicts"
      (is (some (fn [[_ mine _]] (= :inconsistent mine)) runs)
          "some network closes into a negative cycle")
      (is (some (fn [[_ mine _]] (map? mine)) runs)
          "and some closes consistently"))))

(deftest a-bound-reads-back-as-an-ordering
  (is (= #{:before} (stp/point-possibilities [1 5])))
  (is (= #{:after} (stp/point-possibilities [-5 -1])))
  (is (= #{:equal} (stp/point-possibilities [0 0])))
  (is (= #{:before :equal} (stp/point-possibilities [0 5])))
  (is (= #{:equal :after} (stp/point-possibilities [-5 0])))
  (is (= #{:before :equal :after} (stp/point-possibilities [-5 5])))
  (is (= #{:before :equal :after} (stp/point-possibilities stp/unbounded))
      "a bound is a closed interval, so at least one ordering always survives"))

;; ---- the endpoint signatures, derived from numeric layouts ---------------

(def ^:private by-endpoints
  "Each Allen base relation as the endpoint inequalities that define it, independent of
  `endpoint-signature`."
  {:before        (fn [_as ae bs _be] (< ae bs))
   :meets         (fn [_as ae bs _be] (= ae bs))
   :overlaps      (fn [as ae bs be] (and (< as bs) (< bs ae) (< ae be)))
   :finished-by   (fn [as ae bs be] (and (< as bs) (= ae be)))
   :contains      (fn [as ae bs be] (and (< as bs) (> ae be)))
   :starts        (fn [as ae bs be] (and (= as bs) (< ae be)))
   :equal         (fn [as ae bs be] (and (= as bs) (= ae be)))
   :started-by    (fn [as ae bs be] (and (= as bs) (> ae be)))
   :during        (fn [as ae bs be] (and (> as bs) (< ae be)))
   :finishes      (fn [as ae bs be] (and (> as bs) (= ae be)))
   :overlapped-by (fn [as ae bs be] (and (> as bs) (< as be) (> ae be)))
   :met-by        (fn [as _ae _bs be] (= as be))
   :after         (fn [as _ae _bs be] (> as be))})

(def ^:private layouts
  "Every proper interval over the six points 0..5 — enough to realize any layout of two."
  (vec (for [s (range 6) e (range 6) :when (< s e)] [s e])))

(defn- relation-of [[as ae] [bs be]]
  (first (keep (fn [[rel pred]] (when (pred as ae bs be) rel)) by-endpoints)))

(defn- ordering [a b] (cond (< a b) :before (= a b) :equal :else :after))

(defn- signature-of [[as ae] [bs be]]
  {[:start :start] (ordering as bs) [:start :end] (ordering as be)
   [:end :start]   (ordering ae bs) [:end :end]   (ordering ae be)})

(deftest the-endpoint-signatures-match-the-relation-definitions
  (let [derived (reduce (fn [m [a b]]
                          (update m (relation-of a b) (fnil conj #{}) (signature-of a b)))
                        {} (for [a layouts b layouts] [a b]))]
    (testing "each relation forces exactly one set of four orderings"
      (doseq [[rel sigs] derived]
        (is (= 1 (count sigs)) (str rel " forces " (count sigs) " different signatures"))))
    (testing "and that is the one transcribed"
      (is (= iv/all-relations (set (keys derived))))
      (is (= iv/all-relations stp/allen-relations))
      (doseq [[rel sigs] derived]
        (is (= (first sigs) (stp/endpoint-signature rel)) (str rel))))
    (testing "the thirteen signatures are distinct"
      (is (= 13 (count (set (vals stp/endpoint-signature))))))))

(deftest a-network-saying-nothing-narrows-nothing
  (is (= iv/all-relations (stp/relations-from-endpoints {} '[As Ae] '[Bs Be]))))

(deftest the-overlap-window-is-the-later-start-to-the-earlier-end
  (testing "A runs 0 to 10, B runs 4 to 20 — six shared"
    (let [net (-> {} (stp/narrow 'As 'Ae 10 10) (stp/narrow 'As 'Bs 4 4)
                  (stp/narrow 'Bs 'Be 16 16))
          pc  (stp/close net (stp/nodes net))]
      (is (= [6 6] (stp/overlap-bounds-from-endpoints pc '[As Ae] '[Bs Be])))
      (is (= [6 6] (stp/overlap-bounds-from-endpoints pc '[Bs Be] '[As Ae]))
          "the overlap is symmetric")))
  (testing "intervals apart share nothing, and the clamp is what says so"
    (let [net (-> {} (stp/narrow 'As 'Ae 2 2) (stp/narrow 'Bs 'Be 3 3)
                  (stp/narrow 'Ae 'Bs 1 1))
          pc  (stp/close net (stp/nodes net))]
      (is (= [0 0] (stp/overlap-bounds-from-endpoints pc '[As Ae] '[Bs Be])))))
  (testing "a network that constrains nothing bounds nothing"
    (let [[lo hi] (stp/overlap-bounds-from-endpoints {} '[As Ae] '[Bs Be])]
      (is (= 0 lo))
      (is (not (Double/isFinite (double hi)))))))

;; ---- the prover over a KB ------------------------------------------------

(tu/deftest-kb a-derived-gap-is-bound-in-the-base-unit
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (testing "half an hour then an hour is 5400 seconds, though nobody said so"
      (is (= '(QuantityFn 5400 Second) (bound kb (list 'temporalDistance P R '?d)))))
    (testing "the units compose through the table, so a mixture is no obstacle"
      (is (v/ask? kb (list 'temporalDistance P R '(QuantityFn 1.5 Hour)) C))
      (is (v/ask? kb (list 'temporalDistance P R '(QuantityFn 90 Minute)) C)))
    (testing "and the gap read backwards is the same one negated"
      (is (= '(QuantityFn -5400 Second) (bound kb (list 'temporalDistance R P '?d))))
      (is (v/ask? kb (list 'temporalDistance R P '(QuantityFn -90 Minute)) C)))
    (testing "an instant against itself is no gap at all"
      (is (= '(QuantityFn 0 Second) (bound kb (list 'temporalDistance P P '?d)))))))

(tu/deftest-kb a-bounded-constraint-stays-bounded
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityIntervalFn 10 20 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 5 Minute)) C)
    (testing "the bounds add separately, and the render reports what is not known"
      (is (= '(QuantityIntervalFn 900 1500 Second)
             (bound kb (list 'temporalDistance P R '?d)))))
    (testing "so no point measure is claimed"
      (is (not (v/ask? kb (list 'temporalDistance P R '(QuantityFn 900 Second)) C)))
      (is (not (v/ask? kb (list 'temporalDistance P R '(QuantityFn 1500 Second)) C))))))

(tu/deftest-kb the-derived-bound-is-the-tightest-one-entailed
  (load-time-units kb)
  (tu/with-terms [P Q R]
    ;; P to Q is stated loosely and determined exactly by the way round through R
    (v/assert kb (list 'temporalDistance P Q '(QuantityIntervalFn 10 20 Minute)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 5 Minute)) C)
    (v/assert kb (list 'temporalDistance R Q '(QuantityFn 8 Minute)) C)
    (testing "the two routes intersect to the exact figure"
      (is (= '(QuantityFn 780 Second) (bound kb (list 'temporalDistance P Q '?d)))))
    (testing "a stated bound containing the derived one is entailed"
      (is (v/ask? kb (list 'temporalDistance P Q '(QuantityIntervalFn 10 20 Minute)) C))
      (is (v/ask? kb (list 'temporalDistance P Q '(QuantityIntervalFn 0 60 Minute)) C)))
    (testing "anything tighter is not"
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityIntervalFn 14 20 Minute)) C)))
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityFn 700 Second)) C))))))

(tu/deftest-kb an-arriving-constraint-is-relaxed-into-the-answer-already-held
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 30 Minute)) C)
    (stp/closed-network kb C)                     ; the first ask closes from nothing
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (let [cold (atom 0)
          warm (atom 0)
          counting (fn [f n] (fn [& args] (swap! n inc) (apply f args)))
          from-scratch (let [{:keys [net]} (stp/problem kb C)]
                         (stp/close net (stp/nodes net)))
          answer   (with-redefs [stp/close-state      (counting stp/close-state cold)
                                 stp/close-state-from (counting stp/close-state-from warm)]
                     (stp/closed-network kb C))]
      (testing "the arriving constraint is relaxed into the resident closure"
        (is (= 1 @warm))
        (is (zero? @cold)))
      (testing "and R, which the previous answer had no row for, joins it"
        (is (= [5400 5400] (stp/constraint answer P R))))
      (testing "reaching exactly what the pass from nothing reaches"
        (is (= from-scratch answer))))))

(tu/deftest-kb a-gap-nothing-reaches-has-no-measure
  (load-time-units kb)
  (tu/with-terms [P Q R S]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Minute)) C)
    (testing "R sits in no constraint: the separation is unbounded and no measure binds"
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) C)))
      (is (= '[[Duration Second] ##-Inf ##Inf] (stp/separation kb C P R))))
    (testing "a half-bounded gap binds no measure either"
      (v/assert kb (list 'temporalDistance R S '(QuantityIntervalFn 5 5 Minute)) C)
      (is (empty? (v/ask kb (list 'temporalDistance P S '?d) C))))))

(tu/deftest-kb a-calendar-moment-is-placed-at-its-offset-from-its-frames-epoch-node
  (load-time-units kb)
  (tu/with-terms [P X]
    (let [h (v/assert kb (list 'temporalDistance '(InstantFn 2000 1 1 0 0 0) P '(QuantityFn 1 Hour)) C)]
      (testing "a gap stated from a moment reaches the same moment spelled another way, and a later one"
        (is (= '(QuantityFn 3600 Second) (bound kb (list 'temporalDistance '(StartFn (DayFn 2000 1 1)) P '?d))))
        (is (= '(QuantityFn 1800 Second) (bound kb (list 'temporalDistance '(InstantFn 2000 1 1 0 30 0) P '?d)))))
      (testing "no gap joins a moment in no zone to an absolute one"
        (is (empty? (v/ask kb (list 'temporalDistance '(StartFn (DatetimeFn "2000-01-01T00:00Z")) P '?d) C))))
      (v/retract! kb h))
    (v/assert kb '(dimensionOf Metre Length) C)
    (v/assert kb (list 'temporalDistance P X '(QuantityFn 5 Metre)) C)
    (v/assert kb (list 'includesInstant '(YearFn 2000) X) C)
    (testing "an instant placed under another key than the stated constraints' joins no network and refuses none"
      (is (= ['Length #{P X}] [(:dimension (stp/problem kb C)) (stp/nodes (:net (stp/problem kb C)))])))))

(tu/deftest-kb the-two-epoch-nodes-lie-within-the-widest-zone-offset-of-each-other
  (load-time-units kb)
  (tu/with-terms [X Y]
    (let [loc '(InstantFn 2000 1 1 0 0 0)
          abs '(StartFn (DatetimeFn "2000-01-01T00:00Z"))]
      (v/assert kb (list 'includesInstant '(DayFn 2000 1 1) X) C)
      (v/assert kb (list 'includesInstant '(DatetimeFn "2000-01-01T12Z") Y) C)
      (testing "a wall-clock reading and the same absolute reading are at most 18 hours apart"
        (is (= '(QuantityIntervalFn -64800 64800 Second) (bound kb (list 'temporalDistance loc abs '?d)))))
      (let [h (v/assert kb (list 'includesInstant '(DatetimeFn "2000-03-01T00Z") X) C)]
        (testing "an instant inside a local day and an absolute hour 60 days later fits no offset"
          (is (inconsistent? kb C))
          (is (empty? (v/ask kb (list 'temporalDistance loc abs '?d) C))))
        (v/retract! kb h)))))

(tu/deftest-kb an-inconsistent-network-answers-nothing-and-is-reported
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    ;; P to Q is an hour and Q to R is an hour, so P to R cannot also be an hour
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 1 Hour)) C)
    (testing "no assignment of times satisfies all three, and the closure proves it"
      (is (inconsistent? kb C))
      (is (nil? (stp/separation kb C P R))))
    (testing "no goal is answered, the pair stated outright included"
      (is (empty? (v/ask kb (list 'temporalDistance P Q '?d) C)))
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C))))
    (testing "the clash is reported"
      (let [entry (first (filter #(= :metric-temporal-inconsistency (:violation %))
                                 (v/violations kb)))]
        (is (some? entry))
        (is (= C (:context entry)))
        (is (= '#{P Q R} (set (map #(get {P 'P, Q 'Q, R 'R} %) (:nodes (:detail entry))))))
        (is (seq (:cycle (:detail entry))) "and it names the instants on the cycle")))
    (testing "retracting one of the three gives the others their answers back"
      (v/retract! kb (v/handle-of kb (list 'temporalDistance P R '(QuantityFn 1 Hour)) C))
      (is (not (inconsistent? kb C)))
      (is (= '(QuantityFn 7200 Second) (bound kb (list 'temporalDistance P R '?d)))))))

(tu/deftest-kb constraints-of-two-dimensions-are-refused-and-reported
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 5 Metre)) C)
    (testing "no network is built, and no goal is answered, the gap stated outright included"
      (is (nil? (stp/problem kb C)))
      (is (empty? (v/ask kb (list 'temporalDistance P Q '?d) C)))
      (let [entry (first (filter #(= :metric-temporal-mixed-dimensions (:violation %))
                                 (v/violations kb)))]
        (is (some? entry))
        (is (= C (:context entry)))
        (is (= '[Duration Length] (:dimensions (:detail entry))))
        (is (= '[Metre Second] (:units (:detail entry))))))
    (testing "a query loop reports once"
      (v/ask kb (list 'temporalDistance P R '?d) C)
      (v/ask kb (list 'temporalDistance Q R '?d) C)
      (is (= 1 (count (filter #(= :metric-temporal-mixed-dimensions (:violation %))
                              (v/violations kb))))))))

(tu/deftest-kb the-constraints-are-read-under-belief-and-visibility
  (load-time-units kb)
  (tu/with-terms [P Q R CxInner]
    (v/assert kb (list 'genlCx CxInner C) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) CxInner)
    (testing "the inner context sees both, so it composes the chain"
      (is (= '(QuantityFn 7200 Second)
             (get (tu/sole-answer (v/ask kb (list 'temporalDistance P R '?d) CxInner)) '?d))))
    (testing "the outer sees only its own, so it composes nothing"
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) C))))
    (testing "retracting a link breaks the chain"
      (v/retract! kb (v/handle-of kb (list 'temporalDistance Q R '(QuantityFn 1 Hour))
                                  CxInner))
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) CxInner))))))

;; ---- one gap, written two ways (docs/stp.md, "Both verdicts are read to the tolerance")

(tu/deftest-kb the-same-gap-written-in-two-units-is-one-constraint
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 66 Minute)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1.1 Hour)) C)
    (testing "the KB's own measure comparison calls the two the same quantity"
      (is (v/ask? kb '(sameQuantity (QuantityFn 66 Minute) (QuantityFn 1.1 Hour)) C)))
    (testing "so the metric layer does not read 3960.0000000000005 and 3960 as crossed"
      (is (not (inconsistent? kb C)))
      (is (= '(QuantityFn 3960 Second) (bound kb (list 'temporalDistance P Q '?d)))))
    (testing "and files nothing"
      (is (empty? (v/violations kb))))))

(tu/deftest-kb a-cycle-a-conversion-opens-is-not-a-contradiction
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1.1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Minute)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 67 Minute)) C)
    (testing "66 minutes then one more is 67: the cycle closing at −5e-13 is no contradiction"
      (is (not (inconsistent? kb C)))
      (is (= '(QuantityFn 4020 Second) (bound kb (list 'temporalDistance P R '?d))))
      (is (empty? (v/violations kb))))))

(tu/deftest-kb noise-a-chain-accumulates-does-not-close-a-cycle
  (load-time-units kb)
  (v/clear-violations! kb)
  (let [ts (mapv (fn [_] (tu/tmp-ind "T")) (range 11))]
    (doseq [i (range 10)]
      (v/assert kb (list 'temporalDistance (ts i) (ts (inc i)) '(QuantityFn 0.1 Second)) C))
    (v/assert kb (list 'temporalDistance (ts 0) (ts 10) '(QuantityFn 1 Second)) C)
    (testing "ten tenths of a second sum to 0.9999999999999999: a −1.1e-16 cycle is no
              contradiction"
      (is (not (inconsistent? kb C))))
    (testing "and the bound renders as the figure"
      (is (= '(QuantityFn 1 Second)
             (bound kb (list 'temporalDistance (ts 0) (ts 10) '?d)))))))

(tu/deftest-kb a-disagreement-wider-than-the-epsilon-is-still-a-contradiction
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 3960 Second)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 3960.000001 Second)) C)
    (testing "a microsecond is a thousand epsilons"
      (is (inconsistent? kb C))
      (is (seq (filter #(= :metric-temporal-inconsistency (:violation %))
                       (v/violations kb)))))
    (testing "and inside a rebound millisecond tolerance, with the KB unchanged"
      (is (not (binding [provers/*quantity-tolerance* 1e-3] (inconsistent? kb C))))
      (is (inconsistent? kb C)))))

(tu/deftest-kb the-metric-layer-and-the-duration-arithmetic-read-one-pair-of-facts-alike
  (v/add-prover kb (dur/duration-prover))
  (load-time-units kb)
  (tu/with-terms [A P Q]
    (v/assert kb (list 'length A '(QuantityFn 66 Minute)) C)
    (v/assert kb (list 'length A '(QuantityFn 1.1 Hour)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 66 Minute)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1.1 Hour)) C)
    (testing "a length and a gap each written in both units read alike"
      (is (= '(QuantityFn 3960 Second)
             (get (tu/sole-answer (v/ask kb (list 'totalDuration (list 'list A) '?d) C)) '?d)))
      (is (= '(QuantityFn 3960 Second) (bound kb (list 'temporalDistance P Q '?d)))))))

;; ---- who is told the network cannot be satisfied --------------------------

(tu/deftest-kb every-context-that-cannot-satisfy-the-constraints-is-told-so
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R CxInner]
    (v/assert kb (list 'genlCx CxInner C) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 1 Hour)) C)
    (testing "the two contexts reach one network and close it once between them"
      (let [passes   (atom 0)
            counting (fn [f] (fn [& args] (swap! passes inc) (apply f args)))]
        (with-redefs [stp/close-state      (counting stp/close-state)
                      stp/close-state-from (counting stp/close-state-from)]
          (is (inconsistent? kb CxInner))
          (is (inconsistent? kb C)))
        (is (<= @passes 1))))
    (testing "and each context is reported, once"
      (let [es (filter #(= :metric-temporal-inconsistency (:violation %)) (v/violations kb))]
        (is (= #{CxInner C} (set (map :context es))))
        (is (= 2 (count es)))))))

(tu/deftest-kb a-second-kb-holding-the-same-constraints-is-told-so-too
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    (let [facts [(list 'temporalDistance P Q '(QuantityFn 1 Hour))
                 (list 'temporalDistance Q R '(QuantityFn 1 Hour))
                 (list 'temporalDistance P R '(QuantityFn 1 Hour))]
          other (doto (tu/isolated-fresh)
                  (tu/load-core!)
                  (v/add-prover (stp/stp-prover)))]
      (try
        (load-time-units other)
        (doseq [s facts] (v/assert kb s C) (v/assert other s C))
        (testing "the two KBs reach the same network"
          (is (inconsistent? kb C))
          (is (inconsistent? other C)))
        (testing "and both are told"
          (is (= 1 (count (filter #(= :metric-temporal-inconsistency (:violation %))
                                  (v/violations kb)))))
          (is (= 1 (count (filter #(= :metric-temporal-inconsistency (:violation %))
                                  (v/violations other))))))
        (finally (tu/clear-kb! other))))))

;; ---- the bridge to the interval algebra ----------------------------------

(defn- bridge-interval
  "Give interval `i` the two bounding instants `s` and `e`."
  [kb i s e]
  (v/assert kb (list 'startOf i s) C)
  (v/assert kb (list 'endOf i e) C))

(tu/deftest-kb the-bridge-needs-both-endpoints-and-a-satisfiable-network
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs]
    (testing "with no metric constraints there is nothing to read"
      (is (nil? (stp/allen-narrowing kb C))))
    (bridge-interval kb A As Ae)
    (v/assert kb (list 'startOf B Bs) C)                  ; no endOf
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (testing "an interval missing one of its bounding instants is not read"
      (is (nil? (get (endpoints-of kb B C) 0)))
      (is (nil? (stp/allen-narrowing kb C))))
    (testing "and neither is an interval whose start is stated of two different instants"
      (tu/with-terms [Bs2]
        (v/assert kb (list 'startOf B Bs2) C)
        (is (nil? (endpoints-of kb B C)))))))

;; ---- the narrowing is a reader of the interval network -------------------

(defmacro ^:private with-allen
  "Run `body` with the Allen prover registered, restoring the registry afterwards."
  [kb & body]
  `(let [before# @(:provers ~kb)]
     (v/add-prover ~kb (iv/allen-prover))
     (try ~@body (finally (reset! (:provers ~kb) before#)))))

(defn- two-hours-apart!
  "A lasts two hours, B three, and B begins an hour after A ends; answers the three
  constraints' handles."
  [kb A B As Ae Bs Be]
  (bridge-interval kb A As Ae)
  (bridge-interval kb B Bs Be)
  [(v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
   (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 3 Hour)) C)
   (v/assert kb (list 'temporalDistance Ae Bs '(QuantityFn 1 Hour)) C)])

(tu/deftest-kb an-interval-goal-is-answered-off-the-measures-alone
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (two-hours-apart! kb A B As Ae Bs Be)
    (testing "the narrowing determines the pair both ways"
      (let [narrowed (stp/allen-narrowing kb C)]
        (is (= #{:before} (get narrowed [A B])))
        (is (= #{:after} (get narrowed [B A])))))
    (testing "the interval network reads it without the Allen prover registered"
      (is (= #{:before} (iv/possible-allen-relations kb C A B)))
      (is (= #{:after} (iv/possible-allen-relations kb C B A))))
    (with-allen kb
      (testing "nobody wrote an interval relation down"
        (is (empty? (v/sentexes-matching kb (list 'before A B) C)))
        (is (empty? (v/sentexes-matching kb (list 'after B A) C))))
      (testing "and the algebra answers both the base relation and the disjunction over it"
        (is (v/ask? kb (list 'before A B) C))
        (is (v/ask? kb (list 'after B A) C))
        (is (v/ask? kb (list 'precedes A B) C))
        (is (v/ask? kb (list 'temporallyDisjoint A B) C)))
      (testing "the refutation comes out of the same network"
        (is (v/ask? kb (list 'not (list 'sharesTimeWith A B)) C))
        (is (not (v/ask? kb (list 'during A B) C)))))))

(tu/deftest-kb what-a-metrically-entailed-interval-relation-rests-on
  (load-time-units kb)
  (tu/with-terms [A B C2 As Ae Bs Be Cs Ce]
    (let [[_ _ h-gap] (two-hours-apart! kb A B As Ae Bs Be)
          _           (bridge-interval kb C2 Cs Ce)          ; related to neither
          h-other     (v/assert kb (list 'temporalDistance Cs Ce '(QuantityFn 9 Hour)) C)
          sup         (iv/allen-support kb C A B)]
      (testing "the gap that decided the pair is named"
        (is (contains? sup h-gap)))
      (testing "and an unrelated interval's constraint is not"
        (is (not (contains? sup h-other))))
      (testing "a pair the constraints do not narrow is not recorded"
        (is (not (contains? (stp/allen-narrowing kb C) [A C2]))))
      (testing "retracting the gap gives the relation back to the algebra"
        (v/retract! kb h-gap)
        (is (not (v/ask? kb (list 'before A B) C)))
        (is (= iv/all-relations (iv/possible-allen-relations kb C A B)))))))

(tu/deftest-kb a-stored-relation-and-a-metric-bound-narrow-one-network-together
  (load-time-units kb)
  (tu/with-terms [A B C2 As Ae Bs Be]
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 3 Hour)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityIntervalFn 1 5 Hour)) C)
    (v/assert kb (list 'before B C2) C)
    (with-allen kb
      (testing "the measures alone leave three relations open between A and B"
        (is (= #{:before :meets :overlaps} (get (stp/allen-narrowing kb C) [A B])))
        (is (= #{:before :meets :overlaps} (iv/possible-allen-relations kb C A B))))
      (testing "and composing them with the stored B-before-C step puts A before C"
        (is (v/ask? kb (list 'before A C2) C))))))

(tu/deftest-kb a-forward-rule-resting-on-a-metric-entailment-is-withdrawn-with-it
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be finishedFirst]
    (with-allen kb
      (v/assert kb (list 'arg finishedFirst 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'before '?x '?y)] (list finishedFirst '?x) C {:direction :forward})
      (let [[_ _ h-gap] (two-hours-apart! kb A B As Ae Bs Be)
            concl (tu/sole-answer (v/sentexes-matching kb (list finishedFirst A) '?ctx)
                                  (list finishedFirst A))]
        (testing "the rule fired on a relation the metric layer entailed and nobody stored"
          (is (some? concl))
          (is (false? (v/premise? kb (:id concl)))))
        (testing "and the proof names the constraint behind it"
          (is (contains? (set (keys (:nodes (v/why kb (:id concl))))) h-gap)))
        (testing "so retracting that constraint takes the conclusion with it"
          (v/retract! kb h-gap)
          (is (empty? (v/sentexes-matching kb (list finishedFirst A) '?ctx))))))))

(tu/deftest-kb an-unsatisfiable-metric-network-withdraws-the-allen-firings-it-licensed
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be D Ds De P Q finishedFirst]
    (with-allen kb
      (v/assert kb (list 'arg finishedFirst 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'before '?x '?y)] (list finishedFirst '?x) C {:direction :forward})
      (let [hs (two-hours-apart! kb A B As Ae Bs Be)
            _  (bridge-interval kb D Ds De)                  ; related to neither
            hd (v/assert kb (list 'temporalDistance Ds De '(QuantityFn 9 Hour)) C)]
        (testing "the rule fires on a relation only the metric layer entails"
          (is (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx))))
        (testing "a negative cycle through instants no interval is bounded by leaves the interval
                  network satisfiable"
          (let [cycle [(v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
                       (v/assert kb (list 'temporalDistance Q P '(QuantityFn 1 Hour)) C)]]
            (is (inconsistent? kb C))
            (is (true? (:consistent? (v/qualitative-network kb :allen C))))
            (is (v/ask? kb (list 'before A B) C))
            (is (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx)))
            (run! #(v/retract! kb %) cycle)))
        ;; B begins an hour after A ends, and A ends an hour after B begins
        (let [h (v/assert kb (list 'temporalDistance Bs Ae '(QuantityFn 1 Hour)) C)]
          (testing "a negative cycle through A's end and B's start makes the interval network
                    unsatisfiable"
            (is (inconsistent? kb C))
            (is (false? (:consistent? (v/qualitative-network kb :allen C))))
            (is (not (v/ask? kb (list 'before A B) C))))
          (testing "the network names the metric cycle as its source, not the pair it emptied"
            (let [net                 (v/qualitative-network kb :allen C)
                  [{:keys [support]
                    :as   src}]          (:unsatisfiable-sources net)]
              (is (empty? (:unsatisfiable net)))
              (is (= [{:source :metric
                       :pairs  (nm/by-print-key #{[Ae Bs] [Bs Ae]})
                       :cycle  (nm/by-print-key #{As Ae Bs})}]
                     (map #(dissoc % :support) (:unsatisfiable-sources net))))
              (is (= #{(hs 0) (hs 2) h}
                     (set (filter #(= 'temporalDistance (first (v/sentence-of (v/sentex kb %))))
                                  (:support src))))
                  "the measures among the cycle's instants, and not B's or D's duration")
              (is (not (contains? (set support) hd)))
              (is (every? #(#{'dimensionOf 'conversionFactor 'temporalDistance}
                            (first (v/sentence-of (v/sentex kb %))))
                          support)
                  "the rest is the unit table the measures converted through")))
          (testing "so the firing is withdrawn, though every fact it listed is still believed"
            (is (empty? (v/sentexes-matching kb (list finishedFirst A) '?ctx))))
          (testing "and retracting the cycle revives it"
            (v/retract! kb h)
            (is (v/ask? kb (list 'before A B) C))
            (is (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx)))))))))

(tu/deftest-kb a-refused-metric-network-withdraws-the-allen-firings-it-licensed
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  ;; each order states the Metre gap before or after the measures the rule fires on, and
  ;; reads the same three things: the firing with the Metre gap stored, the source the
  ;; interval network names, and the firing with the Metre gap retracted
  (let [run (fn [metre-first?]
              (tu/with-terms [A B As Ae Bs Be P Q finishedFirst]
                (with-allen kb
                  (let [metre! #(v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Metre)) C)
                        h      (when metre-first? (metre!))]
                    (v/assert kb (list 'arg finishedFirst 1 'thing) 'CxUniverse {:strength :monotonic})
                    (v/assert-rule kb [(list 'before '?x '?y)] (list finishedFirst '?x) C
                                   {:direction :forward})
                    (two-hours-apart! kb A B As Ae Bs Be)
                    (let [fired-before (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx))
                          h            (or h (metre!))
                          net          (v/qualitative-network kb :allen C)
                          during       {:fired?  (boolean (seq (v/sentexes-matching
                                                                kb (list finishedFirst A) '?ctx)))
                                        :before? (v/ask? kb (list 'before A B) C)
                                        :consistent? (:consistent? net)
                                        :sources (mapv #(dissoc % :support)
                                                       (:unsatisfiable-sources net))}]
                      (v/retract! kb h)
                      {:fired-before (boolean fired-before)
                       :during       during
                       :after        {:fired?  (boolean (seq (v/sentexes-matching
                                                              kb (list finishedFirst A) '?ctx)))
                                      :before? (v/ask? kb (list 'before A B) C)}})))))
        late  (run false)
        early (run true)]
    (testing "the rule fires on a relation only the metric layer entails"
      (is (:fired-before late)))
    (testing "a Metre gap refuses the metric network, so the interval network reading it is
              unsatisfiable, names the refusal as its source, and withdraws the firing"
      (is (= {:fired? false :before? false :consistent? false
              :sources [{:source :metric :dimensions '[Duration Length]}]}
             (:during late))))
    (testing "retracting the Metre gap revives the firing"
      (is (= {:fired? true :before? true} (:after late))))
    (testing "the Metre gap stated first gives the same belief at every step"
      (is (= (dissoc late :fired-before) (dissoc early :fired-before))))))

(tu/deftest-kb the-narrowing-declares-what-moves-it-and-what-names-a-reader
  (testing "every predicate the closure reads is a trigger, the unit table included"
    (is (= '#{temporalDistance includesInstant startOf endOf dimensionOf conversionFactor}
           stp/allen-narrowing-sources)))
  (testing "a calculus folds both sets into its triggers, beside the point network's"
    (is (= (-> (:predicates iv/allen)
               (into stp/allen-narrowing-sources)
               (into (keys pt/instant-denotation)))
           (:trigger-predicates iv/allen)))
    (testing "and a conversionFactor names no reader context"
      (is (contains? (:trigger-predicates iv/allen) 'conversionFactor))
      (is (not (contains? (:context-predicates iv/allen) 'conversionFactor)))
      (is (contains? (:context-predicates iv/allen) 'temporalDistance))
      (is (contains? (:context-predicates iv/allen) 'includesInstant)))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (is (not-any? #(instance? TemporalDistanceProver %) provers/default-provers))
  (testing "registered, it estimates one answer, costs a computation and is authoritative"
    (let [p (stp/stp-prover)]
      (is (= [1 :compute 100] [(prover-types/est-bindings p kb nil C)
                               (prover-types/cost p kb nil C)
                               (prover-types/completeness p kb nil C)]))))
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (testing "a stated constraint is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'temporalDistance P Q '?d) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'temporalDistance P R '?d) C))))
    (testing "the registered prover on the very same facts does"
      (is (= '(QuantityFn 7200 Second) (bound kb (list 'temporalDistance P R '?d)))))))

(tu/deftest-kb a-gap-check-in-the-right-dimension-but-wrong-base-unit-fails
  (load-time-units kb)
  (tu/with-terms [P Q]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 30 Minute)) C)   ; 1800 Second
    (v/assert kb '(dimensionOf Fortnight Duration) C)                       ; no factor
    (testing "the right dimension and magnitude in the wrong base unit is not entailed"
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityFn 1800 Fortnight)) C))))
    (testing "the same gap in the actual base unit still checks"
      (is (v/ask? kb (list 'temporalDistance P Q '(QuantityFn 1800 Second)) C)))))
