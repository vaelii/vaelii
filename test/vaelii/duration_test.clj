;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.duration-test
  "`totalDuration` and `overlapDuration` (`vaelii.impl.duration`). See docs/duration.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.duration :as dur]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu])
  (:import [vaelii.impl.duration DurationProver]))

(use-fixtures :once (tu/loaded #(doto % (tu/load-core!)
                                      (v/add-prover (dur/duration-prover)))))
(use-fixtures :each (tu/neutral))

(def ^:private C 'CxUniverse)

(defn- load-time-units
  "Three units of one dimension, all converting direct to Second — the direct-to-base
  contract the normalization assumes."
  [kb]
  (v/assert kb '(dimensionOf Second Duration)     C)
  (v/assert kb '(dimensionOf Minute Duration)     C)
  (v/assert kb '(dimensionOf Hour Duration)       C)
  (v/assert kb '(conversionFactor Second Second 1)    C)
  (v/assert kb '(conversionFactor Minute Second 60)   C)
  (v/assert kb '(conversionFactor Hour Second 3600)   C))

(defn- bound [kb goal] (get (tu/sole-answer (v/ask kb goal C)) '?d))

;; ---- totalDuration -------------------------------------------------------

(tu/deftest-kb a-total-is-the-sum-rendered-in-the-base-unit
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "two hours and half an hour make 9000 seconds, in the dimension's base unit"
      (is (= '(QuantityFn 9000 Second)
             (bound kb (list 'totalDuration (list 'list A B) '?d)))))
    (testing "an integral magnitude renders as an integer"
      (is (integer? (nth (bound kb (list 'totalDuration (list 'list A B) '?d)) 1))))
    (testing "the components' order"
      (is (= (bound kb (list 'totalDuration (list 'list A B) '?d))
             (bound kb (list 'totalDuration (list 'list B A) '?d)))))))

(tu/deftest-kb a-ground-total-is-checked-in-whatever-unit-it-is-written
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "the rendered answer checks"
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 9000 Second)) C)))
    (testing "so does the same duration in another unit of the dimension"
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 2.5 Hour)) C))
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 150 Minute)) C)))
    (testing "a wrong total does not"
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 9001 Second)) C)))
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 2 Hour)) C))))
    (testing "and neither does the right number in the wrong dimension"
      (v/assert kb '(dimensionOf Metre Length) C)
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 9000 Metre)) C))))))

(tu/deftest-kb one-component-is-its-own-total
  (load-time-units kb)
  (tu/with-terms [A]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (is (= '(QuantityFn 7200 Second) (bound kb (list 'totalDuration (list 'list A) '?d))))))

(tu/deftest-kb a-bounded-length-carries-through-to-a-bounded-total
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityIntervalFn 1 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "the bounds add separately"
      (is (= '(QuantityIntervalFn 5400 9000 Second)
             (bound kb (list 'totalDuration (list 'list A B) '?d)))))
    (testing "and the check form compares both bounds"
      (is (v/ask? kb (list 'totalDuration (list 'list A B)
                           '(QuantityIntervalFn 1.5 2.5 Hour)) C))
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B)
                                '(QuantityIntervalFn 1 2.5 Hour)) C))))))

(tu/deftest-kb the-dimension-check-refuses-to-add-unlike-things
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 5 Metre)) C)
    (testing "two hours plus five metres"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C)))
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 7200 Second)) C))))
    (testing "each on its own still totals"
      (is (= '(QuantityFn 7200 Second) (bound kb (list 'totalDuration (list 'list A) '?d))))
      (is (= '(QuantityFn 5 Metre) (bound kb (list 'totalDuration (list 'list B) '?d)))))))

(tu/deftest-kb a-component-with-no-stated-length-has-no-total
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (testing "B has no stated length"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C))))
    (testing "B's only length is not a structural measure"
      (tu/with-terms [TwoHours]
        (v/assert kb (list 'length B TwoHours) C)
        (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C)))))
    (testing "B has two stated lengths that differ"
      (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
      (is (seq (v/ask kb (list 'totalDuration (list 'list A B) '?d) C)))
      (v/assert kb (list 'length B '(QuantityFn 45 Minute)) C)
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C))))))

(tu/deftest-kb the-same-length-said-twice-is-still-one-length
  (load-time-units kb)
  (tu/with-terms [A B CxInner]
    (v/assert kb (list 'genlCx CxInner C) C)
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length A '(QuantityFn 120 Minute)) CxInner)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    ;; asked in CxInner, which sees both of A's lengths
    (is (= '(QuantityFn 9000 Second)
           (get (tu/sole-answer (v/ask kb (list 'totalDuration (list 'list A B) '?d) CxInner))
                '?d)))))

(tu/deftest-kb the-lengths-are-read-under-belief-and-visibility
  (load-time-units kb)
  (tu/with-terms [A B CxInner]
    (v/assert kb (list 'genlCx CxInner C) C)
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) CxInner)
    (testing "the inner context sees both lengths"
      (is (= '(QuantityFn 9000 Second)
             (get (tu/sole-answer (v/ask kb (list 'totalDuration (list 'list A B) '?d) CxInner))
                  '?d))))
    (testing "the outer sees only its own, so the total has a component it cannot read"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C))))
    (testing "retracting a length takes the total with it"
      (v/retract! kb (v/handle-of kb (list 'length B '(QuantityFn 30 Minute)) CxInner))
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) CxInner))))))

;; ---- overlap-bounds, without a KB ----------------------------------------

(deftest overlap-bounds-reads-the-qualitative-answer-as-a-quantity
  (testing "an inconsistent network has no overlap to measure"
    (is (nil? (#'dur/overlap-bounds #{} [10 10] [4 4]))))
  (testing "every possible relation apart ⇒ exactly zero"
    (is (= [0 0] (#'dur/overlap-bounds #{:before} [10 10] [4 4])))
    (is (= [0 0] (#'dur/overlap-bounds #{:before :after :meets :met-by} [10 10] [4 4])))
    (is (= [0 0] (#'dur/overlap-bounds #{:meets} [10 10] [4 4]))))
  (testing "every possible relation nesting one inside the other ⇒ the contained length"
    (is (= [4 4] (#'dur/overlap-bounds #{:during} [4 4] [10 10])))
    (is (= [4 4] (#'dur/overlap-bounds #{:during :starts :finishes} [4 4] [10 10])))
    (is (= [4 4] (#'dur/overlap-bounds #{:contains} [10 10] [4 4])))
    (is (= [4 4] (#'dur/overlap-bounds #{:equal} [4 4] [4 4]))
        "equality nests both ways, and both readings give the same answer"))
  (testing "anything else is bounded by the shorter of the two, and by nothing below"
    (is (= [0 4] (#'dur/overlap-bounds #{:overlaps} [10 10] [4 4])))
    (is (= [0 4] (#'dur/overlap-bounds #{:before :during} [10 10] [4 4]))
        "a set spanning cases falls through to the over-approximation")
    (is (= [0 4] (#'dur/overlap-bounds #{:before :after :meets :met-by :overlaps}
                                       [10 10] [4 4]))))
  (testing "a bounded length bounds the overlap it contains"
    (is (= [3 5] (#'dur/overlap-bounds #{:during} [3 5] [10 10])))
    (is (= [0 5] (#'dur/overlap-bounds #{:overlaps} [3 5] [10 10]))))
  (testing "a negative upper bound gives a zero overlap, never crossed bounds"
    (is (= [0 0] (#'dur/overlap-bounds #{:overlaps} [-5 -5] [10 10])))))

;; ---- overlapDuration -----------------------------------------------------

(tu/deftest-kb the-overlap-is-read-off-the-possible-relations
  (load-time-units kb)
  (doseq [[rel bind holds fails]
          [['before   '(QuantityFn 0 Second)    ['(QuantityFn 0 Hour)]  ['(QuantityFn 1 Second)]]
           ['contains '(QuantityFn 1800 Second) ['(QuantityFn 30 Minute)] ['(QuantityFn 2 Hour)]]
           ['overlaps '(QuantityIntervalFn 0 1800 Second) ['(QuantityIntervalFn 0 30 Minute)]
            ['(QuantityFn 1800 Second) '(QuantityFn 0 Second)]]]]
    (tu/with-terms [A B]
      (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
      (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
      (v/assert kb (list rel A B) C)
      (testing (str rel)
        (is (= bind (bound kb (list 'overlapDuration A B '?d))))
        (is (= bind (bound kb (list 'overlapDuration B A '?d))))
        (doseq [m holds] (is (v/ask? kb (list 'overlapDuration A B m) C) (pr-str m)))
        (doseq [m fails] (is (not (v/ask? kb (list 'overlapDuration A B m) C)) (pr-str m)))))))

(tu/deftest-kb an-unconstrained-pair-gets-the-widest-answer
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "all thirteen relations possible"
      (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (testing "learning they are disjoint collapses it to zero"
      (v/assert kb (list 'meets A B) C)
      (is (= '(QuantityFn 0 Second) (bound kb (list 'overlapDuration A B '?d)))))))

(tu/deftest-kb a-composed-relation-answers-as-readily-as-an-asserted-one
  (load-time-units kb)
  (tu/with-terms [A B D]
    (v/assert kb (list 'length A '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'length D '(QuantityFn 3 Hour)) C)
    (v/assert kb (list 'during A B) C)
    (v/assert kb (list 'during B D) C)
    (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A D '?d))))))

(tu/deftest-kb an-inconsistent-network-has-no-overlap-at-all
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'after A B) C)
    (testing "before and after cannot both hold"
      (is (empty? (v/ask kb (list 'overlapDuration A B '?d) C)))
      (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 0 Second)) C))))
    (testing "retracting one gives the answer back"
      (v/retract! kb (v/handle-of kb (list 'after A B) C))
      (is (= '(QuantityFn 0 Second) (bound kb (list 'overlapDuration A B '?d)))))))

(tu/deftest-kb an-overlap-needs-both-lengths-and-one-dimension
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'during A B) C)
    (testing "B's length is not stated, so there is nothing to bound the overlap by"
      (is (empty? (v/ask kb (list 'overlapDuration A B '?d) C))))
    (testing "and a length of the wrong dimension is refused rather than compared"
      (v/assert kb (list 'length B '(QuantityFn 5 Metre)) C)
      (is (empty? (v/ask kb (list 'overlapDuration A B '?d) C))))))

(tu/deftest-kb a-negative-length-is-stored-and-read-as-no-length
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn -5 Minute)) C)
    (is (seq (v/sentexes-matching kb (list 'length B '?m) C)))
    (is (empty? (v/ask kb (list 'overlapDuration A B '?d) C)))
    (is (empty? (v/ask kb (list 'overlapDuration B A '?d) C)))
    (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C)))))

;; ---- sharpened by the metric network -------------------------------------

(defn- bridge-interval
  "Give interval `i` the two bounding instants `s` and `e`."
  [kb i s e]
  (v/assert kb (list 'startOf i s) C)
  (v/assert kb (list 'endOf i e) C))

(tu/deftest-kb endpoint-facts-alone-change-nothing
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (testing "no temporalDistance is stated, so nothing sharpens"
      (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (testing "and neither does a constraint about instants these intervals do not bound"
      (tu/with-terms [P Q]
        (v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Minute)) C)
        (is (= '(QuantityIntervalFn 0 1800 Second)
               (bound kb (list 'overlapDuration A B '?d))))))))

(tu/deftest-kb a-metric-network-turns-an-indefinite-overlap-into-a-figure
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "nothing qualitative and nothing metric — the widest answer"
      (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityFn 105 Minute)) C)
    (testing "B begins 105 minutes into A's two hours, so they share fifteen minutes"
      (is (= '(QuantityFn 900 Second) (bound kb (list 'overlapDuration A B '?d))))
      (is (v/ask? kb (list 'overlapDuration A B '(QuantityFn 15 Minute)) C))
      (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 1800 Second)) C))))
    (testing "and the sharpened overlap is symmetric, like the qualitative one"
      (is (= '(QuantityFn 900 Second) (bound kb (list 'overlapDuration B A '?d)))))
    (testing "with no Allen relation stated"
      (is (empty? (v/sentexes-matching kb (list 'overlaps A B) C))))))

(tu/deftest-kb a-sharpened-bound-that-is-still-a-range-says-so
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 1 Hour)) C)
    (testing "the shorter interval is an hour, so that is all the qualitative bound knows"
      (is (= '(QuantityIntervalFn 0 3600 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityIntervalFn 1.5 2.5 Hour)) C)
    (testing "B starts 1.5 to 2.5 hours into A, so the overlap is up to half an hour"
      (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d))))
      (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 1800 Second)) C))))))

(tu/deftest-kb the-metric-and-qualitative-bounds-are-intersected
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityFn 30 Minute)) C)
    (testing "the gaps put B inside A, with and without the stated `during`"
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A B '?d))))
      (v/assert kb (list 'during B A) C)
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (testing "a stated `before` against gaps that put D inside A"
      (tu/with-terms [D Ds De]
        (v/assert kb (list 'length D '(QuantityFn 30 Minute)) C)
        (bridge-interval kb D Ds De)
        (v/assert kb (list 'temporalDistance Ds De '(QuantityFn 30 Minute)) C)
        (v/assert kb (list 'temporalDistance As Ds '(QuantityFn 30 Minute)) C)
        (v/assert kb (list 'before A D) C)      ; but the gaps put D inside A
        (is (empty? (v/ask kb (list 'overlapDuration A D '?d) C)))))))

(tu/deftest-kb a-metric-network-of-another-dimension-is-not-consulted
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 5 Metre)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityFn 1 Metre)) C)
    (testing "gaps in metres"
      (is (= '(QuantityIntervalFn 0 1800 Second)
             (bound kb (list 'overlapDuration A B '?d)))))))

(tu/deftest-kb an-unsatisfiable-metric-network-sharpens-no-overlap
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be P Q]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 30 Minute)) C)
    (testing "a negative cycle through instants that bound neither interval"
      (let [cycle [(v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
                   (v/assert kb (list 'temporalDistance Q P '(QuantityFn 1 Hour)) C)]]
        (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d))))
        (run! #(v/retract! kb %) cycle)))
    (testing "a negative cycle through A's end and B's start"
      (v/assert kb (list 'temporalDistance Ae Bs '(QuantityFn 1 Hour)) C)
      (v/assert kb (list 'temporalDistance Bs Ae '(QuantityFn 1 Hour)) C)
      (is (empty? (v/ask kb (list 'overlapDuration A B '?d) C))))))

(tu/deftest-kb a-determined-overlap-without-both-lengths-answers-nothing
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityFn 105 Minute)) C)
    (is (empty? (v/ask kb (list 'overlapDuration A B '?d) C)))
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (is (= '(QuantityFn 900 Second) (bound kb (list 'overlapDuration A B '?d))))))

(tu/deftest-kb bounds-crossing-within-the-tolerance-collapse-to-a-point
  ;; A's 0.3 s length against an overlap window of 0.4 − 0.1 = 0.30000000000000004 s
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (v/assert kb (list 'length A '(QuantityFn 0.3 Second)) C)
    (v/assert kb (list 'length B '(QuantityFn 1 Second)) C)
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance Bs As '(QuantityFn 0.1 Second)) C)
    (v/assert kb (list 'temporalDistance Bs Ae '(QuantityFn 0.4 Second)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 1 Second)) C)
    (is (= '(QuantityFn 0.3 Second) (bound kb (list 'overlapDuration A B '?d))))))

;; ---- the structure of the goal -----------------------------------------------

(tu/deftest-kb neither-duration-is-assertible
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    ;; The `(list I1 I2 …)` of components is one argument, so `totalDuration` is binary.
    (doseq [[s arity-class] [[(list 'totalDuration (list 'list A B) '(QuantityFn 9000 Second))
                              'binary_predicate]
                             [(list 'overlapDuration A B '(QuantityFn 0 Second))
                              'ternary_predicate]]]
      (is (v/ask? kb (list arity-class (first s)) C) (str (first s) " is a " arity-class))
      (let [e (try (v/assert kb s C) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= :not-well-formed (:type (ex-data e))) (pr-str s))
        (is (empty? (v/sentexes-with-functor kb (first s))))))
    (testing "the computed answer is unchanged"
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 9000 Second)) C)))))

(tu/deftest-kb a-goal-the-prover-cannot-read-is-not-claimed
  (load-time-units kb)
  (tu/with-terms [A]
    ;; one length in the KB, so an open component read as a pattern would match it
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (testing "the components must be a (list …), not a bare interval"
      (is (empty? (v/ask kb (list 'totalDuration A '?d) C))))
    (testing "an open component is not enumerated"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A '?x) '?d) C)))
      (is (empty? (v/ask kb (list 'overlapDuration A '?x '?d) C))))
    (testing "an empty component list"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list) '?d) C))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (testing "no duration arithmetic in the default registry"
    (is (not-any? #(instance? DurationProver %) provers/default-provers))))

(tu/deftest-kb without-the-prover-the-lengths-are-inert
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "a stored length is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'length A '?m) C))))
    (testing "but nothing in the default registry adds two of them up"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'totalDuration (list 'list A B) '?d) C))))
    (testing "the registered prover on the very same facts does"
      (is (= '(QuantityFn 9000 Second) (bound kb (list 'totalDuration (list 'list A B) '?d)))))))

(tu/deftest-kb a-non-finite-magnitude-is-refused-not-stored
  ;; ##Inf and ##NaN are number?s; `assert` and `check` refuse either as a magnitude
  (tu/with-terms [lengthOf IvA CxDur]
    (doseq [s [(list lengthOf IvA (list 'QuantityIntervalFn 0 ##Inf 'Second))
               (list lengthOf IvA (list 'QuantityFn ##NaN 'Second))]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"finite"
                            (v/assert kb s CxDur))
          (pr-str s))
      (is (= [:not-well-formed] (mapv :type (v/check kb s CxDur))) (pr-str s)))
    (testing "a variable magnitude is a pattern, not a measure — still legal"
      (is (some? (v/assert-rule kb [(list lengthOf '?i (list 'QuantityFn '?n 'Second))]
                                (list 'quantified_interval '?i) CxDur))))))

(tu/deftest-kb a-total-in-the-right-dimension-but-wrong-base-unit-does-not-check
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 3 Second)) C)
    (v/assert kb (list 'length B '(QuantityFn 2 Second)) C)   ; total: 5 Second
    (v/assert kb '(dimensionOf Fortnight Duration) C)          ; a dimension, and no factor
    (testing "the right dimension and magnitude in the wrong base unit fails"
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 5 Fortnight)) C))))
    (testing "the same total in the actual base unit still checks"
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 5 Second)) C)))))
