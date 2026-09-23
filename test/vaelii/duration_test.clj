;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.duration-test
  "Interval duration arithmetic (`vaelii.impl.duration`): `totalDuration` and
  `overlapDuration`, computed from the stored `(length I M)` facts, the unit table, and —
  for the overlap — the qualitative Allen relations still possible between two intervals.

  The prover never stores anything and never enumerates: both goals are a computation
  with at most one answer, bound into a variable or checked against a ground measure.
  What the tests are really watching is that the answer stays *honest* — a sum of exact
  lengths renders as a point, a bounded overlap renders as an interval, and a pair whose
  lengths are of different dimensions is refused rather than added up."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.duration :as dur]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu])
  (:import [vaelii.impl.duration DurationProver]))

;; a fresh KB per test: the CxCore grammar, CxMeasure (the measure structural NATs and
;; the dimensionOf / conversionFactor table the magnitudes normalize through),
;; CxTime (the interval relations plus length / totalDuration / overlapDuration),
;; and the prover registered — it is opt-in, so registering it is what turns stored
;; lengths into arithmetic.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxMeasure "upper"] [CxTime "upper"]])
                        (v/add-prover (dur/duration-prover)))))

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
    (testing "an integral magnitude renders as an integer, so the bound answer is `=` to
              the obvious way of writing it"
      (is (integer? (nth (bound kb (list 'totalDuration (list 'list A B) '?d)) 1))))
    (testing "and the components' own order does not change it"
      (is (= (bound kb (list 'totalDuration (list 'list A B) '?d))
             (bound kb (list 'totalDuration (list 'list B A) '?d)))))))

(tu/deftest-kb a-ground-total-is-checked-in-whatever-unit-it-is-written
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "the rendered answer checks"
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 9000 Second)) C)))
    (testing "so does the same duration in any other unit of the dimension — the check
              normalizes, where the bind had to pick one unit to render in"
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
    (testing "an interval measure plus a point is an interval measure — the bounds add
              separately, and the render reports what is not known"
      (is (= '(QuantityIntervalFn 5400 9000 Second)
             (bound kb (list 'totalDuration (list 'list A B) '?d)))))
    (testing "and the check form compares both bounds"
      (is (v/ask? kb (list 'totalDuration (list 'list A B)
                           '(QuantityIntervalFn 1.5 2.5 Hour)) C))
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B)
                                '(QuantityIntervalFn 1 2.5 Hour)) C))))))

(tu/deftest-kb the-dimension-gate-refuses-to-add-unlike-things
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 5 Metre)) C)
    (testing "two hours plus five metres is not a number, so there is no answer at all"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C)))
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 7200 Second)) C))))
    (testing "each on its own still totals"
      (is (= '(QuantityFn 7200 Second) (bound kb (list 'totalDuration (list 'list A) '?d))))
      (is (= '(QuantityFn 5 Metre) (bound kb (list 'totalDuration (list 'list B) '?d)))))))

(tu/deftest-kb a-component-with-no-stated-length-has-no-total
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (testing "an open-world gap is not zero — B might last any time at all"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A B) '?d) C))))
    (testing "and two stated lengths that disagree are a contradiction, not a choice"
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
    (testing "duplicates collapse once normalized, whether restated or reworded, so a
              redundant fact does not read as a disagreement"
      (is (= '(QuantityFn 9000 Second)
             (bound kb (list 'totalDuration (list 'list A B) '?d)))))))

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
    (is (= [0 5] (#'dur/overlap-bounds #{:overlaps} [3 5] [10 10])))))

;; ---- overlapDuration -----------------------------------------------------

(tu/deftest-kb intervals-that-cannot-meet-overlap-for-no-time
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'before A B) C)
    (is (= '(QuantityFn 0 Second) (bound kb (list 'overlapDuration A B '?d))))
    (is (v/ask? kb (list 'overlapDuration A B '(QuantityFn 0 Hour)) C)
        "zero is zero in any unit of the dimension")
    (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 1 Second)) C)))))

(tu/deftest-kb a-contained-interval-overlaps-for-its-whole-length
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'length B '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'during A B) C)
    (testing "A lies wholly inside B, so all thirty minutes of it are shared"
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A B '?d))))
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration B A '?d)))
          "and the overlap is symmetric — the converse relation nests the other way"))))

(tu/deftest-kb a-partial-overlap-is-bounded-not-known
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'overlaps A B) C)
    (testing "the qualitative relation says they share a middle but not how much of one"
      (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d))))
      (is (v/ask? kb (list 'overlapDuration A B '(QuantityIntervalFn 0 30 Minute)) C)))
    (testing "so no point measure is claimed"
      (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 1800 Second)) C)))
      (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 0 Second)) C))))))

(tu/deftest-kb an-unconstrained-pair-gets-the-widest-honest-answer
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "nothing qualitative is stated, so all thirteen relations remain and the
              overlap is anything up to the shorter interval"
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
    (testing "during∘during pins A inside D though nobody said so, so the overlap is all
              of A — the arithmetic reads the tightened network, not the stored facts"
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A D '?d)))))))

(tu/deftest-kb an-inconsistent-network-has-no-overlap-at-all
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'after A B) C)
    (testing "before and after cannot both hold, and an unsatisfiable theory is not
              mined for a number"
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

;; ---- sharpened by the metric network -------------------------------------
;; The qualitative relation set cannot say how much of a partial overlap is shared, so it
;; falls back to `[0, min(len1, len2)]`.  When `vaelii.impl.stp` bounds both intervals'
;; endpoints numerically there is a real answer, and the two sound bounds are intersected.

(defn- bridge-interval
  "Give interval `i` the two bounding instants `s` and `e`."
  [kb i s e]
  (v/assert kb (list 'startOf i s) C)
  (v/assert kb (list 'endOf i e) C))

(tu/deftest-kb endpoint-facts-alone-change-nothing
  ;; the compatibility boundary: naming an interval's endpoints is not a metric constraint,
  ;; so the answer is the qualitative one to the digit
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
    (testing "nothing qualitative and nothing metric — the widest honest answer"
      (is (= '(QuantityIntervalFn 0 1800 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityFn 105 Minute)) C)
    (testing "A runs two hours from its start and B begins an hour and three quarters in, so
              they share the last fifteen minutes of A — and that is a point, not a range"
      (is (= '(QuantityFn 900 Second) (bound kb (list 'overlapDuration A B '?d))))
      (is (v/ask? kb (list 'overlapDuration A B '(QuantityFn 15 Minute)) C))
      (is (not (v/ask? kb (list 'overlapDuration A B '(QuantityFn 1800 Second)) C))))
    (testing "and the sharpened overlap is symmetric, like the qualitative one"
      (is (= '(QuantityFn 900 Second) (bound kb (list 'overlapDuration B A '?d)))))
    (testing "no qualitative fact was needed — the network is silent about the Allen
              relation and the endpoints answered anyway"
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
    (testing "B starts between an hour and a half and two and a half hours in, so it may
              overlap by half an hour or not at all — halving the ceiling without pinning it"
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
    (testing "the metric network puts B wholly inside A, and the qualitative one agrees
              once it is told so — the two meet at the same figure"
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A B '?d))))
      (v/assert kb (list 'during B A) C)
      (is (= '(QuantityFn 1800 Second) (bound kb (list 'overlapDuration A B '?d)))))
    (testing "a qualitative fact contradicting the metric one leaves no overlap both can
              agree on, and there is no number to report"
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
    (testing "gaps measured in metres are not durations, so they cannot narrow one — the
              qualitative answer stands untouched"
      (is (= '(QuantityIntervalFn 0 1800 Second)
             (bound kb (list 'overlapDuration A B '?d)))))))

;; ---- the structure of the goal -----------------------------------------------

(tu/deftest-kb the-list-of-components-is-one-argument
  ;; the declared arity is what a stored sentence is held to, so it has to agree with the
  ;; shape the prover reads: `(totalDuration (list …) D)` is binary, the components being
  ;; a single term, and CxTime declares it so
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "a sentence in the form the prover answers passes the arity check"
      (is (v/assert kb (list 'totalDuration (list 'list A B) '(QuantityFn 9000 Second)) C)))
    (testing "and spreading the components out does not — that would be arity three"
      (is (= :arity (try (v/assert kb (list 'totalDuration A B '(QuantityFn 9000 Second)) C)
                         nil
                         (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
    (testing "overlapDuration is the ternary one"
      (is (v/assert kb (list 'overlapDuration A B '(QuantityFn 0 Second)) C)))))

(tu/deftest-kb a-goal-the-prover-cannot-read-is-not-claimed
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'length B '(QuantityFn 30 Minute)) C)
    (testing "the components must be a (list …), not a bare interval"
      (is (empty? (v/ask kb (list 'totalDuration A '?d) C))))
    (testing "an open component is not enumerated — this computes, it does not search"
      (is (empty? (v/ask kb (list 'totalDuration (list 'list A '?x) '?d) C)))
      (is (empty? (v/ask kb (list 'overlapDuration A '?x '?d) C))))
    (testing "and an empty component list totals nothing, rather than zero of no unit"
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
  ;; ##Inf and ##NaN are number?s, so an infinite bound stored cleanly — and then
  ;; every duration and metric goal in the context threw a raw NumberFormatException
  ;; out of the magnitude arithmetic.  Both entry points refuse it before storage; a
  ;; variable magnitude stays legal, since a rule antecedent binds it.
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
  ;; A unit that declares its dimension but no `conversionFactor` is its own base, so it
  ;; converts only to itself.  A total computed in Seconds must not read equal to the
  ;; same magnitude stated in that unit — five fortnights are not five seconds, though
  ;; both are Durations.
  (load-time-units kb)
  (tu/with-terms [A B]
    (v/assert kb (list 'length A '(QuantityFn 3 Second)) C)
    (v/assert kb (list 'length B '(QuantityFn 2 Second)) C)   ; total: 5 Second
    (v/assert kb '(dimensionOf Fortnight Duration) C)          ; a dimension, and no factor
    (testing "the right dimension and magnitude in the wrong base unit fails"
      (is (not (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 5 Fortnight)) C))))
    (testing "the same total in the actual base unit still checks"
      (is (v/ask? kb (list 'totalDuration (list 'list A B) '(QuantityFn 5 Second)) C)))))
