;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.calendar-test
  "The calendar clock (`vaelii.impl.calendar`): a calendar term's two bounding moments read
  off its fields, and the orderings that follow.  Every test runs under the
  net-neutrality fixture, which checks that a computed endpoint stores nothing."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.calendar :as cal]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.point :as point]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the upper layer, CxChange for the event-calculus tests, and the
;; prover registered.
;; The KB is built per test because a test registers reasoners, which a KB shared
;; across tests would keep.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/empty-kb)
                        (tu/load-core-with! '[[CxChange "middle"]])
                        (v/add-prover (cal/calendar-prover)))))

(def ^:private C 'CxUniverse)

(defn- one
  "The single term `goal`'s one variable binds to, or nil when nothing answers."
  [kb goal var]
  (let [sols (v/ask kb goal C)]
    (when (= 1 (count sols)) (get (first sols) var))))

(defn- starts-at [kb term] (one kb (list 'startOf term '?i) '?i))
(defn- ends-at   [kb term] (one kb (list 'endOf   term '?i) '?i))

;; ---- the endpoints, and the one term per moment -------------------------

(tu/deftest-kb an-endpoint-is-computed-from-the-fields
  (testing "a year begins at its first midnight and ends at the next one"
    (is (= '(InstantFn 2000 1 1 0 0 0) (starts-at kb '(YearFn 2000))))
    (is (= '(InstantFn 2001 1 1 0 0 0) (ends-at   kb '(YearFn 2000)))))
  (testing "and so does every other granularity"
    (is (= '(InstantFn 2000 3 1 0 0 0) (starts-at kb '(MonthFn 2000 3))))
    (is (= '(InstantFn 2000 4 1 0 0 0) (ends-at   kb '(MonthFn 2000 3))))
    (is (= '(InstantFn 2000 1 15 0 0 0) (starts-at kb '(DayFn 2000 1 15))))
    (is (= '(InstantFn 2000 1 16 0 0 0) (ends-at   kb '(DayFn 2000 1 15)))))
  (testing "a reduced-precision ISO term is the same interval, so it has the same moments"
    (is (= (starts-at kb '(MonthFn 2000 3)) (starts-at kb '(DatetimeFn "2000-03"))))
    (is (= (ends-at   kb '(MonthFn 2000 3)) (ends-at   kb '(DatetimeFn "2000-03")))))
  (testing "and ISO's finer fields carry on down to the second"
    (is (= '(InstantFn 2000 1 15 13 0 0) (starts-at kb '(DatetimeFn "2000-01-15T13"))))
    (is (= '(InstantFn 2000 1 15 14 0 0) (ends-at   kb '(DatetimeFn "2000-01-15T13"))))
    (is (= '(InstantFn 2000 1 15 13 30 46)
           (ends-at kb '(DatetimeFn "2000-01-15T13:30:45"))))))

(tu/deftest-kb the-end-of-one-year-and-the-start-of-the-next-are-the-same-term
  ;; The whole reason the convention is half-open and the moment has one spelling: two
  ;; terms that name one moment would not be one moment to anything that compares terms.
  (is (= (ends-at kb '(YearFn 1999)) (starts-at kb '(YearFn 2000))))
  (is (= (ends-at kb '(MonthFn 2000 2)) (starts-at kb '(MonthFn 2000 3))))
  (is (= (ends-at kb '(DayFn 2000 12 31)) (starts-at kb '(YearFn 2001))))
  (testing "and the moment is an instant, where the terms either side of it are stretches"
    (is (dt/instant-term? (ends-at kb '(YearFn 1999))))
    (is (not (dt/calendar-term? (ends-at kb '(YearFn 1999)))))))

(tu/deftest-kb the-calendar-is-the-platform-calendar-and-not-a-table
  (testing "February's length follows the year"
    (is (= '(InstantFn 2000 2 29 0 0 0) (ends-at kb '(DayFn 2000 2 28))))
    (is (= '(InstantFn 1900 3 1 0 0 0)  (ends-at kb '(DayFn 1900 2 28))))
    (is (= '(InstantFn 2000 3 1 0 0 0)  (ends-at kb '(MonthFn 2000 2))))))

(tu/deftest-kb an-endpoint-can-be-checked-as-well-as-bound
  (is (v/ask? kb '(startOf (YearFn 2000) (InstantFn 2000 1 1 0 0 0)) C))
  (is (not (v/ask? kb '(startOf (YearFn 2000) (InstantFn 2000 1 2 0 0 0)) C)))
  (is (not (v/ask? kb '(endOf (YearFn 2000) (InstantFn 2000 12 31 0 0 0)) C))))

;; ---- the convention, read as Allen relations ----------------------------

(tu/deftest-kb consecutive-calendar-terms-meet-and-are-not-before
  ;; Allen's `before` is strict and wants a gap; there is none between 1999 and 2000, so
  ;; what holds is `meets`, and `precedes` is the ordering that covers both.
  (testing "1999 and 2000 touch"
    (is (v/ask? kb '(meets (YearFn 1999) (YearFn 2000)) C))
    (is (v/ask? kb '(precedes (YearFn 1999) (YearFn 2000)) C))
    (is (not (v/ask? kb '(before (YearFn 1999) (YearFn 2000)) C))))
  (testing "with a year between them they do not"
    (is (v/ask? kb '(before (YearFn 1999) (YearFn 2001)) C))
    (is (v/ask? kb '(after (YearFn 2001) (YearFn 1999)) C)))
  (testing "and two consecutive months are the same claim one granularity down"
    (is (v/ask? kb '(meets (MonthFn 2000 2) (MonthFn 2000 3)) C))
    (is (v/ask? kb '(metBy (MonthFn 2000 3) (MonthFn 2000 2)) C))))

(tu/deftest-kb containment-comes-out-as-the-relation-the-fields-say
  (testing "a month with room either side is during its year"
    (is (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) C))
    (is (v/ask? kb '(contains (YearFn 2000) (MonthFn 2000 3)) C)))
  (testing "the first and last months share an end with it instead"
    (is (v/ask? kb '(starts (MonthFn 2000 1) (YearFn 2000)) C))
    (is (v/ask? kb '(finishes (MonthFn 2000 12) (YearFn 2000)) C)))
  (testing "and all three are subintervals, which is the disjunction over them"
    (is (every? #(v/ask? kb (list 'subintervalOf % '(YearFn 2000)) C)
                '[(MonthFn 2000 1) (MonthFn 2000 3) (MonthFn 2000 12)
                  (DayFn 2000 7 4) (YearFn 2000)])))
  (testing "two spellings of one interval are intervalEqual, not two intervals"
    (is (v/ask? kb '(intervalEqual (MonthFn 2000 1) (DatetimeFn "2000-01")) C))
    (is (v/ask? kb '(subintervalOf (DatetimeFn "2000-01-15") (MonthFn 2000 1)) C)))
  (testing "and a sibling month is inside neither the other nor the wrong year"
    (is (not (v/ask? kb '(subintervalOf (MonthFn 2000 2) (MonthFn 2000 1)) C)))
    (is (not (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2001)) C)))
    (is (v/ask? kb '(temporallyDisjoint (MonthFn 2000 1) (MonthFn 2000 2)) C))))

(deftest the-two-readings-of-containment-agree-everywhere
  ;; `datetime/subinterval?` orders time-keyed contexts; the clock answers sentences
  ;; (docs/time.md, "It agrees with the context ordering").
  (let [terms '[(YearFn 2000) (YearFn 2001)
                (MonthFn 2000 1) (MonthFn 2000 3) (MonthFn 2000 12) (MonthFn 2001 1)
                (DayFn 2000 1 1) (DayFn 2000 3 15) (DayFn 2000 12 31)
                (DatetimeFn "2000") (DatetimeFn "2000-03") (DatetimeFn "2000-03-15")]
        sub   (stp/interval-denotation 'subintervalOf)
        wrong (for [a terms b terms
                    :when (not= (dt/subinterval? a b)
                                (contains? sub (cal/relation a b)))]
                [a b (cal/relation a b)])]
    (is (= [] (vec wrong)))))

;; ---- the point algebra over two computed moments ------------------------

(tu/deftest-kb two-computed-moments-are-ordered-by-their-fields
  (testing "the three base relations"
    (is (v/ask? kb '(instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 1 1 0 0 0)) C))
    (is (v/ask? kb '(instantAfter (InstantFn 2000 1 1 0 0 0) (InstantFn 1999 6 1 0 0 0)) C))
    (is (v/ask? kb '(instantEqual (InstantFn 2000 1 1 0 0 0) (InstantFn 2000 1 1 0 0 0)) C))
    (is (not (v/ask? kb '(instantBefore (InstantFn 2000 1 1 0 0 0)
                                        (InstantFn 1999 6 1 0 0 0)) C))))
  (testing "and the three derived ones, which are the complements"
    (is (v/ask? kb '(instantNotAfter (InstantFn 2000 1 1 0 0 0) (InstantFn 2000 1 1 0 0 0)) C))
    (is (v/ask? kb '(instantNotBefore (InstantFn 2000 1 1 0 0 0) (InstantFn 2000 1 1 0 0 0)) C))
    (is (v/ask? kb '(instantNotEqual (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 1 1 0 0 0)) C)))
  (testing "the endpoints of two calendar terms order the terms the same way"
    (is (v/ask? kb (list 'instantBefore (starts-at kb '(YearFn 1999))
                         (starts-at kb '(YearFn 2000)))
                C))
    (is (v/ask? kb (list 'instantEqual (ends-at kb '(YearFn 1999))
                         (starts-at kb '(YearFn 2000)))
                C))))

(tu/deftest-kb a-stated-instant-is-never-invented-an-order
  ;; The clock reads six fields.  `ThreeOClock` has none, so nothing here has anything to
  ;; say about where it falls — only what the KB was told.
  (tu/with-terms [ThreeOClock]
    (is (not (v/ask? kb (list 'instantBefore '(InstantFn 2000 1 1 0 0 0) ThreeOClock) C)))
    (is (not (v/ask? kb (list 'instantAfter ThreeOClock '(InstantFn 2000 1 1 0 0 0)) C)))
    (testing "and a stated ordering is still an ordinary stored fact"
      (v/assert kb (list 'instantBefore ThreeOClock '(InstantFn 2000 1 1 0 0 0)) C)
      (is (v/ask? kb (list 'instantBefore ThreeOClock '(InstantFn 2000 1 1 0 0 0)) C)))))

;; ---- what it refuses ----------------------------------------------------

(tu/deftest-kb an-open-end-answers-nothing-rather-than-enumerating-the-calendar
  (testing "an interval relation needs both terms"
    (is (empty? (v/ask kb '(during ?m (YearFn 2000)) C)))
    (is (empty? (v/ask kb '(during (MonthFn 2000 3) ?y) C)))
    (is (empty? (v/ask kb '(during ?a ?b) C))))
  (testing "and so does an instant ordering"
    (is (empty? (v/ask kb '(instantBefore ?a (InstantFn 2000 1 1 0 0 0)) C)))
    (is (empty? (v/ask kb '(instantBefore ?a ?b) C))))
  (testing "the interval of an endpoint is the one thing that may not be open"
    (is (empty? (v/ask kb '(startOf ?i (InstantFn 2000 1 1 0 0 0)) C)))))

(tu/deftest-kb a-term-the-calendar-cannot-place-has-no-endpoints
  (testing "a date the calendar does not have — stricter than the containment reader,
            which bounds a day at 31 whatever the month"
    (is (dt/subinterval? '(DayFn 2000 2 30) '(MonthFn 2000 2)))
    (is (nil? (dt/bounds '(DayFn 2000 2 30))))
    (is (empty? (v/ask kb '(startOf (DayFn 2000 2 30) ?i) C))))
  (testing "and a term whose end would leave the four-digit year"
    (is (some? (dt/bounds '(YearFn 9998))))
    (is (nil? (dt/bounds '(YearFn 9999))))
    (is (empty? (v/ask kb '(endOf (YearFn 9999) ?i) C)))))

(tu/deftest-kb the-clock-answers-in-a-context-with-no-edge
  ;; Every context sees CxUniverse, so a reader with no `genlCx` edge reads the clock's
  ;; vocabulary there.
  (tu/with-terms [CxOutside]
    (is (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) 'CxUniverse))
    (is (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) CxOutside))
    (is (seq (v/ask kb '(startOf (YearFn 2000) ?i) CxOutside)))))

;; ---- what the answer rests on, and what it does not displace ------------

(tu/deftest-kb a-computed-answer-rests-on-the-time-vocabulary-declaration
  (testing "the answer's support is the declaration the prover's scoping reads"
    (is (satisfies? prover-types/SupportingProver (cal/calendar-prover)))
    (is (some? (v/handle-of kb '(transitive instantBefore) 'CxUniverse)))
    (is (= [#{(v/handle-of kb '(transitive instantBefore) 'CxUniverse)}]
           (mapv second (provers/solve-goal-with-support
                         kb '(during (MonthFn 2000 3) (YearFn 2000)) C)))))
  (testing "and there is no sentex to have a handle — the fixture's net-neutrality check
            is the other half of this"
    (v/ask kb '(startOf (YearFn 2000) ?i) C)
    (is (nil? (v/handle-of kb '(startOf (YearFn 2000) (InstantFn 2000 1 1 0 0 0)) C)))
    (is (empty? (v/sentexes-matching kb '(startOf (YearFn 2000) ?i) C)))))

(tu/deftest-kb a-computed-endpoint-augments-a-stated-one-rather-than-replacing-it
  (tu/with-terms [MillenniumMidnight]
    (v/assert kb (list 'startOf '(YearFn 2000) MillenniumMidnight) C)
    (is (= #{MillenniumMidnight '(InstantFn 2000 1 1 0 0 0)}
           (into #{} (map '?i) (v/ask kb '(startOf (YearFn 2000) ?i) C))))))

(tu/deftest-kb a-calendar-term-stops-a-calculus-running-alone
  ;; `CalculusProver` claims completeness 100 over the network it reads, and correctly —
  ;; but a calendar term appears in no stored fact and so in no network, and its fields
  ;; are a source the calculus does not read.  That is `shadowing-channels`' `:calendar`
  ;; channel, and without it the union would drop the clock's answer.
  (v/add-reasoner kb :allen :point)
  (testing "the channel names the goal's own terms, and no index read decides it"
    (is (contains? (provers/shadowing-channels
                    kb '(during (MonthFn 2000 3) (YearFn 2000)) C)
                   :calendar))
    (is (not (contains? (provers/shadowing-channels kb '(during Breakfast Lunch) C)
                        :calendar))))
  (testing "so both provers run and the clock's answer survives"
    (is (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) C))
    (is (v/ask? kb '(instantBefore (InstantFn 1999 1 1 0 0 0)
                                   (InstantFn 2000 1 1 0 0 0)) C))
    (is (some #{:guarded-by} (mapcat keys (v/query-plan
                                           kb '(during (MonthFn 2000 3) (YearFn 2000)) C))))))

;; ---- where the event calculus stops -------------------------------------

(tu/deftest-kb inertia-over-computed-moments-reads-the-clocks-order
  ;; docs/time.md, "What `clipped` can see"
  (let [W  'CxWell
        t3 '(InstantFn 2000 1 15 15 0 0)
        t4 '(InstantFn 2000 1 15 16 0 0)
        t5 '(InstantFn 2000 1 15 17 0 0)
        t6 '(InstantFn 2000 1 15 18 0 0)]
    (tu/with-terms [AsleepFn Rex RexSleeps RexWakes]
      (let [F (list AsleepFn Rex)]
        (v/assert kb (list 'result AsleepFn 'fluent) W)
        (v/assert kb (list 'happens RexSleeps t3) W)
        (v/assert kb (list 'initiates RexSleeps F t3) W)
        (v/assert kb (list 'happens RexWakes t5) W)
        (let [ends (v/assert kb (list 'terminates RexWakes F t5) W)]
          (testing "the clock orders the moments, so the fluent holds until the event that ends it"
            (is (v/query? kb (list 'holdsAt F t4) W {:max-depth 3}))
            (is (not (v/query? kb (list 'holdsAt F t6) W {:max-depth 3})))
            (is (empty? (v/sentexes-matching kb (list 'clipped '?a F '?b) W))
                "no stored edge orders the moments, so no reason is stored"))
          (doseq [[a b] [[t3 t4] [t4 t5] [t5 t6]]]
            (v/assert kb (list 'instantBefore a b) W))
          (testing "stated links store the reason, and the answers do not move"
            (is (seq (v/sentexes-matching kb (list 'clipped t3 F t6) W)))
            (is (v/query? kb (list 'holdsAt F t4) W {:max-depth 3}))
            (is (not (v/query? kb (list 'holdsAt F t6) W {:max-depth 3}))))
          (v/retract! kb (v/handle-of kb (list 'instantBefore t5 t6) W))
          (testing "retracting a link takes the stored reason back, and the clock still orders the end"
            (is (empty? (v/sentexes-matching kb (list 'clipped t3 F t6) W)))
            (is (not (v/query? kb (list 'holdsAt F t6) W {:max-depth 3}))))
          (v/assert kb (list 'instantBefore t5 t6) W)
          (v/retract! kb ends)
          (testing "retracting the end gives the fluent back past it"
            (is (empty? (v/sentexes-matching kb (list 'clipped t3 F t6) W)))
            (is (v/query? kb (list 'holdsAt F t6) W {:max-depth 3}))))))))

(tu/deftest-kb an-initially-fluent-stops-at-an-event-the-clock-orders
  (let [W  'CxWell
        t4 '(InstantFn 2000 1 15 16 0 0)
        t5 '(InstantFn 2000 1 15 17 0 0)
        t6 '(InstantFn 2000 1 15 18 0 0)]
    (tu/with-terms [IndoorsFn Rex RexLeaves]
      (let [G (list IndoorsFn Rex)]
        (v/assert kb (list 'result IndoorsFn 'fluent) W)
        (v/assert kb (list 'initially G) W)
        (v/assert kb (list 'happens RexLeaves t5) W)
        (let [ends (v/assert kb (list 'terminates RexLeaves G t5) W)]
          (testing "the fluent holds until the event the clock orders before the moment asked"
            (is (v/query? kb (list 'holdsAt G t4) W {:max-depth 3}))
            (is (not (v/query? kb (list 'holdsAt G t6) W {:max-depth 3}))))
          (v/retract! kb ends)
          (testing "retracting the end gives the fluent back past it"
            (is (v/query? kb (list 'holdsAt G t6) W {:max-depth 3}))))))))

(tu/deftest-kb a-NAF-conjunct-the-clock-answers-only-bound-waits-for-its-binder
  ;; The clock literals come first as written, and the join runs them after the generator
  ;; binds ?t.
  (let [t3 '(InstantFn 2000 1 15 15 0 0)
        t5 '(InstantFn 2000 1 15 17 0 0)
        t6 '(InstantFn 2000 1 15 18 0 0)]
    (tu/with-terms [rang Bell]
      (v/assert kb (list rang Bell t5) 'CxWell)
      (let [nothing-rang (fn [a b]
                           (list 'unknown
                                 (list 'thereExists '?t
                                       (list 'and (list 'instantBefore a '?t)
                                             (list 'instantBefore '?t b)
                                             (list rang Bell '?t)))))]
        (is (not (v/ask? kb (nothing-rang t3 t6) 'CxWell)))
        (is (v/ask? kb (nothing-rang t6 t3) 'CxWell))))))

(tu/deftest-kb a-rule-over-stated-bounds-fires-after-its-binder-in-any-order
  (tu/with-terms [tagged early JanJun AprSep]
    (let [at     (fn [m] (list 'InstantFn 2000 m 1 0 0 0))
          fired? #(boolean (seq (v/sentexes-matching kb (list early JanJun) C)))]
      (doseq [[i s e] [[JanJun 1 7] [AprSep 4 10]]]
        (v/assert kb (list 'startOf i (at s)) C)
        (v/assert kb (list 'endOf i (at e)) C))
      (v/assert kb (list tagged JanJun) C)
      (v/assert kb (tu/fwd [(list tagged '?x) (list 'overlaps '?x AprSep)] (list early '?x)) C)
      (testing "the rule arriving last joins the open overlaps literal after tagged binds ?x"
        (is (fired?)))
      (let [second-end (v/assert kb (list 'endOf JanJun (at 3)) C)]
        (testing "a second end leaves the interval no extent"
          (is (not (fired?))))
        (v/retract! kb second-end)
        (testing "retracting the second end re-joins the rule"
          (is (fired?)))))))

(tu/deftest-kb the-functional-at-instant-audit-asks-at-each-event-s-moment
  (let [[t3 t4 t5] (for [h [3 4 5]] (list 'InstantFn 2000 1 1 h 0 0))
        W          'CxWell]
    (tu/with-terms [HostStateFn Svc BoxA BoxB SwapA SwapB Other]
      (v/assert kb (list 'reifiable_function HostStateFn) W)
      (v/assert kb (list 'result HostStateFn 'fluent) W)
      (v/assert kb (list 'functional_at_instant HostStateFn) W)
      (doseq [[e t box] [[SwapA t3 BoxA] [SwapB t4 BoxB]]]
        (v/assert kb (list 'happens e t) W)
        (v/assert kb (list 'initiates e (list HostStateFn Svc box) t) W))
      (v/assert kb (list 'happens Other t5) W)
      (testing "no instantBefore names t5, and the clock orders it after both starts"
        (is (= #{{:function HostStateFn :subject Svc :instant t5 :values #{BoxA BoxB} :kind :merge}}
               (v/functional-at-instant-violations kb HostStateFn W)))))))

(tu/deftest-kb an-open-instant-before-from-a-named-moment-answers-in-any-conjunct-order
  (v/add-reasoner kb :point)
  (let [W  'CxWell
        c2 '(InstantFn 2000 1 5 0 0 0)]
    (tu/with-terms [T1 T9 RexWakes]
      (v/assert kb (list 'time_point T1) W)
      (v/assert kb (list 'time_point T9) W)
      (v/assert kb (list 'instantBefore T1 '(InstantFn 2000 1 1 0 0 0)) W)
      (v/assert kb (list 'instantBefore '(InstantFn 2000 1 20 0 0 0) T9) W)
      (v/assert kb (list 'happens RexWakes c2) W)
      (testing "the point network orders c2, which only a happens fact names, between T1 and T9"
        (is (v/ask? kb (list 'instantBefore T1 c2) W))
        (is (v/ask? kb (list 'instantBefore c2 T9) W)))
      (testing "c2 is no node, so the open instantBefore waits for happens to bind it"
        (doseq [body [[(list 'happens '?e '?i) (list 'instantBefore T1 '?i) (list 'instantBefore '?i T9)]
                      [(list 'instantBefore T1 '?i) (list 'instantBefore '?i T9) (list 'happens '?e '?i)]]
                :let [exists (list 'thereExists '(?e ?i) (cons 'and body))
                      order  (pr-str (mapv first body))]]
          (is (true? (v/ask? kb exists W)) order)
          (is (false? (v/ask? kb (list 'unknown exists) W)) order)
          (is (= #{{'?e RexWakes '?i c2}} (set (v/query kb body W))) order))))))

(tu/deftest-kb an-open-allen-goal-beside-a-calendar-term-answers-in-any-conjunct-order
  (v/add-reasoner kb :allen)
  (let [W 'CxWell, jan '(MonthFn 2000 1)]
    (tu/with-terms [M Bell taggedQ]
      (v/assert kb (list 'during M '(DayFn 2000 1 5)) W)
      (v/assert kb (list taggedQ Bell jan) W)
      (testing "the network places M in January, which no interval fact names"
        (is (v/ask? kb (list 'during M jan) W)))
      (testing "January is no node, so the open during waits for taggedQ to bind it"
        (doseq [body [[(list taggedQ Bell '?m) (list 'during M '?m)]
                      [(list 'during M '?m) (list taggedQ Bell '?m)]]
                :let [exists (list 'thereExists '?m (cons 'and body))
                      order  (pr-str (mapv first body))]]
          (is (true? (v/ask? kb exists W)) order)
          (is (= #{{'?m jan}} (set (v/query kb body W))) order))))))

;; ---- the vocabulary the answers are written in --------------------------

(tu/deftest-kb the-clock-answers-the-whole-shipped-vocabulary-and-only-what-holds
  ;; The predicate lists are read off the algebras: for a pair whose relation is `:during`,
  ;; exactly the predicates denoting `:during` hold.
  (let [a '(MonthFn 2000 3)
        b '(YearFn 2000)
        i '(InstantFn 1999 6 1 0 0 0)
        j '(InstantFn 2000 1 1 0 0 0)]
    (is (= :during (cal/relation a b)))
    (is (= :before (cal/relation '(YearFn 1999) '(YearFn 2001))))
    (testing "every one of the twenty interval predicates is claimed, and answered by its
              own denotation"
      (is (= (into #{} (keep (fn [[pred rels]] (when (rels :during) pred)))
                   stp/interval-denotation)
             (into #{} (filter #(v/ask? kb (list % a b) C))
                   (keys stp/interval-denotation)))))
    (testing "and every one of the six instant predicates, the same way"
      (is (= (into #{} (keep (fn [[pred rels]] (when (rels :before) pred)))
                   point/instant-denotation)
             (into #{} (filter #(v/ask? kb (list % i j) C))
                   (keys point/instant-denotation)))))))

(deftest an-instant-term-has-one-canonical-shape-per-moment
  (testing "an instant term is one canonical shape per moment"
    (is (= '(InstantFn 2000 1 1 0 0 0) (dt/instant-term [2000 1 1 0 0 0])))
    (is (= [2000 1 1 0 0 0] (dt/instant-fields '(InstantFn 2000 1 1 0 0 0))))
    (is (nil? (dt/instant-fields '(InstantFn 2000 1 1))))
    (is (nil? (dt/instant-fields '(InstantFn 2000 2 30 0 0 0))))
    (is (nil? (dt/instant-fields '(YearFn 2000))))))
