;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.calendar-test
  "The calendar clock (`vaelii.impl.calendar`): a calendar term's two bounding moments read
  off its fields, and the orderings that follow.

  Three claims run through all of it.  The convention is **half-open**, so the end of one
  term is the same term as the start of the next and consecutive terms `meet` rather than
  being `before`.  Nothing is **stored** — every test here runs under the net-neutrality
  fixture, which is the check that a computed endpoint leaves no sentex, no justification
  and no term behind.  And the answer is a function of the two terms alone, so it carries
  no support and refuses an open end rather than enumerating the calendar."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.calendar :as cal]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.interval :as interval]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.point :as point]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxTime vocabulary the goals are written in
;; (which is also what the clock's scoping gate reads), the CxChange event calculus the
;; last test drives, and the prover registered.  Opt-in like every other reasoner, so an
;; unregistered KB stores and retrieves calendar facts and pays nothing.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (core-context/load-into)
                        (seed/load-context 'CxTime "upper")
                        (seed/load-context 'CxChange "middle")
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
  ;; `datetime/subinterval?` is what orders a time-keyed CONTEXT (docs/context-nat.md) and
  ;; the clock is what answers a SENTENCE about the terms.  They are separate mechanisms
  ;; over one field reader, and this is the claim that they cannot disagree: `b`'s fields
  ;; being a prefix of `a`'s is the same claim as `a`'s bounds lying inside `b`'s.
  (let [terms '[(YearFn 2000) (YearFn 2001)
                (MonthFn 2000 1) (MonthFn 2000 3) (MonthFn 2000 12) (MonthFn 2001 1)
                (DayFn 2000 1 1) (DayFn 2000 3 15) (DayFn 2000 12 31)
                (DatetimeFn "2000") (DatetimeFn "2000-03") (DatetimeFn "2000-03-15")]
        sub   (interval/interval-denotation 'subintervalOf)
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

(tu/deftest-kb the-clock-answers-only-where-its-vocabulary-is-visible
  ;; CxTime sees CxCore and not the other way about, so a reader down in the grammar has
  ;; no `startOf` to ask about and gets no answer to it.
  (is (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) 'CxUniverse))
  (is (not (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) 'CxCore)))
  (is (empty? (v/ask kb '(startOf (YearFn 2000) ?i) 'CxCore))))

;; ---- what the answer rests on, and what it does not displace ------------

(tu/deftest-kb a-computed-answer-rests-on-nothing-stored
  (testing "the prover reports no support, which is the claim that no retraction reaches it"
    (is (not (satisfies? prover-types/SupportingProver (cal/calendar-prover))))
    (is (= [#{}] (mapv second (provers/solve-goal-with-support
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
  ;; are a source the calculus does not read.  That is `shadowing-channels`' fourth
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

(tu/deftest-kb inertia-over-computed-moments-still-needs-its-edges-written-down
  ;; Pinned rather than swept, and the reason is this test's own subject.  Where the
  ;; event calculus stops is where it reaches `instantBefore` with one end OPEN, and
  ;; which end is open is a fact about the order the conjuncts run in: ranked, the open
  ;; literal is reached first and the calendar prover declines it; unranked, it is
  ;; reached last with both ends already ground and the clock answers, deriving a
  ;; `holdsAt` this test exists to say the theory does not reach.
  (tu/with-pinned [#'plan/*enabled*]
    ;; The clock orders two moments; it supplies no `instantBefore` EDGE.  Both halves of
    ;; the event calculus reach that predicate with one end **open** — "what happened before
    ;; six", not "is three before six" — so both stop at the same place, which is what keeps
    ;; a fluent from being reported as persisting past an event the clock could have ordered
    ;; and the narrative did not (docs/time.md, "What `clipped` can see").
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
          (v/assert kb (list 'terminates RexWakes F t5) W)
          (testing "the clock orders the moments, and the theory reads none of it"
            (is (v/ask? kb (list 'instantBefore t3 t5) W))
            (is (empty? (v/sentexes-matching kb (list 'clipped '?a F '?b) W)))
            (is (not (v/query? kb (list 'holdsAt F t4) W {:max-depth 3}))))
          (doseq [[a b] [[t3 t4] [t4 t5] [t5 t6]]]
            (v/assert kb (list 'instantBefore a b) W))
          (testing "state the links and the whole theory reads them, exactly as it does
                    for an afternoon of named moments"
            (is (v/query? kb (list 'holdsAt F t4) W {:max-depth 3}))
            (is (not (v/query? kb (list 'holdsAt F t6) W {:max-depth 3})))
            (is (seq (v/sentexes-matching kb (list 'clipped t3 F t6) W))))
          (v/retract! kb (v/handle-of kb (list 'instantBefore t5 t6) W))
          (testing "and retracting a link takes the derived reason back with it"
            (is (empty? (v/sentexes-matching kb (list 'clipped t3 F t6) W)))))))))

;; ---- the vocabulary the answers are written in --------------------------

(tu/deftest-kb the-clock-answers-the-whole-shipped-vocabulary-and-only-what-holds
  ;; A predicate the clock answered but the algebras did not name would be one nothing else
  ;; in this tree can compose with, so the rosters are read off the algebras themselves: for
  ;; a pair whose relation is `:during`, exactly the predicates denoting `:during` hold.
  (let [a '(MonthFn 2000 3)
        b '(YearFn 2000)
        i '(InstantFn 1999 6 1 0 0 0)
        j '(InstantFn 2000 1 1 0 0 0)]
    (is (= :during (cal/relation a b)))
    (is (= :before (cal/relation '(YearFn 1999) '(YearFn 2001))))
    (testing "every one of the twenty interval predicates is claimed, and answered by its
              own denotation"
      (is (= (into #{} (keep (fn [[pred rels]] (when (rels :during) pred)))
                   interval/interval-denotation)
             (into #{} (filter #(v/ask? kb (list % a b) C))
                   (keys interval/interval-denotation)))))
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
