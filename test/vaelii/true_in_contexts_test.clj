;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.true-in-contexts-test
  "True in what contexts: the inverse of \"is P true here?\", one fixture per test.

  temporal_capability_test.clj asks of each fixture whether a fact holds in a given
  slice.  This namespace asks the inverse as well: in which contexts is the fact true?
  Each test asks both, and requires that the two answers agree: every context the inverse
  names answers the fact when asked there, and a context the inverse leaves out does not.

  The inverse is spelled the way vaelii already spells it: a goal read at a **variable
  context**, `(v/ask kb s '?where)`, which unifies each witness into `?where`
  (docs/contexts.md, \"The query contexts\").  That read already keeps only the maximal
  witnesses (`taxonomy/maximal-contexts`, called from `vantage/witnessed`): the max-cxs
  of Iris's ruling of 2026-10-24.  What it does not do yet is merge times, so a fact true
  in 2000 and in 2001 is two answers today where it ought to be one answer, 2000 through
  2001.  Merging adjacent times, along one monad only, is what the `^:red` tests here ask
  for.  The helper specifications are in the PR, not in this tree.

  An answer is a **symbolic region**, not a list of existing contexts (Iris, ruled
  2026-10-24): a context term, `(CxTimeFn monad time)` or a monad context, and a `cx/`
  witness is spelled back as the term it was minted from (`natFormula`).  A merged answer
  such as 2000 through 2001 is a term no write has minted,
  `(CxTimeFn CxMonad (DatetimeRangeFn \"2000\" \"2001\"))`, which a list of existing
  context objects could not hold.

  Where more than one set of bindings describes the same region, a test accepts each of
  them.  The bindings need not be disjoint, but none may be entirely redundant with
  respect to another: no binding's region lies inside another's (Iris, 2026-10-24).

  The conventions are temporal_capability_test.clj's: the same fixture, the same
  helpers, the shipped vocabulary, and `^:red` on a test that ought to pass and does not
  yet.  `CxTimeFn` is declared by each test that slices, as that namespace does.
  `genlMonad` is issue #181's name, used only inside `^:red` tests."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

;; The fixture of temporal_capability_test.clj: a fresh KB per test with the upper layer,
;; the CxChange event calculus, CxRealWorld, CxNow and CxRealWorldNow, and no prover.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"] [CxRealWorld "middle"]
                                              [CxNow "middle"] [CxRealWorldNow "middle"]]))))

(def ^:private U 'CxUniverse)

;; ---- the helpers temporal_capability_test.clj has, restated ------------------

(defn- slice
  "The time-sliced context `(CxTimeFn monad time)`."
  ([time] (slice 'CxMonad time))
  ([monad time] (list 'CxTimeFn monad time)))

(defn- year  [y] (list 'DatetimeFn (str y)))
(defn- month [s] (list 'DatetimeFn s))

(defn- declare-cxtimefn!
  "What docs/context-nat.md declares for `CxTimeFn`, as temporal_capability_test.clj
  declares it: its applications are contexts ordered by `subintervalOf` on the time, and
  `CxMonad` sits under CxWell."
  [kb]
  (v/assert kb '(result CxTimeFn context) U)
  (v/assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U)
  (v/assert kb '(genlCx CxMonad CxWell) U))

(defn- monads!
  "Place each of `ms` under CxWell, so each is an ordinary context and a monad."
  [kb & ms]
  (doseq [m ms] (v/assert kb (list 'genlCx m 'CxWell) U)))

(defn- open-from!
  "Make `name` a time_interval that starts at the InstantFn `start` and has no end
  stated: a partially open time."
  [kb name start]
  (v/assert kb (list 'time_interval name) U)
  (v/assert kb (list 'startOf name (cons 'InstantFn start)) U))

;; ---- the inverse query --------------------------------------------------------

(defn- spelled
  "The context term the context `k` was minted from — the `CxTimeFn` application a
  `cx/` constant reifies — or `k` itself when nothing minted it."
  [kb k]
  (or (some #(get % '?e) (v/ask kb (list 'natFormula k '?e) U)) k))

(defn- true-in
  "In which contexts is the ground sentence `s` true: the witnesses a variable-context
  read unifies into `?where`, each spelled as a context term (`spelled`).  A set, so the
  order the read returns them in is no part of the answer."
  [kb s]
  (into #{} (map #(spelled kb (get % '?where))) (v/ask kb s '?where)))

(defn- true-here?
  "Is the sentence `s` true in context `ctx`, the forward question."
  [kb s ctx]
  (true? (v/ask? kb s ctx)))

(defn- mint!
  "Write a fresh fact into each of `ctxs`, so a read naming one of them names a real
  context and not the empty no-match a never-minted slice resolves to
  (temporal_capability_test.clj, a-slice-nobody-wrote-into-still-inherits)."
  [kb & ctxs]
  (doseq [c ctxs] (v/assert kb (list (tu/tmp-pred "mint")) c)))

(defn- agrees?
  "Do the two directions agree for `s`: is `s` true here in every context the inverse
  names?"
  [kb s]
  (every? #(true-here? kb s %) (true-in kb s)))

(defn- sole-time
  "The time of the one slice in `answer`, or nil when `answer` is not one slice, so a
  bound read on a wrong answer fails its assertion rather than throwing."
  [answer]
  (let [region (when (= 1 (count answer)) (first answer))]
    (when (and (seq? region) (= 'CxTimeFn (first region))) (nth region 2))))

;; ---- redundancy between bindings ---------------------------------------------

(defn- year-span
  "The years `[from to]` a slice's time spans, for a `DatetimeFn` year or a
  `DatetimeRangeFn` over two years; nil for any other time."
  [time]
  (when (seq? time)
    (case (first time)
      DatetimeFn      [(parse-long (second time)) (parse-long (second time))]
      DatetimeRangeFn [(parse-long (second time)) (parse-long (nth time 2))]
      nil)))

(defn- inside?
  "Does binding `a`'s region lie inside binding `b`'s: is `a`'s monad `b`'s or below it
  (`below`, a map from a monad to the set of monads above it) and `a`'s year span inside
  `b`'s?  Only slices over years are compared; anything else is not inside."
  [below a b]
  (let [[_ ma ta] (when (seq? a) a)
        [_ mb tb] (when (seq? b) b)
        [a0 a1]   (year-span ta)
        [b0 b1]   (year-span tb)]
    (boolean (and a0 b0
                  (or (= ma mb) (contains? (get below ma #{}) mb))
                  (<= b0 a0 a1 b1)))))

(defn- none-redundant?
  "Is no binding in `answer` entirely redundant with respect to another: does no
  binding's region lie inside another's (`inside?`)?"
  [below answer]
  (not-any? (fn [[a b]] (and (not= a b) (inside? below a b)))
            (for [a answer b answer] [a b])))

;; =========================================================================
;; Monad, time, both, and a partially open time — Iris, 2026-10-24 09:08
;; =========================================================================

(tu/deftest-kb along-time-only-a-fact-in-one-year-is-true-in-that-year
  ;; The time dimension alone: one monad, one write.  The inverse names the year, and the
  ;; forward question agrees at the year, at a month of it, and not at the next year.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [s (list p)]
      (v/assert kb s (slice (year 2000)))
      (mint! kb (slice (month "2000-01")) (slice (year 2001)))
      (testing "the inverse names 2000 along CxMonad, and only it"
        (is (= #{(slice (year 2000))} (true-in kb s))))
      (testing "and the forward question agrees: true in 2000 and its January, not in 2001"
        (is (agrees? kb s))
        (is (true-here? kb s (slice (month "2000-01"))))
        (is (not (true-here? kb s (slice (year 2001)))))))))

(tu/deftest-kb along-the-monad-only-a-fact-in-a-monad-and-its-sub-monad-is-true-in-the-monad
  ;; The monad dimension alone: two monad contexts with no time, the sub-monad placed by
  ;; genlCx, which is how the KB orders monads today.  The fact is written into both; the
  ;; sub-monad adds no claim, so the inverse names the super-monad alone.
  (tu/with-terms [p CxSuper CxSub CxOther]
    (monads! kb CxSuper CxSub CxOther)
    (v/assert kb (list 'genlCx CxSub CxSuper) U)
    (let [s (list p)]
      (v/assert kb s CxSuper)
      (v/assert kb s CxSub)
      (mint! kb CxOther)
      (testing "the inverse names the super-monad and not the sub-monad"
        (is (= #{CxSuper} (true-in kb s))))
      (testing "and the forward question agrees: true along both, not along an unrelated monad"
        (is (agrees? kb s))
        (is (true-here? kb s CxSub))
        (is (not (true-here? kb s CxOther)))))))

(tu/deftest-kb ^:red along-the-monad-only-a-fact-in-a-monad-and-its-genlmonad-sub-monad-is-true-in-the-monad
  ;; The genlMonad twin of along-the-monad-only-a-fact-in-a-monad-and-its-sub-monad-is-true-in-the-monad.
  ;; genlMonad is issue #181's name and the KB does not ship it, so nothing orders the two
  ;; monads and the inverse names both today.
  (tu/with-terms [p CxSuper CxSub CxOther]
    (monads! kb CxSuper CxSub CxOther)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [s (list p)]
      (v/assert kb s CxSuper)
      (v/assert kb s CxSub)
      (mint! kb CxOther)
      (testing "the inverse names the super-monad and not the sub-monad"
        (is (= #{CxSuper} (true-in kb s))))
      (testing "and the forward question agrees: true along both, not along an unrelated monad"
        (is (agrees? kb s))
        (is (true-here? kb s CxSub))
        (is (not (true-here? kb s CxOther)))))))

(tu/deftest-kb along-monad-and-time-the-answer-keeps-both-parts
  ;; Both dimensions: a fact written into one slice along a monad other than CxMonad.  The
  ;; answer is that slice whole — neither the monad nor the time is dropped — so the same
  ;; year along CxMonad is not in it, and the same monad in another year is not.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxStory]
    (monads! kb CxStory)
    (let [s (list p)]
      (v/assert kb s (slice CxStory (year 2000)))
      (mint! kb (slice CxStory (month "2000-01")) (slice (year 2000)) (slice CxStory (year 2001)))
      (testing "the inverse names (CxStory, 2000): the monad and the time together"
        (is (= #{(slice CxStory (year 2000))} (true-in kb s))))
      (testing "and the forward question agrees: true at January along CxStory"
        (is (agrees? kb s))
        (is (true-here? kb s (slice CxStory (month "2000-01")))))
      (testing "and not in 2000 along CxMonad, nor in 2001 along CxStory"
        (is (not (true-here? kb s (slice (year 2000)))))
        (is (not (true-here? kb s (slice CxStory (year 2001)))))))))

(tu/deftest-kb ^:red along-a-partially-open-time-the-answer-is-the-open-region-with-its-stated-bound
  ;; A time that starts at the beginning of 2000 and has no end stated: its end is
  ;; unknown, not infinite.  The fact is written there and at the moment it starts.  A
  ;; vaelii interval is half-open, start in and end out, so that moment is inside the open
  ;; time and the inverse names the open region alone.  The test asserts the bound the answer
  ;; carries and its inclusivity, and that no end is made up: the answer's time has the
  ;; stated start, includes it, and answers no endOf; and 2010, which an assumed endpoint
  ;; would place inside, is not where the fact is true.  Today nothing orders the
  ;; instant's slice under the open time's (an-instant-slice-nobody-wrote-into-still-inherits-from-its-year),
  ;; so the inverse names both.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point :includes-instant)
  (tu/with-terms [p Since2000]
    (open-from! kb Since2000 [2000 1 1 0 0 0])
    (let [s     (list p)
          start '(InstantFn 2000 1 1 0 0 0)]
      (v/assert kb s (slice Since2000))
      (v/assert kb s (slice start))
      (mint! kb (slice (year 1999)) (slice (year 2010)))
      (let [answer (true-in kb s)
            time   (sole-time answer)]
        (testing "the inverse names one region along CxMonad, the open one"
          (is (= #{(slice Since2000)} answer)))
        (testing "its time starts at the stated bound, and the bound is inside it"
          (is (some? time))
          (is (= [{'?i start}] (when time (v/ask kb (list 'startOf time '?i) U))))
          (is (true? (when time (v/ask? kb (list 'includesInstant time start) U)))))
        (testing "and it has no end: nothing answers its endOf, so none was guessed"
          (is (empty? (when time (v/ask kb (list 'endOf time '?i) U))))))
      (testing "the forward question agrees: true at the start, not in 1999, and not in 2010"
        (is (agrees? kb s))
        (is (true-here? kb s (slice start)))
        (is (not (true-here? kb s (slice (year 1999)))))
        (is (not (true-here? kb s (slice (year 2010)))))))))

(tu/deftest-kb ^:red along-a-partially-open-time-a-closed-year-that-meets-it-extends-it-backward
  ;; The merging twin of along-a-partially-open-time-the-answer-is-the-open-region-with-its-stated-bound:
  ;; 1999 meets the open time that starts with 2000, so the two are one region along
  ;; CxMonad, from the start of 1999, with an end as unknown as the open time's.  The
  ;; answer is a term no write minted, so the test asserts its bounds and not its spelling:
  ;; the start of 1999, inside it, and no endOf.  Today the two writes are two answers.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point :includes-instant)
  (tu/with-terms [p Since2000]
    (open-from! kb Since2000 [2000 1 1 0 0 0])
    (let [s     (list p)
          start '(InstantFn 1999 1 1 0 0 0)]
      (v/assert kb s (slice (year 1999)))
      (v/assert kb s (slice Since2000))
      (mint! kb (slice (year 1998)) (slice (year 2010)))
      (testing "control: 1999 ends where the open time starts"
        (is (= [{'?i '(InstantFn 2000 1 1 0 0 0)}] (v/ask kb (list 'endOf (year 1999) '?i) U))))
      (let [answer (true-in kb s)
            region (when (= 1 (count answer)) (first answer))
            time   (sole-time answer)]
        (testing "the inverse names one region, along CxMonad"
          (is (= 1 (count answer)))
          (is (= ['CxTimeFn 'CxMonad] (when (seq? region) (take 2 region)))))
        (testing "it starts where 1999 starts, and that start is inside it"
          (is (some? time))
          (is (= [{'?i start}] (when time (v/ask kb (list 'startOf time '?i) U))))
          (is (true? (when time (v/ask? kb (list 'includesInstant time start) U)))))
        (testing "and it has no end"
          (is (empty? (when time (v/ask kb (list 'endOf time '?i) U)))))
        (testing "the forward question agrees: true in the merged region, not in 1998 or 2010"
          (is (agrees? kb s))
          (is (not (true-here? kb s (slice (year 1998)))))
          (is (not (true-here? kb s (slice (year 2010))))))))))

;; =========================================================================
;; Iris's list — 2026-10-24 09:56
;; =========================================================================
;; Each case is asserted in two contexts and read both ways.  Times are DatetimeFn
;; strings, so a merged answer is a DatetimeRangeFn over two of them.

(tu/deftest-kb asserted-in-2000-and-in-january-2000-is-true-in-2000
  ;; January is inside 2000, so its slice sees 2000's and adds no claim.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [s (list p)]
      (v/assert kb s (slice (year 2000)))
      (v/assert kb s (slice (month "2000-01")))
      (mint! kb (slice (year 2001)))
      (testing "the inverse names 2000 alone"
        (is (= #{(slice (year 2000))} (true-in kb s))))
      (testing "and the forward question agrees, and is false in 2001"
        (is (agrees? kb s))
        (is (true-here? kb s (slice (month "2000-01"))))
        (is (not (true-here? kb s (slice (year 2001)))))))))

(tu/deftest-kb asserted-in-2000-and-in-2010-and-not-between-is-two-bindings
  ;; The two years are not adjacent, so nothing merges them.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [s (list p)]
      (v/assert kb s (slice (year 2000)))
      (v/assert kb s (slice (year 2010)))
      (mint! kb (slice (year 2005)))
      (testing "the inverse names 2000 and 2010, two bindings"
        (is (= #{(slice (year 2000)) (slice (year 2010))} (true-in kb s))))
      (testing "and the forward question agrees, and is false in 2005, between them"
        (is (agrees? kb s))
        (is (not (true-here? kb s (slice (year 2005)))))))))

(tu/deftest-kb ^:red asserted-in-2000-and-in-2001-is-true-in-2000-through-2001
  ;; 2000 meets 2001 (the calendar clock answers it), so the two are one region along
  ;; CxMonad: max-times merges adjacent intervals.  Today the read answers two cx/
  ;; witnesses.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p]
    (let [s      (list p)
          merged (slice '(DatetimeRangeFn "2000" "2001"))]
      (v/assert kb s (slice (year 2000)))
      (v/assert kb s (slice (year 2001)))
      (mint! kb (slice (year 2002)))
      (testing "control: 2000 meets 2001"
        (is (true? (v/ask? kb (list 'meets (year 2000) (year 2001)) U))))
      (testing "the inverse names one region, 2000 through 2001"
        (is (= #{merged} (true-in kb s))))
      (testing "and the forward question agrees there, and is false in 2002"
        (is (true-here? kb s merged))
        (is (agrees? kb s))
        (is (not (true-here? kb s (slice (year 2002)))))))))

(tu/deftest-kb ^:red asserted-in-2000-and-at-an-instant-somewhere-in-2000-is-true-in-2000
  ;; An instant known only to lie in 2000.  Its slice ought to sit under 2000's
  ;; (homogeneity downward), so it adds no claim.  Today nothing orders an instant slice
  ;; under the interval that includes it
  ;; (a-fact-in-a-named-year-slice-holds-in-a-slice-keyed-by-a-named-moment-inside-it), so
  ;; the inverse names both.
  (declare-cxtimefn! kb)
  (tu/with-terms [p Sometime]
    (v/assert kb (list 'time_point Sometime) U)
    (v/assert kb (list 'includesInstant (year 2000) Sometime) U)
    (let [s (list p)]
      (v/assert kb s (slice (year 2000)))
      (v/assert kb s (slice Sometime))
      (testing "the inverse names 2000 alone"
        (is (= #{(slice (year 2000))} (true-in kb s))))
      (testing "and the forward question agrees, at the instant too"
        (is (agrees? kb s))
        (is (true-here? kb s (slice Sometime)))))))

(tu/deftest-kb asserted-in-2000-and-at-an-instant-somewhere-in-2001-is-two-bindings
  ;; An instant known only to lie in 2001 is not inside 2000, and an instant has no
  ;; extent to meet 2000 with, so the two answers stay apart.
  (declare-cxtimefn! kb)
  (tu/with-terms [p Sometime]
    (v/assert kb (list 'time_point Sometime) U)
    (v/assert kb (list 'includesInstant (year 2001) Sometime) U)
    (let [s (list p)]
      (v/assert kb s (slice (year 2000)))
      (v/assert kb s (slice Sometime))
      (mint! kb (slice (year 2001)))
      (testing "the inverse names 2000 and the instant, two bindings"
        (is (= #{(slice (year 2000)) (slice Sometime)} (true-in kb s))))
      (testing "and the forward question agrees, and is false in the rest of 2001"
        (is (agrees? kb s))
        (is (not (true-here? kb s (slice (year 2001)))))))))

(tu/deftest-kb asserted-in-2000-and-at-an-unspecified-instant-is-two-bindings
  ;; An instant nothing locates.  It is not known to be in 2000, so it is not absorbed,
  ;; and not known to be next to it, so it is not merged.
  (declare-cxtimefn! kb)
  (tu/with-terms [p Whenever]
    (v/assert kb (list 'time_point Whenever) U)
    (let [s (list p)]
      (v/assert kb s (slice (year 2000)))
      (v/assert kb s (slice Whenever))
      (testing "the inverse names 2000 and the instant, two bindings"
        (is (= #{(slice (year 2000)) (slice Whenever)} (true-in kb s))))
      (testing "and the forward question agrees"
        (is (agrees? kb s))))))

(tu/deftest-kb ^:red asserted-in-partially-overlapping-ranges-is-true-in-their-union
  ;; The complicated case.  January to June and April to September overlap, May is inside
  ;; both, and November is a month after September ends.  The three overlapping writes are
  ;; one region, January through September, and November stays apart: October is between
  ;; them and the fact is not written there.  Today the read answers January to June,
  ;; April to September and November, since nothing orders the ranges or merges them,
  ;; and the overlap itself is not entailed from the bounds yet
  ;; (two-partially-overlapping-datetime-ranges-and-their-intersection).
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p]
    (let [s       (list p)
          jan-jun '(DatetimeRangeFn "2000-01" "2000-06")
          apr-sep '(DatetimeRangeFn "2000-04" "2000-09")
          jan-sep (slice '(DatetimeRangeFn "2000-01" "2000-09"))]
      (v/assert kb s (slice jan-jun))
      (v/assert kb s (slice apr-sep))
      (v/assert kb s (slice (month "2000-05")))
      (v/assert kb s (slice (month "2000-11")))
      (mint! kb (slice (month "2000-08")) (slice (month "2000-10")) (slice (month "2000-12")))
      (testing "the bounds entail that the two ranges overlap"
        (is (true? (v/ask? kb (list 'overlaps jan-jun apr-sep) U))))
      (testing "the inverse names January through September and November, two bindings"
        (is (= #{jan-sep (slice (month "2000-11"))} (true-in kb s))))
      (testing "and the forward question agrees, and is false in October and December"
        (is (agrees? kb s))
        (is (true-here? kb s (slice (month "2000-08"))))
        (is (not (true-here? kb s (slice (month "2000-10")))))
        (is (not (true-here? kb s (slice (month "2000-12")))))))))

(tu/deftest-kb asserted-in-cxuniverse-and-in-cxwell-is-true-in-cxuniverse
  ;; CxWell sees CxUniverse, so its write adds no claim.
  (tu/with-terms [p CxElsewhere]
    (let [s (list p)]
      (v/assert kb s U)
      (v/assert kb s 'CxWell)
      (mint! kb CxElsewhere)
      (testing "the inverse names CxUniverse alone"
        (is (= #{U} (true-in kb s))))
      (testing "and the forward question agrees, at CxWell too"
        (is (agrees? kb s))
        (is (true-here? kb s 'CxWell))))))

(tu/deftest-kb asserted-in-two-sibling-contexts-is-two-bindings
  ;; Two contexts under CxWell, neither under the other.
  (tu/with-terms [p CxLeft CxRight]
    (monads! kb CxLeft CxRight)
    (let [s (list p)]
      (v/assert kb s CxLeft)
      (v/assert kb s CxRight)
      (testing "the inverse names both siblings, two bindings"
        (is (= #{CxLeft CxRight} (true-in kb s))))
      (testing "and the forward question agrees, and is false at their common parent"
        (is (agrees? kb s))
        (is (not (true-here? kb s 'CxWell)))))))

(tu/deftest-kb ^:red asserted-across-monads-and-times-merges-time-only-where-the-monad-agrees
  ;; Monad and time combined.  CxSub is genlMonad-below CxSuper.  Along CxSuper the fact is
  ;; written in 2000 and in 2001, which merge; along CxSub in January 2000, which the
  ;; super-monad's 2000 absorbs, and in 2002, adjacent to the super-monad's 2001.
  ;;
  ;; Iris ruled this case on 2026-10-24: the answer is two bindings, (CxSuper, 2000
  ;; through 2001) and either (CxSub, 2002) or (CxSub, 2000 through 2002), since CxSub
  ;; sees CxSuper's 2000 and 2001.  Either form is accepted.  Merging times only within
  ;; one monad, which gives (CxSub, 2002), is the suggested cheaper implementation.  The
  ;; bindings may overlap, but neither may lie entirely inside the other.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [s     (list p)
          below {CxSub #{CxSuper}}
          super (slice CxSuper '(DatetimeRangeFn "2000" "2001"))]
      (v/assert kb s (slice CxSuper (year 2000)))
      (v/assert kb s (slice CxSuper (year 2001)))
      (v/assert kb s (slice CxSub (month "2000-01")))
      (v/assert kb s (slice CxSub (year 2002)))
      (mint! kb (slice CxSuper (year 2002)) (slice CxSub (year 2003)))
      (let [answer (true-in kb s)]
        (testing "the inverse names (CxSuper, 2000 through 2001) and (CxSub, 2002 or 2000 through 2002)"
          (is (contains? #{#{super (slice CxSub (year 2002))}
                           #{super (slice CxSub '(DatetimeRangeFn "2000" "2002"))}}
                         answer)))
        (testing "and no binding is entirely redundant with respect to the other"
          (is (none-redundant? below answer))))
      (testing "and the forward question agrees, and is false at the pairs outside both"
        (is (agrees? kb s))
        (is (true-here? kb s (slice CxSub (month "2000-01"))))
        (is (true-here? kb s (slice CxSub (year 2002))))
        (is (not (true-here? kb s (slice CxSuper (year 2002)))))
        (is (not (true-here? kb s (slice CxSub (year 2003)))))))))

(tu/deftest-kb asserted-around-a-genlcx-diamond-is-one-binding-per-monad
  ;; Iris's follow-up to the case above, 2026-10-24.  Four monads in a diamond ordered by
  ;; genlCx: CxBottom under CxLeft and CxRight, each of those under CxTop.  The fact is
  ;; written along CxTop in 1999, CxLeft in 2000, CxRight in 2001 and CxBottom in 2002.
  ;; No write's slice lies inside another's, so the answer is the four bindings as
  ;; written.  CxLeft sees CxTop, so (CxLeft, 1999 through 2000) is also accepted in place
  ;; of (CxLeft, 2000), and CxBottom sees all three monads above it, so (CxBottom, 1999
  ;; through 2002) is also accepted in place of (CxBottom, 2002) (Iris, 2026-10-24).
  ;; CxRight has no merged form: it sees CxTop's 1999 but not CxLeft's 2000, so its 1999
  ;; and 2001 do not meet.  Either way no binding lies entirely inside another.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p CxTop CxLeft CxRight CxBottom]
    (monads! kb CxTop CxLeft CxRight CxBottom)
    (v/assert kb (list 'genlCx CxBottom CxLeft) U)
    (v/assert kb (list 'genlCx CxBottom CxRight) U)
    (v/assert kb (list 'genlCx CxLeft CxTop) U)
    (v/assert kb (list 'genlCx CxRight CxTop) U)
    (let [s       (list p)
          below   {CxBottom #{CxLeft CxRight CxTop} CxLeft #{CxTop} CxRight #{CxTop}}
          written [(slice CxTop (year 1999)) (slice CxLeft (year 2000))
                   (slice CxRight (year 2001)) (slice CxBottom (year 2002))]
          lefts   [(slice CxLeft (year 2000)) (slice CxLeft '(DatetimeRangeFn "1999" "2000"))]
          bottoms [(slice CxBottom (year 2002)) (slice CxBottom '(DatetimeRangeFn "1999" "2002"))]
          accepted (set (for [l lefts b bottoms]
                          #{(slice CxTop (year 1999)) l (slice CxRight (year 2001)) b}))]
      (doseq [c written] (v/assert kb s c))
      (mint! kb (slice CxLeft (year 2001)) (slice CxTop (year 2000)))
      (let [answer (true-in kb s)]
        (testing "the inverse names the four writes, CxLeft's and CxBottom's merged or not"
          (is (contains? accepted answer)))
        (testing "and no binding is entirely redundant with respect to another"
          (is (none-redundant? below answer))))
      (testing "and the forward question agrees at each write"
        (is (agrees? kb s))
        (doseq [c written]
          (is (true-here? kb s c))))
      (testing "and is false along CxLeft in 2001 and along CxTop in 2000"
        (is (not (true-here? kb s (slice CxLeft (year 2001)))))
        (is (not (true-here? kb s (slice CxTop (year 2000)))))))))

;; =========================================================================
;; Joint fixture — normalise (monad, time) pairs together
;; =========================================================================

(tu/deftest-kb sibling-monads-in-adjacent-years-are-two-bindings-and-are-not-merged
  ;; True along CxA during 2000 and along CxB during 2001, CxA and CxB siblings.  The years
  ;; meet, but the monads differ, so the answer is the two pairs as written, and not both
  ;; monads over 2000 through 2001: CxA in 2001 and CxB in 2000 are not true.  This holds
  ;; today and must keep holding once times merge.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p CxA CxB]
    (monads! kb CxA CxB)
    (let [s (list p)]
      (v/assert kb s (slice CxA (year 2000)))
      (v/assert kb s (slice CxB (year 2001)))
      (mint! kb (slice CxA (year 2001)) (slice CxB (year 2000)))
      (testing "control: 2000 meets 2001"
        (is (true? (v/ask? kb (list 'meets (year 2000) (year 2001)) U))))
      (testing "the inverse names (CxA, 2000) and (CxB, 2001), two bindings"
        (is (= #{(slice CxA (year 2000)) (slice CxB (year 2001))} (true-in kb s))))
      (testing "and the forward question agrees, and is false at the crossed pairs"
        (is (agrees? kb s))
        (is (not (true-here? kb s (slice CxA (year 2001)))))
        (is (not (true-here? kb s (slice CxB (year 2000)))))))))
