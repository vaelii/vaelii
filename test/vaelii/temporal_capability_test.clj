;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.temporal-capability-test
  "Temporal reasoning, one capability per test: what works, and what ought to.

  Each test is a small demonstration named for the capability it shows.  A capability
  the engine has is asserted as it works.  A capability it ought to have and lacks is
  asserted as it ought to behave, and the test carries `^:red`: it fails today, the
  `:red` selector is the only one that runs it (project.clj, CONTRIBUTING.md §5), and
  the change that makes it pass drops the mark.  A limit the engine has on purpose is an
  ordinary test asserting the limit, and says why it is one.

  This namespace fills the gaps the existing temporal tests leave.  A capability an
  existing test already demonstrates is cited there and not repeated here; the inventory
  is in the PR that added this file.

  The vocabulary is the shipped one: `time.txt` for the interval, instant and calendar
  predicates, `core.txt` for `result`, `contextArgSubrelation` and `genlCx`, and the
  `CxChange` middle theory for the event calculus, and `CxNow` and `CxRealWorldNow` for
  the present.  Nothing here declares a temporal predicate of its own.  `CxTimeFn` is
  the exception, and the first test says why: the shipped KB names it only in comments
  and docs, so a test that wants a time-sliced context declares it, the way
  docs/context-nat.md does.  The red tests also name what issue #181 asks the KB to ship
  and it does not yet: `genlMonad`, `monad_context`, `CxTimeOfFn`/`cxTimeOf` and
  `CxMonadOfFn`/`cxMonadOf`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.test-util :as tu]))

;; A fresh KB per test, with the upper layer, the CxChange event calculus, CxRealWorld,
;; CxNow and CxRealWorldNow loaded and no prover registered.  Each test registers what it uses, so the opt-in tests can ask the
;; same question before and after.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"] [CxRealWorld "middle"]
                                              [CxNow "middle"] [CxRealWorldNow "middle"]]))))

(def ^:private U 'CxUniverse)

(defn- refusal-type
  "The ex-info `:type` `f` throws, or `:answered` when it returns."
  [f]
  (try (f) :answered
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- slice
  "The time-sliced context `(CxTimeFn monad time)`."
  ([time] (slice 'CxMonad time))
  ([monad time] (list 'CxTimeFn monad time)))

(defn- declare-cxtimefn!
  "Declare what docs/context-nat.md declares for `CxTimeFn`: its applications are
  contexts, and two of them that differ only in the time argument (position 2) are
  ordered by `subintervalOf` on it.  The calendar constructors and `DatetimeFn` are
  already `unreifiable_function` in time.txt, so the time argument stays readable.

  `CxMonad`, the default monad, is placed under CxWell, so a slice along it is a slice
  of an ordinary context and not of a bare key.  Restating a declaration the KB already
  believes changes nothing, so this stays harmless once the KB ships `CxTimeFn`."
  [kb]
  (v/assert kb '(result CxTimeFn context) U)
  (v/assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U)
  (v/assert kb '(genlCx CxMonad CxWell) U))

(defn- cx-of
  "The `cx/` constant the context slot of the sentex at `h` reified to."
  [kb h]
  (:context (v/sentex kb h)))

(defn- verdict
  "`argue`'s verdict for `s` read from `ctx`: `:true`, `:false`, `:unknown` or
  `:contradiction`."
  [kb s ctx]
  (:verdict (v/argue kb s ctx)))

(defn- times!
  "Reify times: make each of `intervals` a time_interval and each of `points` a
  time_point, then state each of `relations`, a vector `[R a b]`, in CxUniverse.  A
  calendar term carries its relations in its fields and a named time carries only what is
  stated, so a twin over named times states the relations its calendar original reads
  off the fields."
  [kb intervals points & relations]
  (doseq [i intervals] (v/assert kb (list 'time_interval i) U))
  (doseq [t points] (v/assert kb (list 'time_point t) U))
  (doseq [r relations] (v/assert kb (apply list r) U)))

(defn- chain!
  "Make each of `points` a time_point and order each one before the next."
  [kb & points]
  (doseq [t points] (v/assert kb (list 'time_point t) U))
  (doseq [[a b] (partition 2 1 points)] (v/assert kb (list 'instantBefore a b) U)))

(defn- monads!
  "Place each of `ms` under CxWell, so each is an ordinary context and a monad."
  [kb & ms]
  (doseq [m ms] (v/assert kb (list 'genlCx m 'CxWell) U)))

;; =========================================================================
;; Context slicing — a fact asserted into a time-keyed context
;; =========================================================================

(tu/deftest-kb ^:red cxtimefn-is-declared-in-the-shipped-kb
  ;; The shipped upper layer and CxChange name `CxTimeFn` only in comments today, so every
  ;; other test here declares it itself (declare-cxtimefn!).
  (testing "the KB believes CxTimeFn's applications are contexts, ordered by subintervalOf on the time"
    (is (true? (v/ask? kb '(result CxTimeFn context) U)))
    (is (true? (v/ask? kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U)))))

(tu/deftest-kb a-write-into-a-time-slice-stores-in-a-cx-context
  ;; (a) The write path reads no declaration.  The application in the context slot
  ;; reifies to an opaque `cx/` constant, and the time argument stays structural inside it.
  (tu/with-terms [p]
    (let [h (v/assert kb (list p) (slice '(DatetimeFn "2000")))
          k (cx-of kb h)]
      (testing "a fact written into (CxTimeFn CxMonad (DatetimeFn \"2000\")) is stored in a cx/ context"
        (is (nat-read/reified-context-symbol? k))
        (is (= [(list 'natFormula k (slice '(DatetimeFn "2000")))]
               (map :sentence (v/sentexes-matching kb (list 'natFormula k '?e) U)))))
      (testing "and a read naming the cx/ constant answers it, with no declaration"
        (is (true? (v/ask? kb (list p) k)))))))

(tu/deftest-kb a-read-naming-a-time-slice-answers-once-cxtimefn-is-declared
  ;; (b) A read that names the application, not the constant, answers while CxUniverse
  ;; believes `(result CxTimeFn context)`.  Without a declaration such a read is refused
  ;; for :shape, naming what is missing; context_nat_test.clj's
  ;; an-undeclared-context-application-is-stored-and-refused-at-the-read shows that on a
  ;; function no KB declares, so it holds whether or not the KB ships CxTimeFn.
  (tu/with-terms [p]
    (let [ctx (slice '(DatetimeFn "2000"))]
      (v/assert kb (list p) ctx)
      (v/assert kb '(result CxTimeFn context) U)
      (testing "the read naming the application answers the fact"
        (is (true? (v/ask? kb (list p) ctx)))))))

(tu/deftest-kb a-fact-in-a-year-slice-is-visible-from-its-month
  ;; (c) With the ordering declared, the producer computes (genlCx month year) from the
  ;; two terms' fields.  Nobody asserts the edge.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q]
    (let [year  (slice '(DatetimeFn "2000"))
          month (slice '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) year)
      (v/assert kb (list q) month)
      (testing "a fact in (DatetimeFn \"2000\") is visible from (DatetimeFn \"2000-01\")"
        (is (true? (v/ask? kb (list p) month))))
      (testing "the month's own fact is not visible from the year"
        (is (not (v/ask? kb (list q) year)))))))

(tu/deftest-kb a-fact-in-a-named-year-slice-is-visible-from-a-named-month-inside-it
  ;; The reified twin of a-fact-in-a-year-slice-is-visible-from-its-month: two named
  ;; intervals, with the relations the calendar fields carry stated between them.  The
  ;; producer reads a stated subintervalOf, so here too nobody asserts the genlCx edge.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q Y2000 Jan2000]
    (times! kb [Y2000 Jan2000] [] ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000])
    (let [year  (slice Y2000)
          month (slice Jan2000)]
      (v/assert kb (list p) year)
      (v/assert kb (list q) month)
      (testing "a fact in the named year is visible from the named month inside it"
        (is (true? (v/ask? kb (list p) month))))
      (testing "the month's own fact is not visible from the year"
        (is (not (v/ask? kb (list q) year)))))))

(tu/deftest-kb ^:red a-slice-nobody-wrote-into-still-inherits
  ;; Today a read resolves the slot by dedup and never mints, so a slice with no fact of
  ;; its own has no cx/ constant and the read is scoped to nothing (docs/context-nat.md,
  ;; "Write and read are symmetric").  What a slice sees ought to follow from what it
  ;; names, not from whether anybody has written into it.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [year (slice '(DatetimeFn "2000"))
          jan  (slice '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) year)
      (testing "the year's fact is visible from a month slice that holds no fact of its own"
        (is (true? (v/ask? kb (list p) jan)))
        (is (= :true (verdict kb (list p) jan)))))))

(tu/deftest-kb ^:red a-named-slice-nobody-wrote-into-still-inherits
  ;; The reified twin of a-slice-nobody-wrote-into-still-inherits: the month is a named
  ;; interval with a stated subintervalOf, and nobody writes into its slice.
  (declare-cxtimefn! kb)
  (tu/with-terms [p Y2000 Jan2000]
    (times! kb [Y2000 Jan2000] [] ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000])
    (let [year (slice Y2000)
          jan  (slice Jan2000)]
      (v/assert kb (list p) year)
      (testing "the named year's fact is visible from a named month slice that holds no fact of its own"
        (is (true? (v/ask? kb (list p) jan)))
        (is (= :true (verdict kb (list p) jan)))))))

(tu/deftest-kb ^:red an-instant-slice-nobody-wrote-into-still-inherits-from-its-year
  ;; The point twin of a-slice-nobody-wrote-into-still-inherits: the unwritten slice is
  ;; keyed by a moment of 2000 rather than by its January.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [year (slice '(DatetimeFn "2000"))
          noon (slice '(InstantFn 2000 6 1 12 0 0))]
      (v/assert kb (list p) year)
      (testing "the year's fact is visible from a moment's slice that holds no fact of its own"
        (is (true? (v/ask? kb (list p) noon)))
        (is (= :true (verdict kb (list p) noon)))))))

(tu/deftest-kb ^:red a-slice-along-a-sub-monad-nobody-wrote-into-still-inherits
  ;; The monad-dimension twin of a-slice-nobody-wrote-into-still-inherits: the unwritten
  ;; slice narrows the monad, not the time.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [sup (slice CxSuper '(DatetimeFn "2000"))
          sub (slice CxSub '(DatetimeFn "2000"))]
      (v/assert kb (list p) sup)
      (testing "the super-monad's 2000 fact is visible from the sub-monad's 2000 slice, which holds no fact of its own"
        (is (true? (v/ask? kb (list p) sub)))
        (is (= :true (verdict kb (list p) sub)))))))

(tu/deftest-kb a-fact-in-a-year-slice-holds-in-its-months-and-is-unknown-the-next-year
  ;; Iris's second example.  "Unknown" is read with `argue`: neither p nor (not p)
  ;; answers.  2001 is a sibling of 2000, so it sees nothing stated for 2000.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [y2000 (slice '(DatetimeFn "2000"))
          jan   (slice '(DatetimeFn "2000-01"))
          y2001 (slice '(DatetimeFn "2001"))]
      (v/assert kb (list p) y2000)
      ;; a fact in each of January and 2001 mints those contexts, so the reads below name
      ;; real contexts (see a-slice-nobody-wrote-into-inherits-nothing)
      (tu/with-terms [q r]
        (v/assert kb (list q) y2001)
        (v/assert kb (list r) jan)
        (testing "p stated for 2000 is true in 2000 and in January 2000"
          (is (= :true (verdict kb (list p) y2000)))
          (is (= :true (verdict kb (list p) jan))))
        (testing "and unknown in 2001: neither p nor its negation answers there"
          (is (= :unknown (verdict kb (list p) y2001)))
          (is (not (v/ask? kb (list 'not (list p)) y2001))))))))

(tu/deftest-kb a-fact-in-a-named-year-slice-holds-in-a-named-month-and-is-unknown-the-named-next-year
  ;; The reified twin of a-fact-in-a-year-slice-holds-in-its-months-and-is-unknown-the-next-year.
  ;; The calendar fields say that January starts 2000, that 2000 meets 2001 and that
  ;; January is before 2001, so those are the relations stated between the names.
  (declare-cxtimefn! kb)
  (tu/with-terms [p Y2000 Jan2000 Y2001]
    (times! kb [Y2000 Jan2000 Y2001] []
            ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000]
            ['meets Y2000 Y2001] ['before Jan2000 Y2001])
    (let [y2000 (slice Y2000)
          jan   (slice Jan2000)
          y2001 (slice Y2001)]
      (v/assert kb (list p) y2000)
      (tu/with-terms [q r]
        (v/assert kb (list q) y2001)
        (v/assert kb (list r) jan)
        (testing "p stated for the named 2000 is true there and in the named January"
          (is (= :true (verdict kb (list p) y2000)))
          (is (= :true (verdict kb (list p) jan))))
        (testing "and unknown in the named 2001: neither p nor its negation answers there"
          (is (= :unknown (verdict kb (list p) y2001)))
          (is (not (v/ask? kb (list 'not (list p)) y2001))))))))

(tu/deftest-kb ^:red a-fact-in-a-year-slice-holds-at-an-instant-inside-it-and-is-unknown-at-an-instant-of-the-next-year
  ;; The point twin of a-fact-in-a-year-slice-holds-in-its-months-and-is-unknown-the-next-year:
  ;; a moment of 2000 in place of January, and a moment of 2001 in place of 2001.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [y2000    (slice '(DatetimeFn "2000"))
          noon     (slice '(InstantFn 2000 6 1 12 0 0))
          noon2001 (slice '(InstantFn 2001 6 1 12 0 0))]
      (v/assert kb (list p) y2000)
      (tu/with-terms [q r]
        (v/assert kb (list q) noon2001)
        (v/assert kb (list r) noon)
        (testing "p stated for 2000 is true in 2000 and at a moment of 2000"
          (is (= :true (verdict kb (list p) y2000)))
          (is (= :true (verdict kb (list p) noon))))
        (testing "and unknown at a moment of 2001: neither p nor its negation answers there"
          (is (= :unknown (verdict kb (list p) noon2001)))
          (is (not (v/ask? kb (list 'not (list p)) noon2001))))))))

(tu/deftest-kb ^:red a-fact-in-a-super-monads-slice-holds-along-its-sub-monad-and-is-unknown-along-an-unrelated-monad
  ;; The monad-dimension twin of a-fact-in-a-year-slice-holds-in-its-months-and-is-unknown-the-next-year:
  ;; the sub-monad takes the month's place and an unrelated monad the next year's.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxSuper CxSub CxOther]
    (monads! kb CxSuper CxSub CxOther)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [sup   (slice CxSuper '(DatetimeFn "2000"))
          sub   (slice CxSub '(DatetimeFn "2000"))
          other (slice CxOther '(DatetimeFn "2000"))]
      (v/assert kb (list p) sup)
      (tu/with-terms [q r]
        (v/assert kb (list q) other)
        (v/assert kb (list r) sub)
        (testing "p stated along the super-monad is true there and along the sub-monad"
          (is (= :true (verdict kb (list p) sup)))
          (is (= :true (verdict kb (list p) sub))))
        (testing "and unknown along the unrelated monad: neither p nor its negation answers there"
          (is (= :unknown (verdict kb (list p) other)))
          (is (not (v/ask? kb (list 'not (list p)) other))))))))

(tu/deftest-kb ^:red a-fact-stated-unsliced-holds-in-every-year-slice
  ;; Iris's first example.  The KB has no "eternal" or "atemporal" context: `atemporal`
  ;; is a type of thing (core.txt), not a way of stating a fact.  The nearest is a fact
  ;; stated unsliced, in CxUniverse — the root every wired context sees.  Today a cx/
  ;; slice is wired by nothing but the computed edges between slices and sees nothing
  ;; above it (docs/contexts.md, "A context outside the topology"), and the year was
  ;; reached only by a hand-asserted genlCx on its cx/ constant.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [y2000 (slice '(DatetimeFn "2000"))
          jan   (slice '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) U)
      (let [k (cx-of kb (v/assert kb (list q) y2000))]
        (v/assert kb (list r) jan)
        (testing "the 2000 slice sees CxUniverse, and p stated there is true in 2000"
          (is (true? (v/sees? kb k U)))
          (is (true? (v/ask? kb (list p) y2000)))
          (is (= :true (verdict kb (list p) y2000))))
        (testing "and in January 2000, with nobody wiring either slice by hand"
          (is (true? (v/ask? kb (list p) jan))))))))

(tu/deftest-kb ^:red a-fact-stated-unsliced-holds-in-every-year-slice-along-a-monad-placed-by-genlmonad
  ;; The genlMonad twin of a-fact-stated-unsliced-holds-in-every-year-slice.  The original
  ;; reaches CxUniverse through CxMonad's stated genlCx to CxWell; here the slices are
  ;; along a monad that genlMonad alone places under CxWell.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxStory]
    (v/assert kb (list 'genlMonad CxStory 'CxWell) U)
    (let [y2000 (slice CxStory '(DatetimeFn "2000"))
          jan   (slice CxStory '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) U)
      (let [k (cx-of kb (v/assert kb (list q) y2000))]
        (v/assert kb (list r) jan)
        (testing "the 2000 slice sees CxUniverse, and p stated there is true in 2000"
          (is (true? (v/sees? kb k U)))
          (is (true? (v/ask? kb (list p) y2000)))
          (is (= :true (verdict kb (list p) y2000))))
        (testing "and in January 2000, with nobody wiring either slice by hand"
          (is (true? (v/ask? kb (list p) jan))))))))

(tu/deftest-kb ^:red a-fact-in-cxwells-year-slice-holds-that-year-along-every-monad-below-cxwell
  ;; The monad-dimension twin of a-fact-stated-unsliced-holds-in-every-year-slice.  The
  ;; original states a fact at no time in particular, along the root, and reads it at
  ;; years; this states one at a year along CxWell, the monad every other monad here sits
  ;; under, and reads it at that year along two monads below it, and at a month of it.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxWell) U)
    (v/assert kb (list 'genlMonad CxStory 'CxWell) U)
    (let [top   (cx-of kb (v/assert kb (list p) (slice 'CxWell '(DatetimeFn "2000"))))
          story (cx-of kb (v/assert kb (list q) (slice CxStory '(DatetimeFn "2000"))))]
      (testing "the 2000 slice along CxStory sees the 2000 slice along CxWell, and p stated there is true"
        (is (true? (v/sees? kb story top)))
        (is (true? (v/ask? kb (list p) (slice CxStory '(DatetimeFn "2000")))))
        (is (= :true (verdict kb (list p) (slice CxStory '(DatetimeFn "2000"))))))
      (testing "and along CxMonad, and at January 2000 along either"
        (is (true? (v/ask? kb (list p) (slice '(DatetimeFn "2000")))))
        (is (true? (v/ask? kb (list p) (slice CxStory '(DatetimeFn "2000-01")))))
        (is (true? (v/ask? kb (list p) (slice '(DatetimeFn "2000-01")))))))))

(tu/deftest-kb ^:red a-slice-along-a-monad-under-cxwell-sees-cxwell-and-not-the-reverse
  ;; (d) CxWell is the shipped bottom anchor, below CxChange.  CxMonad sits under it
  ;; (declare-cxtimefn!), so a slice along CxMonad ought to see CxWell through its monad.
  ;; Today there is no edge either way.  The reverse stays closed: a fact true in 2000
  ;; need not be true in general.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q]
    (let [y2000 (slice '(DatetimeFn "2000"))]
      (v/assert kb (list p) 'CxWell)
      (v/assert kb (list q) y2000)
      (testing "a CxWell fact is visible from the 2000 slice"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "a 2000-slice fact is not visible from CxWell"
        (is (not (v/ask? kb (list q) 'CxWell)))))))

(tu/deftest-kb ^:red a-slice-along-a-monad-genlmonad-below-cxwell-sees-cxwell-and-not-the-reverse
  ;; The genlMonad twin of a-slice-along-a-monad-under-cxwell-sees-cxwell-and-not-the-reverse:
  ;; the monad is placed under CxWell by genlMonad, where CxMonad is placed by genlCx.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (v/assert kb (list 'genlMonad CxStory 'CxWell) U)
    (let [y2000 (slice CxStory '(DatetimeFn "2000"))]
      (v/assert kb (list p) 'CxWell)
      (v/assert kb (list q) y2000)
      (testing "a CxWell fact is visible from the 2000 slice"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "a 2000-slice fact is not visible from CxWell"
        (is (not (v/ask? kb (list q) 'CxWell)))))))

(tu/deftest-kb sibling-month-slices-do-not-see-each-other
  ;; (e) January and February are siblings: neither is a subinterval of the other, so the
  ;; producer orders neither under the other, and each sees only its own facts and the
  ;; year's.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [year (slice '(YearFn 2000))
          jan  (slice '(MonthFn 2000 1))
          feb  (slice '(MonthFn 2000 2))]
      (v/assert kb (list r) year)
      (v/assert kb (list p) jan)
      (v/assert kb (list q) feb)
      (testing "each month sees the year"
        (is (true? (v/ask? kb (list r) jan)))
        (is (true? (v/ask? kb (list r) feb))))
      (testing "and neither month sees the other's facts"
        (is (not (v/ask? kb (list p) feb)))
        (is (not (v/ask? kb (list q) jan)))))))

(tu/deftest-kb sibling-named-month-slices-do-not-see-each-other
  ;; The reified twin of sibling-month-slices-do-not-see-each-other: each named month is a
  ;; stated subinterval of the named year, and January meets February.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r Y2000 Jan2000 Feb2000]
    (times! kb [Y2000 Jan2000 Feb2000] []
            ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000]
            ['during Feb2000 Y2000] ['subintervalOf Feb2000 Y2000]
            ['meets Jan2000 Feb2000])
    (let [year (slice Y2000)
          jan  (slice Jan2000)
          feb  (slice Feb2000)]
      (v/assert kb (list r) year)
      (v/assert kb (list p) jan)
      (v/assert kb (list q) feb)
      (testing "each named month sees the named year"
        (is (true? (v/ask? kb (list r) jan)))
        (is (true? (v/ask? kb (list r) feb))))
      (testing "and neither month sees the other's facts"
        (is (not (v/ask? kb (list p) feb)))
        (is (not (v/ask? kb (list q) jan)))))))

(tu/deftest-kb ^:red two-instant-slices-in-one-year-each-see-the-year-and-not-each-other
  ;; The point twin of sibling-month-slices-do-not-see-each-other: two moments of 2000 in
  ;; place of two of its months.  Two distinct moments are ordered, never nested, so
  ;; neither slice is under the other.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [year (slice '(YearFn 2000))
          jan  (slice '(InstantFn 2000 1 15 12 0 0))
          feb  (slice '(InstantFn 2000 2 15 12 0 0))]
      (v/assert kb (list r) year)
      (v/assert kb (list p) jan)
      (v/assert kb (list q) feb)
      (testing "each moment's slice sees the year"
        (is (true? (v/ask? kb (list r) jan)))
        (is (true? (v/ask? kb (list r) feb))))
      (testing "and neither sees the other's facts"
        (is (not (v/ask? kb (list p) feb)))
        (is (not (v/ask? kb (list q) jan)))))))

(defn- two-spellings
  "Write one fact into the `first` spelling of January 2000, then one into the `second`,
  and report which sees the other's fact."
  [kb first second]
  (tu/with-terms [p q]
    (let [k1 (cx-of kb (v/assert kb (list p) first))
          k2 (cx-of kb (v/assert kb (list q) second))]
      {:distinct?           (not= k1 k2)
       :first-sees-second?  (boolean (v/ask? kb (list q) first))
       :second-sees-first?  (boolean (v/ask? kb (list p) second))})))

(tu/deftest-kb ^:red two-spellings-of-one-month-see-each-others-facts
  ;; docs/context-nat.md: (MonthFn 2000 1) and (DatetimeFn "2000-01") name the same
  ;; interval, and the comparator reads both to one field vector.  Today, as context slots,
  ;; they are two expressions and reify to two cx/ constants; each is a subinterval of the
  ;; other, the second edge would close a genlCx cycle and is refused, and the one edge
  ;; that survives is the same in either arrival order: the MonthFn slice sees the
  ;; DatetimeFn slice and not the reverse.  One month ought to see its own facts whichever
  ;; way it is spelled.  Whether the two are one context is
  ;; two-spellings-of-one-month-name-one-context.
  (declare-cxtimefn! kb)
  (testing "MonthFn written first: each spelling sees the other's fact"
    (is (= {:first-sees-second? true :second-sees-first? true}
           (dissoc (two-spellings kb (slice '(MonthFn 2000 1)) (slice '(DatetimeFn "2000-01")))
                   :distinct?))))
  (tu/with-terms [CxOther]
    (v/assert kb (list 'genlCx CxOther 'CxWell) U)
    (testing "DatetimeFn written first, along a fresh monad so both slices are new: the same"
      (is (= {:first-sees-second? true :second-sees-first? true}
             (dissoc (two-spellings kb (slice CxOther '(DatetimeFn "2000-01"))
                                    (slice CxOther '(MonthFn 2000 1)))
                     :distinct?))))))

(tu/deftest-kb ^:red two-names-of-one-interval-see-each-others-facts
  ;; The reified twin of two-spellings-of-one-month-see-each-others-facts.  The calendar
  ;; comparator finds each spelling a subinterval of the other; here the two names are
  ;; stated intervalEqual and each a subintervalOf the other, so the second computed edge
  ;; would close a genlCx cycle exactly as it does for the two spellings.
  (declare-cxtimefn! kb)
  (tu/with-terms [JanA JanB]
    (times! kb [JanA JanB] []
            ['intervalEqual JanA JanB] ['subintervalOf JanA JanB] ['subintervalOf JanB JanA])
    (testing "JanA written first: each name sees the other's fact"
      (is (= {:first-sees-second? true :second-sees-first? true}
             (dissoc (two-spellings kb (slice JanA) (slice JanB)) :distinct?))))
    (tu/with-terms [CxOther]
      (v/assert kb (list 'genlCx CxOther 'CxWell) U)
      (testing "JanB written first, along a fresh monad so both slices are new: the same"
        (is (= {:first-sees-second? true :second-sees-first? true}
               (dissoc (two-spellings kb (slice CxOther JanB) (slice CxOther JanA))
                       :distinct?)))))))

(tu/deftest-kb ^:red two-spellings-of-one-moment-see-each-others-facts
  ;; The point twin of two-spellings-of-one-month-see-each-others-facts.  An InstantFn term
  ;; is a moment's one calendar spelling, and the start of a calendar term is another
  ;; spelling of a moment (time.txt): (StartFn (MonthFn 2000 1)) is midnight at the start
  ;; of 2000, the moment (InstantFn 2000 1 1 0 0 0) names.  One moment ought to see its
  ;; own facts whichever way it is spelled.
  (declare-cxtimefn! kb)
  (let [instant '(InstantFn 2000 1 1 0 0 0)
        start   '(StartFn (MonthFn 2000 1))]
    (testing "InstantFn written first: each spelling sees the other's fact"
      (is (= {:first-sees-second? true :second-sees-first? true}
             (dissoc (two-spellings kb (slice instant) (slice start)) :distinct?))))
    (tu/with-terms [CxOther]
      (v/assert kb (list 'genlCx CxOther 'CxWell) U)
      (testing "StartFn written first, along a fresh monad so both slices are new: the same"
        (is (= {:first-sees-second? true :second-sees-first? true}
               (dissoc (two-spellings kb (slice CxOther start) (slice CxOther instant))
                       :distinct?)))))))

(tu/deftest-kb ^:red two-names-of-one-monad-see-each-others-facts
  ;; The monad-dimension twin of two-spellings-of-one-month-see-each-others-facts: two
  ;; monads each genlMonad-below the other are one monad by two names, as two spellings
  ;; each a subinterval of the other are one month.  The second arrival order uses a
  ;; fresh year, so both slices are new, where the original uses a fresh monad.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxA CxB]
    (monads! kb CxA CxB)
    (v/assert kb (list 'genlMonad CxA CxB) U)
    (v/assert kb (list 'genlMonad CxB CxA) U)
    (testing "CxA written first: each name's slice sees the other's fact"
      (is (= {:first-sees-second? true :second-sees-first? true}
             (dissoc (two-spellings kb (slice CxA '(YearFn 2000)) (slice CxB '(YearFn 2000)))
                     :distinct?))))
    (testing "CxB written first, at a fresh year: the same"
      (is (= {:first-sees-second? true :second-sees-first? true}
             (dissoc (two-spellings kb (slice CxB '(YearFn 2001)) (slice CxA '(YearFn 2001)))
                     :distinct?))))))

(tu/deftest-kb ^:red a-slice-sees-its-monad-and-the-monad-does-not-see-the-slice
  ;; `CxStory` in `(CxTimeFn CxStory T)` is the dimension: "the year 2000, along the
  ;; CxStory dimension" (docs/context-nat.md).  A monad context's own time is unbounded
  ;; (issue #181), so it contains every slice's time, and a slice ought to sit under its
  ;; monad.  Today the producer orders slices by the time argument alone and the monad is
  ;; a key and nothing more.  The reverse stays closed: what holds in 2000 need not hold
  ;; in the story at large.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (let [y2000 (slice CxStory '(DatetimeFn "2000"))]
      (v/assert kb (list 'genlCx CxStory 'CxWell) U)
      (v/assert kb (list p) CxStory)
      (v/assert kb (list q) y2000)
      (testing "a fact stated in the monad is visible from the monad's 2000 slice"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "and a slice's fact is not in the monad"
        (is (not (v/ask? kb (list q) CxStory)))))))

(tu/deftest-kb slices-along-two-monads-do-not-see-each-other
  ;; Two slices that differ in the monad argument are not siblings (they differ at a
  ;; position no declaration orders), so the same year along two monads are two unrelated
  ;; contexts, and a month along one does not see the year along the other.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxNorth CxSouth]
    (v/assert kb (list p) (slice CxNorth '(DatetimeFn "2000")))
    (tu/with-terms [q r]
      (v/assert kb (list q) (slice CxSouth '(DatetimeFn "2000")))
      (v/assert kb (list r) (slice CxSouth '(DatetimeFn "2000-01")))
      (testing "the same year along another monad does not see p"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000"))))))
      (testing "nor does a month along another monad"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000-01")))))))))

(tu/deftest-kb slices-along-two-monads-keyed-by-named-times-do-not-see-each-other
  ;; The reified twin of slices-along-two-monads-do-not-see-each-other: the year and the
  ;; month are named intervals with a stated subintervalOf, which orders slices along one
  ;; monad and not across two.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxNorth CxSouth Y2000 Jan2000]
    (times! kb [Y2000 Jan2000] [] ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000])
    (v/assert kb (list p) (slice CxNorth Y2000))
    (tu/with-terms [q r]
      (v/assert kb (list q) (slice CxSouth Y2000))
      (v/assert kb (list r) (slice CxSouth Jan2000))
      (testing "the same named year along another monad does not see p"
        (is (not (v/ask? kb (list p) (slice CxSouth Y2000)))))
      (testing "nor does the named month along another monad"
        (is (not (v/ask? kb (list p) (slice CxSouth Jan2000))))))))

(tu/deftest-kb ^:red slices-along-two-monads-under-one-super-monad-see-its-slices-and-not-each-other
  ;; The twin of slices-along-two-monads-do-not-see-each-other in which the two monads
  ;; share a super-monad.  Sharing one relates neither to the other, so the original's
  ;; isolation still holds, and each monad's slices now also see the super-monad's slices
  ;; at the same or a wider time.  sibling-sub-monads-each-see-their-super-monad-and-not-each-other
  ;; asks the same at one time; this one keeps the original's month as well.
  (declare-cxtimefn! kb)
  (tu/with-terms [p s m CxSuper CxNorth CxSouth]
    (doseq [c [CxSuper CxNorth CxSouth]] (v/assert kb (list 'genlCx c 'CxWell) U))
    (v/assert kb (list 'genlMonad CxNorth CxSuper) U)
    (v/assert kb (list 'genlMonad CxSouth CxSuper) U)
    (v/assert kb (list p) (slice CxNorth '(DatetimeFn "2000")))
    (v/assert kb (list s) (slice CxSuper '(DatetimeFn "2000")))
    (v/assert kb (list m) (slice CxSuper '(DatetimeFn "2000-01")))
    (tu/with-terms [q r]
      (v/assert kb (list q) (slice CxSouth '(DatetimeFn "2000")))
      (v/assert kb (list r) (slice CxSouth '(DatetimeFn "2000-01")))
      (testing "the same year along the other sub-monad does not see p"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000"))))))
      (testing "nor does a month along the other sub-monad"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000-01"))))))
      (testing "the year along each sub-monad sees the super-monad's year"
        (is (true? (v/ask? kb (list s) (slice CxNorth '(DatetimeFn "2000")))))
        (is (true? (v/ask? kb (list s) (slice CxSouth '(DatetimeFn "2000"))))))
      (testing "the month along a sub-monad sees the super-monad's year and month"
        (is (true? (v/ask? kb (list s) (slice CxSouth '(DatetimeFn "2000-01")))))
        (is (true? (v/ask? kb (list m) (slice CxSouth '(DatetimeFn "2000-01"))))))
      (testing "and the super-monad's slices see neither sub-monad's facts"
        (is (not (v/ask? kb (list p) (slice CxSuper '(DatetimeFn "2000")))))
        (is (not (v/ask? kb (list r) (slice CxSuper '(DatetimeFn "2000-01")))))))))

(tu/deftest-kb instant-slices-along-two-monads-do-not-see-each-other
  ;; The point twin of slices-along-two-monads-do-not-see-each-other: a moment of 2000 in
  ;; place of its January.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxNorth CxSouth]
    (v/assert kb (list p) (slice CxNorth '(DatetimeFn "2000")))
    (tu/with-terms [q r]
      (v/assert kb (list q) (slice CxSouth '(DatetimeFn "2000")))
      (v/assert kb (list r) (slice CxSouth '(InstantFn 2000 6 1 12 0 0)))
      (testing "the same year along another monad does not see p"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000"))))))
      (testing "nor does a moment of that year along another monad"
        (is (not (v/ask? kb (list p) (slice CxSouth '(InstantFn 2000 6 1 12 0 0)))))))))

(tu/deftest-kb slices-keyed-by-two-unrelated-named-times-do-not-see-each-other
  ;; The time-dimension twin of slices-along-two-monads-do-not-see-each-other: two named
  ;; intervals with nothing stated between them are as unrelated as two monads with
  ;; nothing stated between them, so the same monad at the two times is two unrelated
  ;; contexts, and a named subinterval of one does not see the other.
  (declare-cxtimefn! kb)
  (tu/with-terms [p North South SouthPart]
    (times! kb [North South SouthPart] [] ['subintervalOf SouthPart South])
    (v/assert kb (list p) (slice North))
    (tu/with-terms [q r]
      (v/assert kb (list q) (slice South))
      (v/assert kb (list r) (slice SouthPart))
      (testing "control: the subinterval's slice sees its own interval's"
        (is (true? (v/ask? kb (list q) (slice SouthPart)))))
      (testing "the other named time does not see p"
        (is (not (v/ask? kb (list p) (slice South)))))
      (testing "nor does a named subinterval of it"
        (is (not (v/ask? kb (list p) (slice SouthPart))))))))

(tu/deftest-kb ^:red partially-overlapping-slices-and-their-intersection
  ;; Iris's third example, with the overlap and the intersection given as Allen relations
  ;; between named intervals.  The Allen network entails (subintervalOf AprJun JanJun)
  ;; and (subintervalOf AprJun AprSep) from the two facts below, and the intersection
  ;; slice ought to sit under both on that entailment.  Today the stored-fact oracle the
  ;; producer reads takes only stated subintervalOf facts, never a prover answer.  The
  ;; same question with each interval given by its bounds, and no Allen relation stated,
  ;; is two-partially-overlapping-ranges-and-their-intersection.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :allen)
  (tu/with-terms [p q r JanJun AprSep AprJun]
    (let [h1   (slice JanJun)
          h2   (slice AprSep)
          both (slice AprJun)]
      (v/assert kb (list p) h1)
      (v/assert kb (list q) h2)
      (v/assert kb (list r) both)
      (v/assert kb (list 'overlaps JanJun AprSep) U)
      (v/assert kb (list 'finishes AprJun JanJun) U)
      (v/assert kb (list 'starts AprJun AprSep) U)
      (testing "control: the Allen prover entails that the intersection is inside both"
        (is (true? (v/ask? kb (list 'subintervalOf AprJun JanJun) U)))
        (is (true? (v/ask? kb (list 'subintervalOf AprJun AprSep) U))))
      (testing "neither overlapping slice sees the other's facts"
        (is (not (v/ask? kb (list q) h1)))
        (is (not (v/ask? kb (list p) h2))))
      (testing "the intersection slice sees both, on the entailed subintervalOf alone"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "and neither overlapping slice sees the intersection's own fact"
        (is (not (v/ask? kb (list r) h1)))
        (is (not (v/ask? kb (list r) h2)))))))

(tu/deftest-kb ^:red a-narrative-in-a-time-slice-gets-the-event-calculus
  ;; CxChange is wired under CxUniverse and above CxWell, and CxMonad sits under CxWell,
  ;; so a slice along CxMonad ought to read CxChange's inertia rules through its monad.
  ;; Today a slice sees neither, and the rules do not run over a narrative written into
  ;; one.
  (declare-cxtimefn! kb)
  (tu/with-terms [StateFn Thing Start T1 T2]
    (let [ctx (slice '(DatetimeFn "2000"))
          f   (list StateFn Thing)]
      (v/assert kb (list 'result StateFn 'fluent) U)
      (doseq [s [(list 'time_point T1) (list 'time_point T2) (list 'instantBefore T1 T2)
                 (list 'causal_event Start) (list 'happens Start T1)
                 (list 'initiates Start f T1)]]
        (v/assert kb s ctx))
      (testing "CxChange inertia runs over the narrative: the started state holds at T2"
        (is (true? (v/query? kb (list 'holdsAt f T2) ctx {:max-depth 3})))))))

(tu/deftest-kb ^:red a-narrative-dated-by-calendar-moments-in-a-time-slice-gets-the-event-calculus
  ;; The calendar twin of a-narrative-in-a-time-slice-gets-the-event-calculus: the two
  ;; named moments become InstantFn moments inside 2000, and what the original states of
  ;; them (each a time_point, the first before the second) is stated of these.
  (declare-cxtimefn! kb)
  (tu/with-terms [StateFn Thing Start]
    (let [ctx (slice '(DatetimeFn "2000"))
          f   (list StateFn Thing)
          t1  '(InstantFn 2000 3 1 12 0 0)
          t2  '(InstantFn 2000 9 1 12 0 0)]
      (v/assert kb (list 'result StateFn 'fluent) U)
      (doseq [s [(list 'time_point t1) (list 'time_point t2) (list 'instantBefore t1 t2)
                 (list 'causal_event Start) (list 'happens Start t1)
                 (list 'initiates Start f t1)]]
        (v/assert kb s ctx))
      (testing "CxChange inertia runs over the dated narrative: the started state holds at the later moment"
        (is (true? (v/query? kb (list 'holdsAt f t2) ctx {:max-depth 3})))))))

(tu/deftest-kb ^:red a-narrative-in-a-slice-along-a-monad-placed-by-genlmonad-gets-the-event-calculus
  ;; The genlMonad twin of a-narrative-in-a-time-slice-gets-the-event-calculus: the
  ;; slice's monad reaches CxWell, and through it CxChange, by a stated genlMonad.
  (declare-cxtimefn! kb)
  (tu/with-terms [StateFn Thing Start T1 T2 CxStory]
    (v/assert kb (list 'genlMonad CxStory 'CxWell) U)
    (let [ctx (slice CxStory '(DatetimeFn "2000"))
          f   (list StateFn Thing)]
      (v/assert kb (list 'result StateFn 'fluent) U)
      (doseq [s [(list 'time_point T1) (list 'time_point T2) (list 'instantBefore T1 T2)
                 (list 'causal_event Start) (list 'happens Start T1)
                 (list 'initiates Start f T1)]]
        (v/assert kb s ctx))
      (testing "CxChange inertia runs over the narrative: the started state holds at T2"
        (is (true? (v/query? kb (list 'holdsAt f T2) ctx {:max-depth 3})))))))

(tu/deftest-kb a-rule-stated-in-a-year-slice-runs-in-its-month-slice
  ;; The time-dimension twin of a-narrative-in-a-time-slice-gets-the-event-calculus.  The
  ;; original reads rules stated above the slice's monad; this reads a rule stated at a
  ;; wider time along the same monad, which the month slice sees through the computed
  ;; edge, and it passes today.
  (declare-cxtimefn! kb)
  (tu/with-terms [blooms springHasCome Crocus]
    (let [year  (slice '(DatetimeFn "2000"))
          month (slice '(DatetimeFn "2000-03"))]
      (tu/with-terms [p] (v/assert kb (list p) year))
      (v/assert-rule kb [(list blooms '?x)] (list springHasCome '?x) year {:direction :backward})
      (v/assert kb (list blooms Crocus) month)
      (testing "the year's rule answers over the month's fact, from the month"
        (is (true? (v/query? kb (list springHasCome Crocus) month {:max-depth 3}))))
      (testing "and not from the year, which does not see the month's fact"
        (is (not (v/query? kb (list springHasCome Crocus) year {:max-depth 3})))))))

;; =========================================================================
;; The monad dimension — issue #181, and the isomorphism with time
;; =========================================================================
;; A context has two parts: its monad (which world, story or theory) and its time.
;; `genlMonad` orders monads alone, the way `subintervalOf` orders times alone, and
;; `genlCx` between two contexts is the product: one sees another exactly when its monad
;; is genlMonad-below the other's and its time is inside the other's.  `CxMonadOfFn` and
;; `CxTimeOfFn` take a context apart, and `monad_context` is a context with no temporal
;; part, the type of CxTimeFn's first argument.  Each test below is the monad-side twin
;; of a time-side test above, named in its comment.  A monad-dimension twin of any other
;; time-side test sits beside that test, and a time-dimension twin of a test here sits
;; beside it.

(tu/deftest-kb ^:red the-monad-vocabulary-is-declared-in-the-shipped-kb
  ;; Twin of cxtimefn-is-declared-in-the-shipped-kb.  Issue #181 asks for each of these.
  (testing "genlMonad, a binary relation ordering monads alone"
    (is (true? (v/query? kb '(arity genlMonad 2) U {:max-depth 3}))))
  (testing "monad_context, a context with no temporal part, types CxTimeFn's first argument"
    (is (true? (v/ask? kb '(genl monad_context context) U)))
    (is (true? (v/ask? kb '(arg CxTimeFn 1 monad_context) U))))
  (testing "CxTimeOfFn and cxTimeOf, a context's temporal part, which is a time"
    (is (true? (v/ask? kb '(functionCorrespondingPredicate CxTimeOfFn cxTimeOf) U)))
    (is (true? (v/ask? kb '(result CxTimeOfFn time) U))))
  (testing "CxMonadOfFn and cxMonadOf, a context's monadic part, which is a monad_context"
    (is (true? (v/ask? kb '(functionCorrespondingPredicate CxMonadOfFn cxMonadOf) U)))
    (is (true? (v/ask? kb '(result CxMonadOfFn monad_context) U)))))

(tu/deftest-kb ^:red a-slice-along-a-sub-monad-sees-the-same-time-along-its-super-monad
  ;; Twin of a-fact-in-a-year-slice-is-visible-from-its-month: the same time, with the
  ;; monad narrowing instead of the time.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [sup (slice CxSuper '(YearFn 2000))
          sub (slice CxSub '(YearFn 2000))]
      (v/assert kb (list p) sup)
      (v/assert kb (list q) sub)
      (testing "2000 along the sub-monad sees 2000 along the super-monad"
        (is (true? (v/ask? kb (list p) sub))))
      (testing "and not the reverse"
        (is (not (v/ask? kb (list q) sup)))))))

(tu/deftest-kb ^:red a-slice-along-a-sub-monad-placed-by-genlcx-sees-the-same-time-along-its-super-monad
  ;; The genlCx twin of a-slice-along-a-sub-monad-sees-the-same-time-along-its-super-monad:
  ;; the two monads are ordered by a stated genlCx, which between two monad contexts is a
  ;; genlMonad (genlmonad-between-two-monad-contexts-is-their-genlcx).
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlCx CxSub CxSuper) U)
    (let [sup (slice CxSuper '(YearFn 2000))
          sub (slice CxSub '(YearFn 2000))]
      (v/assert kb (list p) sup)
      (v/assert kb (list q) sub)
      (testing "2000 along the sub-monad sees 2000 along the super-monad"
        (is (true? (v/ask? kb (list p) sub))))
      (testing "and not the reverse"
        (is (not (v/ask? kb (list q) sup)))))))

(tu/deftest-kb ^:red a-slice-sees-a-monad-two-genlmonad-steps-up
  ;; Twin of the entailed-containment half of
  ;; partially-overlapping-slices-and-their-intersection: the ordering is entailed
  ;; (genlMonad is transitive), not stated between the two monads the slices name.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxTop CxMid CxLow]
    (monads! kb CxTop CxMid CxLow)
    (v/assert kb (list 'genlMonad CxLow CxMid) U)
    (v/assert kb (list 'genlMonad CxMid CxTop) U)
    (tu/with-terms [q]
      (v/assert kb (list p) (slice CxTop '(YearFn 2000)))
      (v/assert kb (list q) (slice CxLow '(YearFn 2000)))
      (testing "2000 along CxLow sees 2000 along CxTop through CxMid"
        (is (true? (v/ask? kb (list 'genlMonad CxLow CxTop) U)))
        (is (true? (v/ask? kb (list p) (slice CxLow '(YearFn 2000)))))))))

(tu/deftest-kb ^:red a-slice-sees-a-monad-two-genlcx-steps-up
  ;; The genlCx twin of a-slice-sees-a-monad-two-genlmonad-steps-up.  genlCx is
  ;; transitive today, so the control is that the low monad sees the top one.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxTop CxMid CxLow]
    (monads! kb CxTop CxMid CxLow)
    (v/assert kb (list 'genlCx CxLow CxMid) U)
    (v/assert kb (list 'genlCx CxMid CxTop) U)
    (tu/with-terms [q]
      (v/assert kb (list p) (slice CxTop '(YearFn 2000)))
      (v/assert kb (list q) (slice CxLow '(YearFn 2000)))
      (testing "control: CxLow sees CxTop through CxMid"
        (is (true? (v/sees? kb CxLow CxTop))))
      (testing "2000 along CxLow sees 2000 along CxTop through CxMid"
        (is (true? (v/ask? kb (list p) (slice CxLow '(YearFn 2000)))))))))

(defn- product-pairs
  "For two monads, CxSub genlMonad-below CxSuper, and two times, `narrow` inside `wide`,
  write a fact into each of the four slices and return, for each ordered pair of distinct
  slices `[x y]`, whether x is below y in both dimensions and whether x sees y's fact."
  [kb sub super narrow wide]
  (let [slices {[:sub :narrow]   (slice sub narrow)
                [:sub :wide]     (slice sub wide)
                [:super :narrow] (slice super narrow)
                [:super :wide]   (slice super wide)}
        fact   (into {} (for [k (keys slices)]
                          [k (list (tu/tmp-pred (str "fact" (name (first k)) (name (second k)))))]))
        below? (fn [[m t] [m2 t2]] (and (or (= m m2) (= [m m2] [:sub :super]))
                                        (or (= t t2) (= [t t2] [:narrow :wide]))))]
    (doseq [[k ctx] slices] (v/assert kb (fact k) ctx))
    (for [x (keys slices) y (keys slices) :when (not= x y)]
      [x y (below? x y) (boolean (v/ask? kb (fact y) (slices x)))])))

(tu/deftest-kb ^:red genlcx-between-slices-is-genlmonad-times-time-containment
  ;; The product rule, over the four slices two monads and two times make.  A slice sees
  ;; another exactly when both its monad and its time are at or below the other's, so of
  ;; the twelve ordered pairs of distinct slices three see and nine do not.  The two
  ;; diagonal pairs are the ones a one-dimensional ordering gets wrong: (sub, 2000) and
  ;; (super, January) each narrow one dimension and widen the other.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [slices {[:sub :jan]    (slice CxSub '(MonthFn 2000 1))
                  [:sub :year]   (slice CxSub '(YearFn 2000))
                  [:super :jan]  (slice CxSuper '(MonthFn 2000 1))
                  [:super :year] (slice CxSuper '(YearFn 2000))}
          fact   (into {} (for [k (keys slices)]
                            [k (list (tu/tmp-pred (str "fact" (name (first k)) (name (second k)))))]))
          below? (fn [[m t] [m2 t2]] (and (or (= m m2) (= [m m2] [:sub :super]))
                                          (or (= t t2) (= [t t2] [:jan :year]))))]
      (doseq [[k ctx] slices] (v/assert kb (fact k) ctx))
      (doseq [x (keys slices) y (keys slices) :when (not= x y)]
        (testing (str x " sees " y "'s fact exactly when it is below it in both dimensions")
          (is (= (below? x y) (boolean (v/ask? kb (fact y) (slices x))))))))))

(tu/deftest-kb ^:red genlcx-between-slices-over-named-times-is-genlmonad-times-time-containment
  ;; The reified twin of genlcx-between-slices-is-genlmonad-times-time-containment: the
  ;; month and the year are named intervals with a stated subintervalOf.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxSuper CxSub Y2000 Jan2000]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (times! kb [Y2000 Jan2000] [] ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000])
    (doseq [[x y below? sees?] (product-pairs kb CxSub CxSuper Jan2000 Y2000)]
      (testing (str x " sees " y "'s fact exactly when it is below it in both dimensions")
        (is (= below? sees?))))))

(tu/deftest-kb ^:red genlcx-between-slices-over-a-year-and-an-instant-in-it-is-genlmonad-times-time-containment
  ;; The point twin of genlcx-between-slices-is-genlmonad-times-time-containment: a moment
  ;; of 2000 in place of January, so the time half of the product is includesInstant
  ;; rather than subintervalOf.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (doseq [[x y below? sees?] (product-pairs kb CxSub CxSuper '(InstantFn 2000 1 15 12 0 0) '(YearFn 2000))]
      (testing (str x " sees " y "'s fact exactly when it is below it in both dimensions")
        (is (= below? sees?))))))

(tu/deftest-kb ^:red genlcx-between-slices-is-the-monads-genlcx-times-time-containment
  ;; The genlCx twin of genlcx-between-slices-is-genlmonad-times-time-containment: the two
  ;; monads are ordered by a stated genlCx.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlCx CxSub CxSuper) U)
    (doseq [[x y below? sees?] (product-pairs kb CxSub CxSuper '(MonthFn 2000 1) '(YearFn 2000))]
      (testing (str x " sees " y "'s fact exactly when it is below it in both dimensions")
        (is (= below? sees?))))))

(tu/deftest-kb ^:red sibling-sub-monads-each-see-their-super-monad-and-not-each-other
  ;; Twin of sibling-month-slices-do-not-see-each-other.
  ;; slices-along-two-monads-do-not-see-each-other has no common super-monad.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxSuper CxNorth CxSouth]
    (monads! kb CxSuper CxNorth CxSouth)
    (v/assert kb (list 'genlMonad CxNorth CxSuper) U)
    (v/assert kb (list 'genlMonad CxSouth CxSuper) U)
    (let [sup   (slice CxSuper '(YearFn 2000))
          north (slice CxNorth '(YearFn 2000))
          south (slice CxSouth '(YearFn 2000))]
      (v/assert kb (list r) sup)
      (v/assert kb (list p) north)
      (v/assert kb (list q) south)
      (testing "each sub-monad's slice sees the super-monad's"
        (is (true? (v/ask? kb (list r) north)))
        (is (true? (v/ask? kb (list r) south))))
      (testing "and neither sees the other's facts"
        (is (not (v/ask? kb (list p) south)))
        (is (not (v/ask? kb (list q) north)))))))

(tu/deftest-kb ^:red sibling-monads-placed-by-genlcx-each-see-their-super-monad-and-not-each-other
  ;; The genlCx twin of sibling-sub-monads-each-see-their-super-monad-and-not-each-other.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxSuper CxNorth CxSouth]
    (monads! kb CxSuper CxNorth CxSouth)
    (v/assert kb (list 'genlCx CxNorth CxSuper) U)
    (v/assert kb (list 'genlCx CxSouth CxSuper) U)
    (let [sup   (slice CxSuper '(YearFn 2000))
          north (slice CxNorth '(YearFn 2000))
          south (slice CxSouth '(YearFn 2000))]
      (v/assert kb (list r) sup)
      (v/assert kb (list p) north)
      (v/assert kb (list q) south)
      (testing "each sub-monad's slice sees the super-monad's"
        (is (true? (v/ask? kb (list r) north)))
        (is (true? (v/ask? kb (list r) south))))
      (testing "and neither sees the other's facts"
        (is (not (v/ask? kb (list p) south)))
        (is (not (v/ask? kb (list q) north)))))))

(tu/deftest-kb ^:red a-monad-below-two-monads-sees-both-at-the-same-time
  ;; Twin of partially-overlapping-slices-and-their-intersection: the intersection
  ;; of two monads is a monad genlMonad-below both.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxLeft CxRight CxBoth]
    (monads! kb CxLeft CxRight CxBoth)
    (v/assert kb (list 'genlMonad CxBoth CxLeft) U)
    (v/assert kb (list 'genlMonad CxBoth CxRight) U)
    (let [left  (slice CxLeft '(YearFn 2000))
          right (slice CxRight '(YearFn 2000))
          both  (slice CxBoth '(YearFn 2000))]
      (v/assert kb (list p) left)
      (v/assert kb (list q) right)
      (v/assert kb (list r) both)
      (testing "the slice along the monad below both sees both"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "neither of the other two sees the other's fact or the intersection's"
        (is (not (v/ask? kb (list q) left)))
        (is (not (v/ask? kb (list p) right)))
        (is (not (v/ask? kb (list r) left)))
        (is (not (v/ask? kb (list r) right)))))))

(tu/deftest-kb ^:red a-monad-genlcx-below-two-monads-sees-both-at-the-same-time
  ;; The genlCx twin of a-monad-below-two-monads-sees-both-at-the-same-time.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxLeft CxRight CxBoth]
    (monads! kb CxLeft CxRight CxBoth)
    (v/assert kb (list 'genlCx CxBoth CxLeft) U)
    (v/assert kb (list 'genlCx CxBoth CxRight) U)
    (let [left  (slice CxLeft '(YearFn 2000))
          right (slice CxRight '(YearFn 2000))
          both  (slice CxBoth '(YearFn 2000))]
      (v/assert kb (list p) left)
      (v/assert kb (list q) right)
      (v/assert kb (list r) both)
      (testing "the slice along the monad below both sees both"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "neither of the other two sees the other's fact or the intersection's"
        (is (not (v/ask? kb (list q) left)))
        (is (not (v/ask? kb (list p) right)))
        (is (not (v/ask? kb (list r) left)))
        (is (not (v/ask? kb (list r) right)))))))

(tu/deftest-kb ^:red genlmonad-between-two-monad-contexts-is-their-genlcx
  ;; A monad context's time is unbounded, so between two of them the time half of the
  ;; product always holds and genlCx and genlMonad coincide, each way.
  (tu/with-terms [p CxSuper CxSub CxA CxB]
    (monads! kb CxSuper CxSub CxA CxB)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (v/assert kb (list p) CxSuper)
    (testing "a stated genlMonad makes the sub-monad see the super-monad"
      (is (true? (v/sees? kb CxSub CxSuper)))
      (is (true? (v/ask? kb (list p) CxSub))))
    (v/assert kb (list 'genlCx CxA CxB) U)
    (testing "a stated genlCx between two monad contexts is a genlMonad"
      (is (true? (v/ask? kb (list 'genlMonad CxA CxB) U))))))

(tu/deftest-kb ^:red subintervalof-between-the-times-of-two-slices-along-one-monad-is-their-genlcx
  ;; The time-dimension twin of genlmonad-between-two-monad-contexts-is-their-genlcx.  Along
  ;; one monad the monad half of the product always holds, so genlCx between two slices
  ;; and subintervalOf between their times coincide, each way.  The first way is the
  ;; computed edge and holds today; the second is a stated genlCx between two slices,
  ;; which ought to be read back as a subintervalOf between the times.
  (declare-cxtimefn! kb)
  (tu/with-terms [p Wide Narrow A B]
    (times! kb [Wide Narrow A B] [] ['subintervalOf Narrow Wide])
    (let [kw (cx-of kb (v/assert kb (list p) (slice Wide)))]
      (tu/with-terms [q]
        (let [kn (cx-of kb (v/assert kb (list q) (slice Narrow)))]
          (testing "control: a stated subintervalOf makes the narrower slice see the wider"
            (is (true? (v/sees? kb kn kw)))
            (is (true? (v/ask? kb (list p) (slice Narrow))))))))
    (tu/with-terms [r s]
      (let [ka (cx-of kb (v/assert kb (list r) (slice A)))
            kb' (cx-of kb (v/assert kb (list s) (slice B)))]
        (v/assert kb (list 'genlCx ka kb') U)
        (testing "a stated genlCx between two slices along one monad is a subintervalOf between their times"
          (is (true? (v/ask? kb (list 'subintervalOf A B) U))))))))

(tu/deftest-kb ^:red cxtimeof-and-cxmonadof-take-a-slice-apart-and-cxtimefn-puts-it-back
  ;; The round trip: (CxTimeFn (CxMonadOfFn S) (CxTimeOfFn S)) names S itself.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxStory]
    (monads! kb CxStory)
    (let [k (cx-of kb (v/assert kb (list p) (slice CxStory '(YearFn 2000))))]
      (testing "cxTimeOf answers the slice's time and cxMonadOf its monad"
        (is (= [{'?t '(YearFn 2000)}] (v/ask kb (list 'cxTimeOf k '?t) U)))
        (is (= [{'?m CxStory}] (v/ask kb (list 'cxMonadOf k '?m) U))))
      (testing "and the slice rebuilt from its two parts is the same context"
        (is (true? (v/ask? kb (list p) (list 'CxTimeFn (list 'CxMonadOfFn k) (list 'CxTimeOfFn k)))))))))

(tu/deftest-kb ^:red a-monad-context-is-its-own-monad-and-its-time-is-unbounded
  ;; Issue #181: a monadic context's temporal part is unbounded, so every time is inside
  ;; it, and its monadic part is itself.
  (tu/with-terms [CxStory]
    (monads! kb CxStory)
    (testing "a context under CxWell with no temporal part is a monad_context"
      (is (true? (v/ask? kb (list 'monad_context CxStory) U))))
    (testing "its monad is itself"
      (is (= [{'?m CxStory}] (v/ask kb (list 'cxMonadOf CxStory '?m) U))))
    (testing "and the year 1 and the year 9000 are both inside its time"
      (is (true? (v/ask? kb (list 'subintervalOf '(YearFn 1) (list 'CxTimeOfFn CxStory)) U)))
      (is (true? (v/ask? kb (list 'subintervalOf '(YearFn 9000) (list 'CxTimeOfFn CxStory)) U))))))

(tu/deftest-kb ^:red a-monad-context-is-its-own-monad-and-its-time-contains-named-intervals
  ;; The reified twin of a-monad-context-is-its-own-monad-and-its-time-is-unbounded: the
  ;; years 1 and 9000 become two named intervals, the first stated before the second.
  (tu/with-terms [CxStory Early Late]
    (monads! kb CxStory)
    (times! kb [Early Late] [] ['before Early Late])
    (testing "a context under CxWell with no temporal part is a monad_context"
      (is (true? (v/ask? kb (list 'monad_context CxStory) U))))
    (testing "its monad is itself"
      (is (= [{'?m CxStory}] (v/ask kb (list 'cxMonadOf CxStory '?m) U))))
    (testing "and both named intervals are inside its time"
      (is (true? (v/ask? kb (list 'subintervalOf Early (list 'CxTimeOfFn CxStory)) U)))
      (is (true? (v/ask? kb (list 'subintervalOf Late (list 'CxTimeOfFn CxStory)) U))))))

(tu/deftest-kb ^:red a-monad-context-is-its-own-monad-and-its-time-includes-every-instant
  ;; The point twin of a-monad-context-is-its-own-monad-and-its-time-is-unbounded: the
  ;; first moment of the year 1 and a moment of the year 9000 in place of the two years.
  (tu/with-terms [CxStory]
    (monads! kb CxStory)
    (testing "a context under CxWell with no temporal part is a monad_context"
      (is (true? (v/ask? kb (list 'monad_context CxStory) U))))
    (testing "its monad is itself"
      (is (= [{'?m CxStory}] (v/ask kb (list 'cxMonadOf CxStory '?m) U))))
    (testing "and a moment of the year 1 and one of the year 9000 are both inside its time"
      (is (true? (v/ask? kb (list 'includesInstant (list 'CxTimeOfFn CxStory) '(InstantFn 1 1 1 0 0 0)) U)))
      (is (true? (v/ask? kb (list 'includesInstant (list 'CxTimeOfFn CxStory) '(InstantFn 9000 6 1 12 0 0)) U))))))

(tu/deftest-kb ^:red monad-context-types-cxtimefns-first-argument
  ;; Issue #181: CxTimeFn's first argument is untyped today, so a write into a slice of
  ;; CxNow, or of another slice, is stored like any other.  CxNow has a temporal part
  ;; (it moves), and so does a slice, so neither is a monad_context.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxStory]
    (monads! kb CxStory)
    (testing "control: a write into a slice along a monad context is stored"
      (is (= :answered (refusal-type #(v/assert kb (list p) (slice CxStory '(YearFn 2000)))))))
    (testing "CxNow and a slice are not monad contexts"
      (is (not (v/ask? kb '(monad_context CxNow) U)))
      (is (not (v/ask? kb (list 'monad_context (cx-of kb (v/assert kb (list r) (slice CxStory '(YearFn 2001))))) U))))
    (testing "a write into (CxTimeFn CxNow …) is refused for its argument type"
      (is (= :arg-type (refusal-type #(v/assert kb (list q) (slice 'CxNow '(YearFn 2000)))))))
    (testing "and so is a write into a slice of a slice spelled with CxTimeFn twice"
      (is (= :arg-type (refusal-type #(v/assert kb (list q)
                                                (slice (slice CxStory '(YearFn 2000))
                                                       '(MonthFn 2000 1)))))))))

(tu/deftest-kb ^:red cxtimefns-second-argument-is-typed-a-time
  ;; The time-dimension twin of monad-context-types-cxtimefns-first-argument: CxTimeFn's
  ;; second argument is untyped today, so a write into a slice keyed by a context or by a
  ;; number is stored like any other.  A slice is keyed by a time.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (monads! kb CxStory)
    (testing "control: a write into a slice keyed by a time is stored"
      (is (= :answered (refusal-type #(v/assert kb (list p) (slice CxStory '(YearFn 2000)))))))
    (testing "a write into a slice keyed by a context is refused for its argument type"
      (is (= :arg-type (refusal-type #(v/assert kb (list q) (slice CxStory CxStory))))))
    (testing "and so is a write into a slice keyed by a number"
      (is (= :arg-type (refusal-type #(v/assert kb (list q) (slice CxStory 2000))))))))

(tu/deftest-kb ^:red a-slice-of-a-slice-is-the-slice-of-its-monad-at-the-narrower-time
  ;; Issue #181 defines a slice of a slice through the two parts: January of the slice
  ;; (CxStory, 2000) is (CxTimeFn (CxMonadOfFn S) (MonthFn 2000 1)), which is the slice
  ;; (CxStory, January 2000), and it sees what S holds.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (monads! kb CxStory)
    (let [s  (cx-of kb (v/assert kb (list p) (slice CxStory '(YearFn 2000))))
          ss (list 'CxTimeFn (list 'CxMonadOfFn s) '(MonthFn 2000 1))]
      (testing "a write into the slice of S at January lands in (CxStory, January 2000)"
        (is (= (cx-of kb (v/assert kb (list q) ss))
               (cx-of kb (v/assert kb (list q) (slice CxStory '(MonthFn 2000 1)))))))
      (testing "and that slice sees S's fact"
        (is (true? (v/ask? kb (list p) ss)))))))

(tu/deftest-kb ^:red a-slice-of-a-slice-at-a-named-narrower-time-is-the-slice-of-its-monad-there
  ;; The reified twin of a-slice-of-a-slice-is-the-slice-of-its-monad-at-the-narrower-time:
  ;; the year and the month are named intervals with a stated subintervalOf.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory Y2000 Jan2000]
    (monads! kb CxStory)
    (times! kb [Y2000 Jan2000] [] ['starts Jan2000 Y2000] ['subintervalOf Jan2000 Y2000])
    (let [s  (cx-of kb (v/assert kb (list p) (slice CxStory Y2000)))
          ss (list 'CxTimeFn (list 'CxMonadOfFn s) Jan2000)]
      (testing "a write into the slice of S at the named January lands in (CxStory, January)"
        (is (= (cx-of kb (v/assert kb (list q) ss))
               (cx-of kb (v/assert kb (list q) (slice CxStory Jan2000))))))
      (testing "and that slice sees S's fact"
        (is (true? (v/ask? kb (list p) ss)))))))

(tu/deftest-kb ^:red a-slice-of-a-slice-at-an-instant-is-the-slice-of-its-monad-at-that-instant
  ;; The point twin of a-slice-of-a-slice-is-the-slice-of-its-monad-at-the-narrower-time:
  ;; the slice of S at a moment of 2000, in place of its January.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (monads! kb CxStory)
    (let [noon '(InstantFn 2000 6 1 12 0 0)
          s    (cx-of kb (v/assert kb (list p) (slice CxStory '(YearFn 2000))))
          ss   (list 'CxTimeFn (list 'CxMonadOfFn s) noon)]
      (testing "a write into the slice of S at the moment lands in (CxStory, that moment)"
        (is (= (cx-of kb (v/assert kb (list q) ss))
               (cx-of kb (v/assert kb (list q) (slice CxStory noon))))))
      (testing "and that slice sees S's fact"
        (is (true? (v/ask? kb (list p) ss)))))))

(tu/deftest-kb ^:red a-slice-of-a-slice-along-the-monad-axis-is-the-slice-of-a-sub-monad-at-its-time
  ;; The monad-dimension twin of a-slice-of-a-slice-is-the-slice-of-its-monad-at-the-narrower-time.
  ;; The original keeps S's monad and narrows its time; this keeps S's time and narrows
  ;; its monad: (CxTimeFn CxSubStory (CxTimeOfFn S)), for S the slice (CxStory, 2000) and
  ;; CxSubStory genlMonad-below CxStory, is the slice (CxSubStory, 2000), and it sees what
  ;; S holds.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory CxSubStory]
    (monads! kb CxStory CxSubStory)
    (v/assert kb (list 'genlMonad CxSubStory CxStory) U)
    (let [s  (cx-of kb (v/assert kb (list p) (slice CxStory '(YearFn 2000))))
          ss (list 'CxTimeFn CxSubStory (list 'CxTimeOfFn s))]
      (testing "a write into the sub-monad's slice at S's time lands in (CxSubStory, 2000)"
        (is (= (cx-of kb (v/assert kb (list q) ss))
               (cx-of kb (v/assert kb (list q) (slice CxSubStory '(YearFn 2000)))))))
      (testing "and that slice sees S's fact"
        (is (true? (v/ask? kb (list p) ss)))))))

;; =========================================================================
;; CxNow, the moving present, and temporal projection
;; =========================================================================
;; CxNow is what is true now: a moving, indexical present of no particular world
;; (resources/kb/middle/CxNow.txt).  CxRealWorldNow is the real world's present and sees
;; CxRealWorld and CxNow.  `(CxTimeOfFn CxNow)` names the present, so a sentence about
;; "now" names the time the KB is asked at.  The present is reached through LOWER
;; BOUNDS: a clock reading states `(instantNotBefore now T)`, which stays true for ever
;; after, and what is derived from readings is derived as a bound.  With no upper bound
;; nothing fixes an exact present, so an exact reading ("it is 3:41") and a dated
;; present-tense fact ("today is Saturday") are not stated in CxNow at all.
;;
;; Projection is CxChange's inertia carried across contexts: a fluent started at a
;; moment in one slice still holds at a later moment, until something ends it.  "Later"
;; than a past moment is reached from a reading.  A plain fact of a past slice is not
;; projected: it was true in 2000 and is unknown in 2001.

(def ^:private now '(CxTimeOfFn CxNow))

(defn- reading!
  "A clock reading: in CxNow, now is no earlier than the InstantFn moment `fields`."
  [kb fields]
  (v/assert kb (list 'instantNotBefore now (cons 'InstantFn fields)) 'CxNow))

(defn- reading-at!
  "A clock reading at a named moment: in CxNow, now is no earlier than `moment`."
  [kb moment]
  (v/assert kb (list 'instantNotBefore now moment) 'CxNow))

(defn- real-slice
  "The slice of the real world at `time`."
  [time]
  (slice 'CxRealWorld time))

(defn- fluent!
  "Declare `state-fn` a fluent constructor and return the fluent `(state-fn thing)`."
  [kb state-fn thing]
  (v/assert kb (list 'result state-fn 'fluent) U)
  (list state-fn thing))

(defn- happened!
  "In `ctx`, state that `event` happened at `instant` and `effect` (initiates or
  terminates) `fluent` there."
  [kb ctx event effect fluent instant]
  (doseq [s [(list 'causal_event event) (list 'happens event instant)
             (list effect event fluent instant)]]
    (v/assert kb s ctx)))

(tu/deftest-kb a-fact-true-now-is-true-in-the-real-worlds-present-and-not-timelessly
  ;; CxNow sees CxUniverse; CxRealWorldNow sees CxRealWorld and CxNow; nothing above
  ;; CxNow sees what it states.
  (tu/with-terms [p q]
    (v/assert kb (list p) 'CxNow)
    (v/assert kb (list q) 'CxRealWorld)
    (testing "the real world's present sees both the present and the real world"
      (is (true? (v/sees? kb 'CxRealWorldNow 'CxNow)))
      (is (true? (v/sees? kb 'CxRealWorldNow 'CxRealWorld)))
      (is (true? (v/ask? kb (list p) 'CxRealWorldNow)))
      (is (true? (v/ask? kb (list q) 'CxRealWorldNow))))
    (testing "the present is of no world: CxNow does not see the real world"
      (is (not (v/ask? kb (list q) 'CxNow))))
    (testing "a fact true now is not true timelessly, in general, or in the real world at large"
      (is (not (v/ask? kb (list p) U)))
      (is (not (v/ask? kb (list p) 'CxWell)))
      (is (not (v/ask? kb (list p) 'CxRealWorld))))))

(tu/deftest-kb ^:red cxrealworldnow-is-the-real-world-at-the-present
  ;; The product read back through #181's two functions: its monad is CxRealWorld and its
  ;; time is CxNow's.
  (testing "CxRealWorldNow's monad is CxRealWorld"
    (is (= [{'?m 'CxRealWorld}] (v/ask kb '(cxMonadOf CxRealWorldNow ?m) U))))
  (testing "and its time is the present"
    (is (true? (v/ask? kb (list 'cxTimeOf 'CxRealWorldNow now) U)))))

(tu/deftest-kb ^:red a-later-clock-reading-supersedes-an-earlier-one
  ;; Iris's acceptance test: a reading on Saturday 17 October 2026, then a later one on
  ;; Sunday the 18th.  Both bounds stay true, and the tightest, the earliest the present
  ;; can be, is Sunday's alone.
  (v/add-reasoner kb :point :calendar)
  (reading! kb [2026 10 17 9 0 0])
  (testing "after Saturday's reading: now is no earlier than Saturday, and Sunday is unknown"
    (is (true? (v/ask? kb (list 'instantNotBefore now '(InstantFn 2026 10 17 0 0 0)) 'CxNow)))
    (is (= :unknown (verdict kb (list 'instantNotBefore now '(InstantFn 2026 10 18 0 0 0)) 'CxNow))))
  (reading! kb [2026 10 18 9 0 0])
  (testing "after Sunday's: now is no earlier than Sunday"
    (is (true? (v/ask? kb (list 'instantNotBefore now '(InstantFn 2026 10 18 0 0 0)) 'CxNow))))
  (testing "and the earliest the present can be is Sunday's reading, not Saturday's"
    (is (= [{'?t '(InstantFn 2026 10 18 9 0 0)}]
           (v/ask kb (list 'earliestStartOf now '?t) 'CxNow)))))

(tu/deftest-kb ^:red a-later-reading-at-a-named-moment-supersedes-an-earlier-one
  ;; The reified twin of a-later-clock-reading-supersedes-an-earlier-one: the two readings
  ;; and the two midnights are named moments, ordered as the calendar orders the
  ;; original's.  The point prover takes the place of the calendar clock.
  (v/add-reasoner kb :point)
  (tu/with-terms [SatMidnight SatReading SunMidnight SunReading]
    (chain! kb SatMidnight SatReading SunMidnight SunReading)
    (reading-at! kb SatReading)
    (testing "after the first reading: now is no earlier than the first midnight, and the second is unknown"
      (is (true? (v/ask? kb (list 'instantNotBefore now SatMidnight) 'CxNow)))
      (is (= :unknown (verdict kb (list 'instantNotBefore now SunMidnight) 'CxNow))))
    (reading-at! kb SunReading)
    (testing "after the second: now is no earlier than the second midnight"
      (is (true? (v/ask? kb (list 'instantNotBefore now SunMidnight) 'CxNow))))
    (testing "and the earliest the present can be is the second reading, not the first"
      (is (= [{'?t SunReading}] (v/ask kb (list 'earliestStartOf now '?t) 'CxNow))))))

(tu/deftest-kb with-no-clock-reading-the-present-is-unknown
  ;; Iris's acceptance test: with no reading nothing places the present, not even after
  ;; the year 1.  Correct by design, and passing today; it stays a test so a change
  ;; that reads the host's clock into the KB breaks it.
  (v/add-reasoner kb :point :calendar)
  (testing "now is neither known to be after nor before the start of the year 1"
    (is (= :unknown (verdict kb (list 'instantNotBefore now '(InstantFn 1 1 1 0 0 0)) 'CxNow))))
  (testing "and no earliest present is answered"
    (is (empty? (v/ask kb (list 'earliestStartOf now '?t) 'CxNow)))))

(tu/deftest-kb with-no-clock-reading-the-present-is-unknown-against-a-named-moment
  ;; The reified twin of with-no-clock-reading-the-present-is-unknown: with no reading,
  ;; nothing places the present against a named moment either.  Correct by design.
  (v/add-reasoner kb :point)
  (tu/with-terms [LongAgo]
    (times! kb [] [LongAgo])
    (testing "now is neither known to be after nor before the named moment"
      (is (= :unknown (verdict kb (list 'instantNotBefore now LongAgo) 'CxNow))))
    (testing "and no earliest present is answered"
      (is (empty? (v/ask kb (list 'earliestStartOf now '?t) 'CxNow))))))

(tu/deftest-kb ^:red an-exact-present-and-a-dated-present-tense-fact-are-refused-in-cxnow
  ;; Iris's ruling: CxNow holds bounds, never an exact present and never a dated
  ;; present-tense fact; the day and an age are derived from readings, as bounds.  The
  ;; control is a reading, which is stored.
  (testing "control: a lower-bound reading is stored"
    (is (= :answered (refusal-type #(reading! kb [2026 10 21 3 41 0])))))
  (testing "\"it is 3:41\" is refused"
    (is (not= :answered
              (refusal-type #(v/assert kb (list 'instantEqual now '(InstantFn 2026 10 21 3 41 0))
                                       'CxNow)))))
  (testing "\"today is Saturday 17 October 2026\" is refused"
    (is (not= :answered
              (refusal-type #(v/assert kb (list 'includesInstant '(DayFn 2026 10 17) now)
                                       'CxNow))))))

(tu/deftest-kb ^:red an-exact-present-and-a-present-tense-fact-at-named-times-are-refused-in-cxnow
  ;; The reified twin of an-exact-present-and-a-dated-present-tense-fact-are-refused-in-cxnow:
  ;; the moment and the day are named, so a refusal that reads only the calendar spelling
  ;; misses them.  The control is a reading at a named moment, which is stored.
  (tu/with-terms [ReadAt TwentyOneFortyOne Saturday]
    (times! kb [Saturday] [ReadAt TwentyOneFortyOne])
    (testing "control: a lower-bound reading at a named moment is stored"
      (is (= :answered (refusal-type #(reading-at! kb ReadAt)))))
    (testing "\"it is the named moment\" is refused"
      (is (not= :answered
                (refusal-type #(v/assert kb (list 'instantEqual now TwentyOneFortyOne) 'CxNow)))))
    (testing "\"today is the named Saturday\" is refused"
      (is (not= :answered
                (refusal-type #(v/assert kb (list 'includesInstant Saturday now) 'CxNow)))))))

(tu/deftest-kb ^:red an-exact-present-and-a-dated-present-tense-fact-are-refused-in-a-spec-of-cxnow
  ;; The twin of an-exact-present-and-a-dated-present-tense-fact-are-refused-in-cxnow in a
  ;; context declared under CxNow.  What the present is does not change below CxNow, so
  ;; the refusals hold there too, and a reading is stored there as it is in CxNow.
  (tu/with-terms [CxNowSpec]
    (v/assert kb (list 'genlCx CxNowSpec 'CxNow) U)
    (testing "control: the spec sees CxNow, and a lower-bound reading is stored in it"
      (is (true? (v/sees? kb CxNowSpec 'CxNow)))
      (is (= :answered
             (refusal-type #(v/assert kb (list 'instantNotBefore now '(InstantFn 2026 10 21 3 41 0))
                                      CxNowSpec)))))
    (testing "\"it is 3:41\" is refused"
      (is (not= :answered
                (refusal-type #(v/assert kb (list 'instantEqual now '(InstantFn 2026 10 21 3 41 0))
                                         CxNowSpec)))))
    (testing "\"today is Saturday 17 October 2026\" is refused"
      (is (not= :answered
                (refusal-type #(v/assert kb (list 'includesInstant '(DayFn 2026 10 17) now)
                                         CxNowSpec)))))))

(tu/deftest-kb ^:red age-is-derived-as-a-lower-bound-and-never-as-an-exact-value
  ;; Iris's acceptance test.  Born in 1977, read at no earlier than 17 October 2026: at
  ;; least 48 (a December 1977 birthday is still to come), and not known to be 49 or any
  ;; exact age, because nothing bounds the present from above.  A later reading on
  ;; 1 January 2027 makes it at least 49.  `ageAtLeast` (an organism, an integer number
  ;; of whole years) is a placeholder name: the KB has no age relation, and birthYearOf
  ;; (life.txt) is the only birth fact it has.
  (v/add-reasoner kb :point :calendar)
  (tu/with-terms [Ann]
    (v/assert kb (list 'person Ann) U)
    (v/assert kb (list 'birthYearOf Ann 1977) 'CxRealWorld)
    (reading! kb [2026 10 17 9 0 0])
    (testing "at least 48, and 49 unknown"
      (is (true? (v/query? kb (list 'ageAtLeast Ann 48) 'CxRealWorldNow {:max-depth 3})))
      (is (= :unknown (verdict kb (list 'ageAtLeast Ann 49) 'CxRealWorldNow))))
    (testing "no exact age is answered"
      (is (empty? (v/query kb (list 'ageOf Ann '?n) 'CxRealWorldNow {:max-depth 3}))))
    (reading! kb [2027 1 1 0 0 0])
    (testing "a later reading raises the bound to 49"
      (is (true? (v/query? kb (list 'ageAtLeast Ann 49) 'CxRealWorldNow {:max-depth 3}))))))

(tu/deftest-kb ^:red a-distance-between-two-minute-starts-is-exact-and-between-two-unknown-instants-inside-them-is-bounded
  ;; Iris's ruling: precision shows up in temporalDistance's answer, in its width, with
  ;; no organism, no reading of a calendar convention and no rounding involved.  The
  ;; two dates are made up.  A minute's StartFn is one sharp point, so the distance
  ;; between the start of 14:32 on 17 May 1990 and the start of 09:15 on 21 October 2026
  ;; is exact: 1149619380 seconds.  An instant only known to fall somewhere inside a
  ;; minute (includesInstant) is a different term, not that minute's start, so the
  ;; distance between two such instants is bounded rather than exact even though the two
  ;; minutes are the same precision: each minute's own length counts against the bound,
  ;; for a 120-second width.  The coarser-precision cases this generalises to are
  ;; a-distance-between-two-unknown-instants-is-exactly-as-bounded-as-the-coarser-of-the-two-containing-intervals.
  (v/add-reasoner kb :point :calendar :metric-time)
  (doseq [s ['(dimensionOf Second Duration) '(conversionFactor Second Second 1)]]
    (v/assert kb s U))
  (testing "the distance between the two minutes' starts is exact"
    (is (= [{'?d '(QuantityFn 1149619380 Second)}]
           (v/ask kb '(temporalDistance (StartFn (DatetimeFn "1990-05-17T14:32"))
                                        (StartFn (DatetimeFn "2026-10-21T09:15")) ?d) U))))
  (tu/with-terms [X Y]
    (v/assert kb (list 'includesInstant '(DatetimeFn "1990-05-17T14:32") X) U)
    (v/assert kb (list 'includesInstant '(DatetimeFn "2026-10-21T09:15") Y) U)
    (testing "two unknown instants inside those same-precision minutes give a bounded distance, not an exact one"
      (is (= [{'?d '(QuantityIntervalFn 1149619320 1149619440 Second)}]
             (v/ask kb (list 'temporalDistance X Y '?d) U))))))

(tu/deftest-kb ^:red a-distance-from-a-minute-start-to-a-lower-bound-on-now-is-a-lower-bound
  ;; The present reached only through CxNow's lower-bound readings does not give an
  ;; exact distance: nothing bounds it from above.  The minute is the one from the
  ;; control above, made up; the reading floor is 09:00 on 17 October 2026, also made
  ;; up.  The distance down to the reading's own named moment is exact and stands for
  ;; the lower bound on the distance to now, since now is no earlier than that moment;
  ;; the distance to now itself has no finite upper bound, so temporalDistance returns
  ;; nothing exact and nothing bounded for it.
  (v/add-reasoner kb :point :calendar :metric-time)
  (doseq [s ['(dimensionOf Second Duration) '(conversionFactor Second Second 1)]]
    (v/assert kb s U))
  (reading! kb [2026 10 17 9 0 0])
  (testing "the distance down to the reading floor is exact: a lower bound on the distance to now"
    (is (= [{'?d '(QuantityFn 1149272880 Second)}]
           (v/ask kb '(temporalDistance (StartFn (DatetimeFn "1990-05-17T14:32"))
                                        (InstantFn 2026 10 17 9 0 0) ?d) 'CxRealWorldNow))))
  (testing "no exact or bounded distance to now itself is returned"
    (is (empty? (v/ask kb (list 'temporalDistance '(StartFn (DatetimeFn "1990-05-17T14:32")) now '?d)
                       'CxRealWorldNow)))))

(tu/deftest-kb ^:red a-distance-between-two-unknown-instants-is-exactly-as-bounded-as-the-coarser-of-the-two-containing-intervals
  ;; Varies the precision of each side's containing interval on its own, the other held
  ;; at the minute, the shape this replaces kept.  Each side is an unknown instant
  ;; stated only to fall inside a calendar interval (includesInstant), never a sharp
  ;; point, so even the matching-precision minute/minute row is bounded and not exact —
  ;; a-distance-between-two-minute-starts-is-exact-and-between-two-unknown-instants-inside-them-is-bounded
  ;; already shows why.  includesInstant's half-open convention (at or after the
  ;; interval's StartFn, before its EndFn) makes an interval's end exclusive, so the
  ;; tightest bound for two such instants is [start(later) − end(earlier),
  ;; end(later) − start(earlier)]: the earliest the gap can be is the later interval's
  ;; own first moment minus the earlier interval's own end, and the widest is the later
  ;; interval's own end minus the earlier interval's own first moment.  The dates are
  ;; made up, and the width grows as either side is cut coarser: 120 seconds for two
  ;; minutes, 86460 for a minute against a day, 172800 for two days, and 2678460 for a
  ;; minute against a month.
  (v/add-reasoner kb :point :calendar :metric-time)
  (doseq [s ['(dimensionOf Second Duration) '(conversionFactor Second Second 1)]]
    (v/assert kb s U))
  (let [minute-ref '(DatetimeFn "2026-10-21T09:15")
        day-ref    '(DayFn 2026 10 21)
        gap        (fn [x y] (v/ask kb (list 'temporalDistance x y '?d) U))]
    (tu/with-terms [XMinute XDay XMonth YMinute YDay]
      (v/assert kb (list 'includesInstant '(DatetimeFn "1990-05-17T14:32") XMinute) U)
      (v/assert kb (list 'includesInstant '(DayFn 1990 5 17) XDay) U)
      (v/assert kb (list 'includesInstant '(MonthFn 1990 5) XMonth) U)
      (v/assert kb (list 'includesInstant minute-ref YMinute) U)
      (v/assert kb (list 'includesInstant day-ref YDay) U)
      (testing "both sides to the minute: bounded to a 120-second width"
        (is (= [{'?d '(QuantityIntervalFn 1149619320 1149619440 Second)}] (gap XMinute YMinute))))
      (testing "the earlier side to the day, the later to the minute: bounded to an 86460-second width"
        (is (= [{'?d '(QuantityIntervalFn 1149585300 1149671760 Second)}] (gap XDay YMinute))))
      (testing "the earlier side to the minute, the later to the day: bounded to an 86460-second width"
        (is (= [{'?d '(QuantityIntervalFn 1149586020 1149672480 Second)}] (gap XMinute YDay))))
      (testing "both sides to the day: bounded to a 172800-second width"
        (is (= [{'?d '(QuantityIntervalFn 1149552000 1149724800 Second)}] (gap XDay YDay))))
      (testing "the earlier side to the month, the later to the minute: bounded to a 2678460-second width"
        (is (= [{'?d '(QuantityIntervalFn 1148375700 1151054160 Second)}] (gap XMonth YMinute)))))))

(tu/deftest-kb ^:red a-reading-places-now-after-a-past-year-and-inside-no-year
  ;; A reading of 17 October 2026 places the present after all of 2000, and, with no
  ;; upper bound, inside no year: not even 2026.  So the real world's present sits under
  ;; no year slice, and a fact of the real world's 2026 slice is not known to hold now.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point :calendar)
  (reading! kb [2026 10 17 9 0 0])
  (testing "now is after the end of 2000"
    (is (true? (v/ask? kb (list 'instantNotBefore now '(InstantFn 2001 1 1 0 0 0)) 'CxNow))))
  (testing "and whether 2026 includes now is unknown"
    (is (= :unknown (verdict kb (list 'includesInstant '(YearFn 2026) now) 'CxNow))))
  (tu/with-terms [p]
    (v/assert kb (list p) (real-slice '(YearFn 2026)))
    (testing "so a fact of the real world's 2026 slice is not known now"
      (is (not (v/ask? kb (list p) 'CxRealWorldNow))))))

(tu/deftest-kb ^:red a-reading-at-a-named-moment-places-now-after-a-named-past-year-and-inside-no-named-year
  ;; The reified twin of a-reading-places-now-after-a-past-year-and-inside-no-year: the
  ;; end of 2000, the reading and the years are named, and the calendar's placement of
  ;; the reading (after the end of 2000, inside 2026) is stated.  Red for the original's
  ;; reason: the point prover does not compose the reading's lower bound on now with the
  ;; stated order of the two named moments.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [Y2000 Y2026 End2000 Read]
    (times! kb [Y2000 Y2026] [End2000 Read]
            ['endOf Y2000 End2000] ['instantBefore End2000 Read] ['includesInstant Y2026 Read])
    (reading-at! kb Read)
    (testing "now is after the end of the named 2000"
      (is (true? (v/ask? kb (list 'instantNotBefore now End2000) 'CxNow))))
    (testing "and whether the named 2026 includes now is unknown"
      (is (= :unknown (verdict kb (list 'includesInstant Y2026 now) 'CxNow))))
    (tu/with-terms [p]
      (v/assert kb (list p) (real-slice Y2026))
      (testing "so a fact of the real world's named 2026 slice is not known now"
        (is (not (v/ask? kb (list p) 'CxRealWorldNow)))))))

(tu/deftest-kb ^:red a-past-slice-of-the-real-world-sees-the-real-world-and-not-what-holds-now
  ;; The real world's slice of 2000 sits under its monad CxRealWorld, as any slice sits
  ;; under its monad, and beside CxRealWorldNow rather than under it: what holds now need
  ;; not have held in 2000.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [y2000 (real-slice '(YearFn 2000))]
      (v/assert kb (list p) 'CxRealWorld)
      (v/assert kb (list q) 'CxRealWorldNow)
      (v/assert kb (list r) y2000)
      (testing "the 2000 slice sees a fact of the real world at large"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "and not a fact true now"
        (is (not (v/ask? kb (list q) y2000)))
        (is (= :unknown (verdict kb (list q) y2000)))))))

(tu/deftest-kb ^:red an-eternal-fact-is-visible-from-now-and-from-every-slice
  ;; Iris's eternal example from every vantage, not one year: a fact stated unsliced in
  ;; CxUniverse holds now, in the past and the future, along the real world and along a
  ;; story, at a year and at a day.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxWell) U)
    (v/assert kb (list p) U)
    (testing "control: from CxNow and the real world's present"
      (is (true? (v/ask? kb (list p) 'CxNow)))
      (is (true? (v/ask? kb (list p) 'CxRealWorldNow))))
    (doseq [ctx [(real-slice '(YearFn 2000)) (real-slice '(YearFn 2100))
                 (real-slice '(DayFn 2000 2 29)) (slice CxStory '(YearFn 2000))
                 (slice CxStory '(MonthFn 1066 10))]]
      (testing (str "from " (pr-str ctx))
        (is (true? (v/ask? kb (list p) ctx)))))))

(tu/deftest-kb ^:red an-eternal-fact-is-visible-from-every-slice-along-a-monad-placed-by-genlmonad
  ;; The genlMonad twin of an-eternal-fact-is-visible-from-now-and-from-every-slice: the
  ;; story is placed under CxWell by genlMonad, where the original places it by genlCx.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxStory]
    (v/assert kb (list 'genlMonad CxStory 'CxWell) U)
    (v/assert kb (list p) U)
    (testing "control: from CxNow and the real world's present"
      (is (true? (v/ask? kb (list p) 'CxNow)))
      (is (true? (v/ask? kb (list p) 'CxRealWorldNow))))
    (doseq [ctx [(real-slice '(YearFn 2000)) (real-slice '(YearFn 2100))
                 (real-slice '(DayFn 2000 2 29)) (slice CxStory '(YearFn 2000))
                 (slice CxStory '(MonthFn 1066 10))]]
      (testing (str "from " (pr-str ctx))
        (is (true? (v/ask? kb (list p) ctx)))))))

(tu/deftest-kb ^:red a-fluent-started-in-a-past-slice-holds-now
  ;; Projection to the present: a state started in June 2000, stated in the real world's
  ;; 2000 slice, that nothing has ended since, holds now, and the reading is what puts
  ;; now after June 2000.  The question is asked in CxRealWorldNow, which does not see the
  ;; slice: only the fluent crosses, by inertia, and a plain fact of 2000 does not.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Thing Start p]
    (let [f   (fluent! kb StateFn Thing)
          y2k (real-slice '(YearFn 2000))]
      (happened! kb y2k Start 'initiates f '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list p) y2k)
      (testing "the state holds now"
        (is (true? (v/query? kb (list 'holdsAt f now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "and a plain fact of 2000 is not projected"
        (is (not (v/ask? kb (list p) 'CxRealWorldNow)))))))

(tu/deftest-kb ^:red a-fluent-started-at-a-named-moment-in-a-past-named-slice-holds-now
  ;; The reified twin of a-fluent-started-in-a-past-slice-holds-now: the start, the
  ;; reading and the year are named, the start stated inside the year and before the
  ;; reading.  The point prover takes the place of the calendar clock.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Thing Start p Y2000 Began Read]
    (times! kb [Y2000] [] ['includesInstant Y2000 Began])
    (chain! kb Began Read)
    (reading-at! kb Read)
    (let [f   (fluent! kb StateFn Thing)
          y2k (real-slice Y2000)]
      (happened! kb y2k Start 'initiates f Began)
      (v/assert kb (list p) y2k)
      (testing "the state holds now"
        (is (true? (v/query? kb (list 'holdsAt f now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "and a plain fact of the named 2000 is not projected"
        (is (not (v/ask? kb (list p) 'CxRealWorldNow)))))))

(tu/deftest-kb ^:red a-fluent-ended-after-the-past-slice-does-not-hold-now
  ;; No projection past a terminating event: two states start in 2000, one is ended in
  ;; 2005 (stated in the 2005 slice), and only the other holds now.  The first half is the
  ;; positive control, so the second is not answered by projection being absent.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept Ended Start Stop]
    (let [kept  (fluent! kb StateFn Kept)
          ended (list StateFn Ended)
          y2k   (real-slice '(YearFn 2000))]
      (happened! kb y2k Start 'initiates kept '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list 'initiates Start ended '(InstantFn 2000 6 1 12 0 0)) y2k)
      (happened! kb (real-slice '(YearFn 2005)) Stop 'terminates ended '(InstantFn 2005 3 1 12 0 0))
      (testing "the state nothing ended holds now"
        (is (true? (v/query? kb (list 'holdsAt kept now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "the state ended in 2005 does not"
        (is (not (v/query? kb (list 'holdsAt ended now) 'CxRealWorldNow {:max-depth 3})))))))

(tu/deftest-kb ^:red a-fluent-ended-at-a-named-moment-before-the-reading-does-not-hold-now
  ;; The reified twin of a-fluent-ended-after-the-past-slice-does-not-hold-now.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Kept Ended Start Stop Y2000 Y2005 Began Stopped Read]
    (times! kb [Y2000 Y2005] [] ['includesInstant Y2000 Began] ['includesInstant Y2005 Stopped])
    (chain! kb Began Stopped Read)
    (reading-at! kb Read)
    (let [kept  (fluent! kb StateFn Kept)
          ended (list StateFn Ended)
          y2k   (real-slice Y2000)]
      (happened! kb y2k Start 'initiates kept Began)
      (v/assert kb (list 'initiates Start ended Began) y2k)
      (happened! kb (real-slice Y2005) Stop 'terminates ended Stopped)
      (testing "the state nothing ended holds now"
        (is (true? (v/query? kb (list 'holdsAt kept now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "the state ended before the reading does not"
        (is (not (v/query? kb (list 'holdsAt ended now) 'CxRealWorldNow {:max-depth 3})))))))

(tu/deftest-kb ^:red a-fluent-ended-after-the-reading-is-not-known-to-hold-now
  ;; The bound cuts both ways: a state started in 2000 and ended on 1 March 2030 held at
  ;; the reading of 17 October 2026, but now may be past 2030, so whether it holds now is
  ;; unknown, where a state nothing ended holds.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept Ended Start Stop]
    (let [kept  (fluent! kb StateFn Kept)
          ended (list StateFn Ended)
          y2k   (real-slice '(YearFn 2000))]
      (happened! kb y2k Start 'initiates kept '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list 'initiates Start ended '(InstantFn 2000 6 1 12 0 0)) y2k)
      (happened! kb (real-slice '(YearFn 2030)) Stop 'terminates ended '(InstantFn 2030 3 1 12 0 0))
      (testing "the state nothing ended still holds now"
        (is (true? (v/query? kb (list 'holdsAt kept now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "the state ended in 2030 is unknown now, neither held nor ended"
        (is (= :unknown (verdict kb (list 'holdsAt ended now) 'CxRealWorldNow)))
        (is (not (v/query? kb (list 'holdsAt ended now) 'CxRealWorldNow {:max-depth 3})))))))

(tu/deftest-kb ^:red a-fluent-ended-at-a-named-moment-after-the-reading-is-not-known-to-hold-now
  ;; The reified twin of a-fluent-ended-after-the-reading-is-not-known-to-hold-now.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Kept Ended Start Stop Y2000 Y2030 Began Read Stopped]
    (times! kb [Y2000 Y2030] [] ['includesInstant Y2000 Began] ['includesInstant Y2030 Stopped])
    (chain! kb Began Read Stopped)
    (reading-at! kb Read)
    (let [kept  (fluent! kb StateFn Kept)
          ended (list StateFn Ended)
          y2k   (real-slice Y2000)]
      (happened! kb y2k Start 'initiates kept Began)
      (v/assert kb (list 'initiates Start ended Began) y2k)
      (happened! kb (real-slice Y2030) Stop 'terminates ended Stopped)
      (testing "the state nothing ended still holds now"
        (is (true? (v/query? kb (list 'holdsAt kept now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "the state ended after the reading is unknown now, neither held nor ended"
        (is (= :unknown (verdict kb (list 'holdsAt ended now) 'CxRealWorldNow)))
        (is (not (v/query? kb (list 'holdsAt ended now) 'CxRealWorldNow {:max-depth 3})))))))

(tu/deftest-kb projection-from-now-into-a-dated-future-slice-is-unknown-with-only-lower-bounds
  ;; Projection forward, under the lower-bound ruling.  The present has no upper bound,
  ;; so no dated slice is known to lie after now: with a reading of 17 October 2026, now
  ;; may already be past the start of 2027, and a state observed now is neither held nor
  ;; refuted there.  Correct by design under the ruling, and passing today because no
  ;; slice sees anything.  Projection forward from now to a dated future needs an upper
  ;; bound on now, and an upper bound goes stale, so the spec keeps the verdict unknown:
  ;; a question about a dated future is asked from a dated fact, not from now.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept]
    (let [kept (fluent! kb StateFn Kept)
          t27  '(InstantFn 2027 1 1 0 0 0)
          y27  (real-slice '(YearFn 2027))]
      (v/assert kb (list 'holdsAt kept now) 'CxRealWorldNow)
      (testing "control: it holds now, as stated"
        (is (true? (v/ask? kb (list 'holdsAt kept now) 'CxRealWorldNow))))
      (testing "it is unknown at the start of 2027, which now may be past"
        (is (= :unknown (verdict kb (list 'holdsAt kept t27) y27)))))))

(tu/deftest-kb projection-from-now-into-a-named-future-slice-is-unknown-with-only-lower-bounds
  ;; The reified twin of projection-from-now-into-a-dated-future-slice-is-unknown-with-only-lower-bounds:
  ;; the reading and the later moment are named, the reading stated first.  Correct by
  ;; design under the lower-bound ruling.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Kept Read Later Y2027]
    (times! kb [Y2027] [] ['includesInstant Y2027 Later])
    (chain! kb Read Later)
    (reading-at! kb Read)
    (let [kept (fluent! kb StateFn Kept)
          y27  (real-slice Y2027)]
      (v/assert kb (list 'holdsAt kept now) 'CxRealWorldNow)
      (testing "control: it holds now, as stated"
        (is (true? (v/ask? kb (list 'holdsAt kept now) 'CxRealWorldNow))))
      (testing "it is unknown at the later named moment, which now may be past"
        (is (= :unknown (verdict kb (list 'holdsAt kept Later) y27)))))))

(tu/deftest-kb a-state-holding-now-is-unknown-at-a-dated-past-moment
  ;; Projection backward, under the lower-bound ruling.  The reading puts the start of
  ;; 2025 before now, so the order is known, but a state stated to hold now says nothing
  ;; about an earlier moment: it may have started after it.  Inertia carries a state
  ;; forward from where it started, never back from where it is observed.  Correct by
  ;; design.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept]
    (let [kept (fluent! kb StateFn Kept)
          t25  '(InstantFn 2025 1 1 0 0 0)
          y25  (real-slice '(YearFn 2025))]
      (v/assert kb (list 'holdsAt kept now) 'CxRealWorldNow)
      (testing "control: it holds now, as stated"
        (is (true? (v/ask? kb (list 'holdsAt kept now) 'CxRealWorldNow))))
      (testing "it is unknown at the start of 2025, which is before now"
        (is (= :unknown (verdict kb (list 'holdsAt kept t25) y25)))))))

(tu/deftest-kb a-state-holding-now-is-unknown-at-a-named-past-moment
  ;; The reified twin of a-state-holding-now-is-unknown-at-a-dated-past-moment: the
  ;; earlier moment and the reading are named, the earlier moment stated first.  Correct
  ;; by design.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Kept Earlier Read Y2025]
    (times! kb [Y2025] [] ['includesInstant Y2025 Earlier])
    (chain! kb Earlier Read)
    (reading-at! kb Read)
    (let [kept (fluent! kb StateFn Kept)
          y25  (real-slice Y2025)]
      (v/assert kb (list 'holdsAt kept now) 'CxRealWorldNow)
      (testing "control: it holds now, as stated"
        (is (true? (v/ask? kb (list 'holdsAt kept now) 'CxRealWorldNow))))
      (testing "it is unknown at the earlier named moment"
        (is (= :unknown (verdict kb (list 'holdsAt kept Earlier) y25)))))))

(tu/deftest-kb ^:red a-fluent-started-in-a-past-slice-holds-at-a-later-dated-past-moment
  ;; Projection between two past slices: a state started in June 2000, stated in the real
  ;; world's 2000 slice, that nothing has ended, holds at the start of 2025, asked in the
  ;; 2025 slice.  The calendar fields put 2025 after June 2000; no reading is needed.  A
  ;; plain fact of 2000 is not projected.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (tu/with-terms [StateFn Thing Start p]
    (let [f   (fluent! kb StateFn Thing)
          y2k (real-slice '(YearFn 2000))
          t25 '(InstantFn 2025 1 1 0 0 0)
          y25 (real-slice '(YearFn 2025))]
      (happened! kb y2k Start 'initiates f '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list p) y2k)
      (testing "the state holds at the start of 2025"
        (is (true? (v/query? kb (list 'holdsAt f t25) y25 {:max-depth 3}))))
      (testing "and a plain fact of 2000 is not projected"
        (is (not (v/ask? kb (list p) y25)))))))

(tu/deftest-kb ^:red a-fluent-started-at-a-named-moment-holds-at-a-later-named-past-moment
  ;; The reified twin of a-fluent-started-in-a-past-slice-holds-at-a-later-dated-past-moment:
  ;; the start, the later moment and both years are named, the start stated first.  The
  ;; point prover takes the place of the calendar fields.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Thing Start p Y2000 Y2025 Began Later]
    (times! kb [Y2000 Y2025] []
            ['includesInstant Y2000 Began] ['includesInstant Y2025 Later])
    (chain! kb Began Later)
    (let [f   (fluent! kb StateFn Thing)
          y2k (real-slice Y2000)
          y25 (real-slice Y2025)]
      (happened! kb y2k Start 'initiates f Began)
      (v/assert kb (list p) y2k)
      (testing "the state holds at the later named moment"
        (is (true? (v/query? kb (list 'holdsAt f Later) y25 {:max-depth 3}))))
      (testing "and a plain fact of the named 2000 is not projected"
        (is (not (v/ask? kb (list p) y25)))))))

;; =========================================================================
;; Slices keyed by other kinds of time
;; =========================================================================
;; Every slice above is keyed by a calendar term or by a named interval ordered by
;; stated or Allen-entailed relations.  These key a slice by a moment, by a time with
;; gaps, and by the same month spelled two ways.

(tu/deftest-kb ^:red two-spellings-of-one-month-name-one-context
  ;; Stronger than two-spellings-of-one-month-see-each-others-facts: the two spellings
  ;; denote one interval, so they are one context, and a write through either lands in
  ;; the same cx/ constant.
  (declare-cxtimefn! kb)
  (testing "MonthFn and DatetimeFn for January 2000 reify to one cx/ context"
    (is (false? (:distinct? (two-spellings kb (slice '(MonthFn 2000 1))
                                           (slice '(DatetimeFn "2000-01"))))))))

(tu/deftest-kb ^:red two-names-of-one-interval-name-one-context
  ;; The reified twin of two-spellings-of-one-month-name-one-context: two names stated
  ;; intervalEqual denote one interval, so a write through either lands in one cx/ context.
  (declare-cxtimefn! kb)
  (tu/with-terms [JanA JanB]
    (times! kb [JanA JanB] []
            ['intervalEqual JanA JanB] ['subintervalOf JanA JanB] ['subintervalOf JanB JanA])
    (testing "two names stated intervalEqual reify to one cx/ context"
      (is (false? (:distinct? (two-spellings kb (slice JanA) (slice JanB))))))))

(tu/deftest-kb ^:red two-spellings-of-one-moment-name-one-context
  ;; The point twin of two-spellings-of-one-month-name-one-context.
  (declare-cxtimefn! kb)
  (testing "InstantFn and StartFn for midnight at the start of 2000 reify to one cx/ context"
    (is (false? (:distinct? (two-spellings kb (slice '(InstantFn 2000 1 1 0 0 0))
                                           (slice '(StartFn (MonthFn 2000 1))))))))
  (testing "control: the point network takes the two spellings for one moment"
    (v/add-reasoner kb :point)
    (is (true? (v/ask? kb '(instantEqual (InstantFn 2000 1 1 0 0 0) (StartFn (MonthFn 2000 1))) U)))))

(tu/deftest-kb ^:red two-names-of-one-monad-name-one-context
  ;; The monad-dimension twin of two-spellings-of-one-month-name-one-context.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxA CxB]
    (monads! kb CxA CxB)
    (v/assert kb (list 'genlMonad CxA CxB) U)
    (v/assert kb (list 'genlMonad CxB CxA) U)
    (testing "the year 2000 along two names of one monad reifies to one cx/ context"
      (is (false? (:distinct? (two-spellings kb (slice CxA '(YearFn 2000))
                                             (slice CxB '(YearFn 2000)))))))))

(tu/deftest-kb ^:red a-fact-in-a-year-slice-holds-in-a-slice-keyed-by-an-instant-inside-it
  ;; Homogeneity, downward: a fact true throughout 2000 is true at each moment of 2000.
  ;; A slice keyed by an InstantFn moment is ordered under a slice keyed by an interval
  ;; that includes the moment (includesInstant), which is not subintervalOf: a time_point
  ;; is not a time_interval.  Upward it does not hold, by design: a fact stated at one
  ;; moment of 2000 is not thereby true throughout 2000.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q]
    (let [y2000    (slice '(YearFn 2000))
          noon     (slice '(InstantFn 2000 6 1 12 0 0))
          noon2001 (slice '(InstantFn 2001 6 1 12 0 0))]
      (v/assert kb (list p) y2000)
      (v/assert kb (list q) noon)
      (testing "the year's fact holds in the slice keyed by a moment inside the year"
        (is (true? (v/ask? kb (list p) noon))))
      (testing "and not in the slice keyed by a moment of 2001"
        (is (not (v/ask? kb (list p) noon2001))))
      (testing "the moment's own fact is not lifted to the year"
        (is (not (v/ask? kb (list q) y2000)))))))

(tu/deftest-kb ^:red a-fact-in-a-named-year-slice-holds-in-a-slice-keyed-by-a-named-moment-inside-it
  ;; The reified twin of a-fact-in-a-year-slice-holds-in-a-slice-keyed-by-an-instant-inside-it.
  ;; The calendar places noon of 1 June 2000 inside 2000 and noon of 1 June 2001 after its
  ;; end; here both are stated of a named year and two named moments.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q Y2000 Noon Noon2001]
    (times! kb [Y2000] [Noon Noon2001]
            ['includesInstant Y2000 Noon] ['instantBefore (list 'EndFn Y2000) Noon2001])
    (let [y2000    (slice Y2000)
          noon     (slice Noon)
          noon2001 (slice Noon2001)]
      (v/assert kb (list p) y2000)
      (v/assert kb (list q) noon)
      (testing "the named year's fact holds in the slice keyed by a named moment inside it"
        (is (true? (v/ask? kb (list p) noon))))
      (testing "and not in the slice keyed by a moment after the year's end"
        (is (not (v/ask? kb (list p) noon2001))))
      (testing "the moment's own fact is not lifted to the year"
        (is (not (v/ask? kb (list q) y2000)))))))

(tu/deftest-kb ^:red a-slice-keyed-by-an-intermittent-time-sits-between-its-pieces-and-its-whole
  ;; An intermittent_time has gaps, so it is not a time_interval and subintervalOf, the
  ;; ordering CxTimeFn is declared over, does not apply to it.  The weekends of 2000 are
  ;; part of 2000, and 1 January 2000, a Saturday, is part of the weekends.  A slice keyed
  ;; by the weekends ought to see the year, and the Saturday's slice ought to see the
  ;; weekends'; 3 January 2000, a Monday, is in a gap and sees nothing of the weekends.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r Weekends2000]
    (v/assert kb (list 'intermittent_time Weekends2000) U)
    (v/assert kb (list 'partOf Weekends2000 '(YearFn 2000)) U)
    (v/assert kb (list 'partOf '(DayFn 2000 1 1) Weekends2000) U)
    (v/assert kb (list 'temporallyDisjoint '(DayFn 2000 1 3) Weekends2000) U)
    (let [year     (slice '(YearFn 2000))
          weekends (slice Weekends2000)
          saturday (slice '(DayFn 2000 1 1))
          monday   (slice '(DayFn 2000 1 3))]
      (v/assert kb (list p) year)
      (v/assert kb (list q) weekends)
      (v/assert kb (list r) monday)
      (testing "the weekends' slice sees the year's fact"
        (is (true? (v/ask? kb (list p) weekends))))
      (testing "a Saturday's slice sees the weekends' fact, and the year's"
        (is (true? (v/ask? kb (list q) saturday)))
        (is (true? (v/ask? kb (list p) saturday))))
      (testing "a Monday's slice sees the year's fact and not the weekends'"
        (is (true? (v/ask? kb (list p) monday)))
        (is (not (v/ask? kb (list q) monday)))))))

(tu/deftest-kb ^:red a-slice-keyed-by-an-intermittent-time-sits-between-its-named-pieces-and-its-named-whole
  ;; The reified twin of a-slice-keyed-by-an-intermittent-time-sits-between-its-pieces-and-its-whole:
  ;; the year, the Saturday and the Monday are named intervals, and what the calendar
  ;; fields say of them (both days inside the year, the Saturday before the Monday) is
  ;; stated beside the original's partOf and temporallyDisjoint facts.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r Weekends2000 Y2000 Sat Mon]
    (times! kb [Y2000 Sat Mon] []
            ['subintervalOf Sat Y2000] ['subintervalOf Mon Y2000] ['before Sat Mon])
    (v/assert kb (list 'intermittent_time Weekends2000) U)
    (v/assert kb (list 'partOf Weekends2000 Y2000) U)
    (v/assert kb (list 'partOf Sat Weekends2000) U)
    (v/assert kb (list 'temporallyDisjoint Mon Weekends2000) U)
    (let [year     (slice Y2000)
          weekends (slice Weekends2000)
          saturday (slice Sat)
          monday   (slice Mon)]
      (v/assert kb (list p) year)
      (v/assert kb (list q) weekends)
      (v/assert kb (list r) monday)
      (testing "the weekends' slice sees the named year's fact"
        (is (true? (v/ask? kb (list p) weekends))))
      (testing "the named Saturday's slice sees the weekends' fact, and the year's"
        (is (true? (v/ask? kb (list q) saturday)))
        (is (true? (v/ask? kb (list p) saturday))))
      (testing "the named Monday's slice sees the year's fact and not the weekends'"
        (is (true? (v/ask? kb (list p) monday)))
        (is (not (v/ask? kb (list q) monday)))))))

(tu/deftest-kb ^:red an-instant-on-a-weekend-day-sees-the-weekends-and-an-instant-in-a-gap-does-not
  ;; The point twin of a-slice-keyed-by-an-intermittent-time-sits-between-its-pieces-and-its-whole:
  ;; noon on the Saturday and noon on the Monday in place of the two days.  A moment inside
  ;; a piece of an intermittent time is inside it, and a moment in a gap is not.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r Weekends2000]
    (v/assert kb (list 'intermittent_time Weekends2000) U)
    (v/assert kb (list 'partOf Weekends2000 '(YearFn 2000)) U)
    (v/assert kb (list 'partOf '(DayFn 2000 1 1) Weekends2000) U)
    (v/assert kb (list 'temporallyDisjoint '(DayFn 2000 1 3) Weekends2000) U)
    (let [year     (slice '(YearFn 2000))
          weekends (slice Weekends2000)
          saturday (slice '(InstantFn 2000 1 1 12 0 0))
          monday   (slice '(InstantFn 2000 1 3 12 0 0))]
      (v/assert kb (list p) year)
      (v/assert kb (list q) weekends)
      (v/assert kb (list r) monday)
      (testing "a Saturday moment's slice sees the weekends' fact, and the year's"
        (is (true? (v/ask? kb (list q) saturday)))
        (is (true? (v/ask? kb (list p) saturday))))
      (testing "a Monday moment's slice sees the year's fact and not the weekends'"
        (is (true? (v/ask? kb (list p) monday)))
        (is (not (v/ask? kb (list q) monday)))))))

;; =========================================================================
;; Ranges — a slice keyed by a time_interval given by its bounds
;; =========================================================================
;; YearFn, MonthFn, DayFn and DatetimeFn each name one calendar unit, and calendar units
;; nest or are disjoint and never partially overlap (docs/time.md).  A range such as
;; 2000-01..2000-06 is written two ways here.  Each original is a named time_interval
;; whose startOf and endOf are stated as InstantFn moments, the bounds the calendar clock
;; computes for a calendar term; the end of one unit and the start of the next are the
;; same InstantFn, so the bounds are the clock's own.  Its DatetimeRangeFn twin, beside
;; it, writes the same range as (DatetimeRangeFn "2000-01" "2000-06") and states nothing:
;; time.txt's two rules give the term its bounds.  Each test asks the slices to be
;; ordered from the bounds alone: no subintervalOf and no Allen relation is stated
;; between two ranges or between a range and a calendar term.

(defn- range!
  "Make `name` the time_interval from `start` to `end`, two InstantFn field vectors."
  [kb name start end]
  (v/assert kb (list 'time_interval name) U)
  (v/assert kb (list 'startOf name (cons 'InstantFn start)) U)
  (v/assert kb (list 'endOf name (cons 'InstantFn end)) U))

(defn- bounded!
  "Make `name` the time_interval from the moment `start` to the moment `end`, two terms."
  [kb name start end]
  (v/assert kb (list 'time_interval name) U)
  (v/assert kb (list 'startOf name start) U)
  (v/assert kb (list 'endOf name end) U))

(defn- range-bounds
  "The startOf and endOf the defining rules answer for the DatetimeRangeFn term `r`, as
  `[start end]` (each a vector of the answers), with the calendar clock registered."
  [kb r]
  [(mapv #(get % '?i) (v/query kb (list 'startOf r '?i) U {:max-depth 3}))
   (mapv #(get % '?i) (v/query kb (list 'endOf r '?i) U {:max-depth 3}))])

(tu/deftest-kb ^:red a-fact-in-a-range-is-visible-from-a-subrange-and-from-each-calendar-term-inside-it
  ;; The first quarter of 2000, and February to March inside it.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p Q1 FebMar]
    (range! kb Q1 [2000 1 1 0 0 0] [2000 4 1 0 0 0])
    (range! kb FebMar [2000 2 1 0 0 0] [2000 4 1 0 0 0])
    (v/assert kb (list p) (slice Q1))
    (doseq [inside [(slice FebMar) (slice '(MonthFn 2000 1)) (slice '(MonthFn 2000 3))
                    (slice '(DayFn 2000 2 15)) (slice '(DatetimeFn "2000-03-31T23"))]]
      (testing (str "the range's fact is visible from " (pr-str inside))
        (is (true? (v/ask? kb (list p) inside)))))
    (doseq [outside [(slice '(MonthFn 2000 4)) (slice '(YearFn 2000))]]
      (testing (str "and not from " (pr-str outside) ", which is not inside the range")
        (is (not (v/ask? kb (list p) outside)))))))

(tu/deftest-kb ^:red a-fact-in-a-range-bounded-by-named-moments-is-visible-from-each-named-time-inside-it
  ;; The reified twin of a-fact-in-a-range-is-visible-from-a-subrange-and-from-each-calendar-term-inside-it.
  ;; Every bound is a named moment, ordered by stated instantBefore facts in the order the
  ;; calendar gives the original's InstantFn bounds, and each calendar term the original
  ;; names is a named interval between two of them.  The point prover takes the place of
  ;; the calendar clock.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [p Jan1 Feb1 Feb15 Feb16 Mar1 Mar31h23 Apr1 May1 Y2001
                  Q1 FebMar Jan Mar Feb15th LastHour Apr Y2000]
    (chain! kb Jan1 Feb1 Feb15 Feb16 Mar1 Mar31h23 Apr1 May1 Y2001)
    (doseq [[n s e] [[Q1 Jan1 Apr1] [FebMar Feb1 Apr1] [Jan Jan1 Feb1] [Mar Mar1 Apr1]
                     [Feb15th Feb15 Feb16] [LastHour Mar31h23 Apr1] [Apr Apr1 May1]
                     [Y2000 Jan1 Y2001]]]
      (bounded! kb n s e))
    (v/assert kb (list p) (slice Q1))
    (doseq [inside [FebMar Jan Mar Feb15th LastHour]]
      (testing (str "the range's fact is visible from " inside)
        (is (true? (v/ask? kb (list p) (slice inside))))))
    (doseq [outside [Apr Y2000]]
      (testing (str "and not from " outside ", which is not inside the range")
        (is (not (v/ask? kb (list p) (slice outside))))))))

(tu/deftest-kb ^:red a-fact-in-a-datetime-range-is-visible-from-a-subrange-and-from-each-calendar-term-inside-it
  ;; The DatetimeRangeFn twin of a-fact-in-a-range-is-visible-from-a-subrange-and-from-each-calendar-term-inside-it:
  ;; the first quarter is (DatetimeRangeFn "2000-01" "2000-03") and February to March
  ;; (DatetimeRangeFn "2000-02" "2000-03"), with nothing stated of either.  The control
  ;; is that the defining rules give each range the bounds the original states.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (let [q1     '(DatetimeRangeFn "2000-01" "2000-03")
        febmar '(DatetimeRangeFn "2000-02" "2000-03")]
    (testing "control: the ranges begin and end where the original's stated bounds do"
      (is (= [['(InstantFn 2000 1 1 0 0 0)] ['(InstantFn 2000 4 1 0 0 0)]] (range-bounds kb q1)))
      (is (= [['(InstantFn 2000 2 1 0 0 0)] ['(InstantFn 2000 4 1 0 0 0)]] (range-bounds kb febmar))))
    (tu/with-terms [p]
      (v/assert kb (list p) (slice q1))
      (doseq [inside [(slice febmar) (slice '(MonthFn 2000 1)) (slice '(MonthFn 2000 3))
                      (slice '(DayFn 2000 2 15)) (slice '(DatetimeFn "2000-03-31T23"))]]
        (testing (str "the range's fact is visible from " (pr-str inside))
          (is (true? (v/ask? kb (list p) inside)))))
      (doseq [outside [(slice '(MonthFn 2000 4)) (slice '(YearFn 2000))]]
        (testing (str "and not from " (pr-str outside) ", which is not inside the range")
          (is (not (v/ask? kb (list p) outside))))))))

(tu/deftest-kb ^:red a-fact-in-a-range-holds-at-each-instant-inside-it
  ;; The point twin of a-fact-in-a-range-is-visible-from-a-subrange-and-from-each-calendar-term-inside-it:
  ;; moments in place of the subrange and the calendar terms.  Half-open: the range's
  ;; start is inside it and its end is not.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p Q1]
    (range! kb Q1 [2000 1 1 0 0 0] [2000 4 1 0 0 0])
    (v/assert kb (list p) (slice Q1))
    (doseq [inside ['(InstantFn 2000 1 1 0 0 0) '(InstantFn 2000 2 15 12 0 0)
                    '(InstantFn 2000 3 31 23 59 59)]]
      (testing (str "the range's fact holds at " (pr-str inside))
        (is (true? (v/ask? kb (list p) (slice inside))))))
    (doseq [outside ['(InstantFn 2000 4 1 0 0 0) '(InstantFn 1999 12 31 23 59 59)]]
      (testing (str "and not at " (pr-str outside) ", which is not inside the range")
        (is (not (v/ask? kb (list p) (slice outside))))))))

(tu/deftest-kb ^:red a-range-inside-a-month-sees-the-month-and-its-year
  ;; The converse direction: a range is ordered under the calendar terms containing it.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p q r MidFeb]
    (range! kb MidFeb [2000 2 10 0 0 0] [2000 2 20 0 0 0])
    (v/assert kb (list p) (slice '(MonthFn 2000 2)))
    (v/assert kb (list q) (slice '(YearFn 2000)))
    (v/assert kb (list r) (slice '(MonthFn 2000 3)))
    (testing "the range's slice sees February's fact and 2000's"
      (is (true? (v/ask? kb (list p) (slice MidFeb))))
      (is (true? (v/ask? kb (list q) (slice MidFeb)))))
    (testing "and not March's"
      (is (not (v/ask? kb (list r) (slice MidFeb)))))))

(tu/deftest-kb ^:red a-range-bounded-by-named-moments-inside-a-named-month-sees-the-month-and-its-year
  ;; The reified twin of a-range-inside-a-month-sees-the-month-and-its-year.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point)
  (tu/with-terms [p q r Jan1 Feb1 Feb10 Feb20 Mar1 Apr1 Y2001 MidFeb Feb Y2000 Mar]
    (chain! kb Jan1 Feb1 Feb10 Feb20 Mar1 Apr1 Y2001)
    (doseq [[n s e] [[MidFeb Feb10 Feb20] [Feb Feb1 Mar1] [Y2000 Jan1 Y2001] [Mar Mar1 Apr1]]]
      (bounded! kb n s e))
    (v/assert kb (list p) (slice Feb))
    (v/assert kb (list q) (slice Y2000))
    (v/assert kb (list r) (slice Mar))
    (testing "the range's slice sees the named February's fact and the named 2000's"
      (is (true? (v/ask? kb (list p) (slice MidFeb))))
      (is (true? (v/ask? kb (list q) (slice MidFeb)))))
    (testing "and not the named March's"
      (is (not (v/ask? kb (list r) (slice MidFeb)))))))

(tu/deftest-kb ^:red a-datetime-range-inside-a-month-sees-the-month-and-its-year
  ;; The DatetimeRangeFn twin of a-range-inside-a-month-sees-the-month-and-its-year: the
  ;; tenth to the nineteenth of February, which ends when the nineteenth ends, at the
  ;; original's stated end.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (let [midfeb '(DatetimeRangeFn "2000-02-10" "2000-02-19")]
    (testing "control: the range begins and ends where the original's stated bounds do"
      (is (= [['(InstantFn 2000 2 10 0 0 0)] ['(InstantFn 2000 2 20 0 0 0)]]
             (range-bounds kb midfeb))))
    (tu/with-terms [p q r]
      (v/assert kb (list p) (slice '(MonthFn 2000 2)))
      (v/assert kb (list q) (slice '(YearFn 2000)))
      (v/assert kb (list r) (slice '(MonthFn 2000 3)))
      (testing "the range's slice sees February's fact and 2000's"
        (is (true? (v/ask? kb (list p) (slice midfeb))))
        (is (true? (v/ask? kb (list q) (slice midfeb)))))
      (testing "and not March's"
        (is (not (v/ask? kb (list r) (slice midfeb))))))))

(tu/deftest-kb ^:red an-instant-inside-a-month-sees-the-month-and-its-year
  ;; The point twin of a-range-inside-a-month-sees-the-month-and-its-year: a moment of
  ;; February in place of the range inside it.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p q r]
    (let [noon (slice '(InstantFn 2000 2 15 12 0 0))]
      (v/assert kb (list p) (slice '(MonthFn 2000 2)))
      (v/assert kb (list q) (slice '(YearFn 2000)))
      (v/assert kb (list r) (slice '(MonthFn 2000 3)))
      (testing "the moment's slice sees February's fact and 2000's"
        (is (true? (v/ask? kb (list p) noon)))
        (is (true? (v/ask? kb (list q) noon))))
      (testing "and not March's"
        (is (not (v/ask? kb (list r) noon)))))))

(tu/deftest-kb ^:red two-partially-overlapping-ranges-and-their-intersection
  ;; Iris's third example as she put it: January to June 2000 and April to September
  ;; 2000 overlap, and April to June is their intersection.  Unlike
  ;; partially-overlapping-slices-and-their-intersection, no relation between the
  ;; three is stated: the ordering comes from the bounds.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p q r JanJun AprSep AprJun]
    (range! kb JanJun [2000 1 1 0 0 0] [2000 7 1 0 0 0])
    (range! kb AprSep [2000 4 1 0 0 0] [2000 10 1 0 0 0])
    (range! kb AprJun [2000 4 1 0 0 0] [2000 7 1 0 0 0])
    (let [h1   (slice JanJun)
          h2   (slice AprSep)
          both (slice AprJun)]
      (v/assert kb (list p) h1)
      (v/assert kb (list q) h2)
      (v/assert kb (list r) both)
      (testing "the bounds entail the overlap and the intersection's place inside both"
        (is (true? (v/ask? kb (list 'overlaps JanJun AprSep) U)))
        (is (true? (v/ask? kb (list 'subintervalOf AprJun JanJun) U)))
        (is (true? (v/ask? kb (list 'subintervalOf AprJun AprSep) U))))
      (testing "neither overlapping range's slice sees the other's fact"
        (is (not (v/ask? kb (list q) h1)))
        (is (not (v/ask? kb (list p) h2))))
      (testing "the intersection's slice sees both"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "and neither overlapping slice sees the intersection's fact"
        (is (not (v/ask? kb (list r) h1)))
        (is (not (v/ask? kb (list r) h2))))
      (testing "May 2000, inside the intersection, sees all three"
        (doseq [s [p q r]]
          (is (true? (v/ask? kb (list s) (slice '(MonthFn 2000 5))))))))))

(tu/deftest-kb ^:red two-partially-overlapping-ranges-bounded-by-named-moments-and-their-intersection
  ;; The reified twin of two-partially-overlapping-ranges-and-their-intersection: the six
  ;; bounds are named moments in the calendar's order, and no relation between the ranges
  ;; is stated.  The point prover takes the place of the calendar clock, with the interval
  ;; prover beside it to read relations off the bounds.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :allen :point)
  (tu/with-terms [p q r Jan1 Apr1 May1 Jun1 Jul1 Oct1 JanJun AprSep AprJun May]
    (chain! kb Jan1 Apr1 May1 Jun1 Jul1 Oct1)
    (doseq [[n s e] [[JanJun Jan1 Jul1] [AprSep Apr1 Oct1] [AprJun Apr1 Jul1] [May May1 Jun1]]]
      (bounded! kb n s e))
    (let [h1   (slice JanJun)
          h2   (slice AprSep)
          both (slice AprJun)]
      (v/assert kb (list p) h1)
      (v/assert kb (list q) h2)
      (v/assert kb (list r) both)
      (testing "the bounds entail the overlap and the intersection's place inside both"
        (is (true? (v/ask? kb (list 'overlaps JanJun AprSep) U)))
        (is (true? (v/ask? kb (list 'subintervalOf AprJun JanJun) U)))
        (is (true? (v/ask? kb (list 'subintervalOf AprJun AprSep) U))))
      (testing "neither overlapping range's slice sees the other's fact"
        (is (not (v/ask? kb (list q) h1)))
        (is (not (v/ask? kb (list p) h2))))
      (testing "the intersection's slice sees both"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "and neither overlapping slice sees the intersection's fact"
        (is (not (v/ask? kb (list r) h1)))
        (is (not (v/ask? kb (list r) h2))))
      (testing "the named May, inside the intersection, sees all three"
        (doseq [s [p q r]]
          (is (true? (v/ask? kb (list s) (slice May)))))))))

(tu/deftest-kb ^:red two-partially-overlapping-datetime-ranges-and-their-intersection
  ;; The DatetimeRangeFn twin of two-partially-overlapping-ranges-and-their-intersection,
  ;; in the words Iris chose the function for: (DatetimeRangeFn "2000-01" "2000-06") and
  ;; (DatetimeRangeFn "2000-04" "2000-09") overlap, and (DatetimeRangeFn "2000-04"
  ;; "2000-06") is their intersection.  Nothing is stated of any of the three.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (let [jan-jun '(DatetimeRangeFn "2000-01" "2000-06")
        apr-sep '(DatetimeRangeFn "2000-04" "2000-09")
        apr-jun '(DatetimeRangeFn "2000-04" "2000-06")
        h1      (slice jan-jun)
        h2      (slice apr-sep)
        both    (slice apr-jun)]
    (testing "control: the ranges begin and end where the original's stated bounds do"
      (is (= [['(InstantFn 2000 1 1 0 0 0)] ['(InstantFn 2000 7 1 0 0 0)]] (range-bounds kb jan-jun)))
      (is (= [['(InstantFn 2000 4 1 0 0 0)] ['(InstantFn 2000 10 1 0 0 0)]] (range-bounds kb apr-sep)))
      (is (= [['(InstantFn 2000 4 1 0 0 0)] ['(InstantFn 2000 7 1 0 0 0)]] (range-bounds kb apr-jun))))
    (tu/with-terms [p q r]
      (v/assert kb (list p) h1)
      (v/assert kb (list q) h2)
      (v/assert kb (list r) both)
      (testing "the bounds entail the overlap and the intersection's place inside both"
        (is (true? (v/ask? kb (list 'overlaps jan-jun apr-sep) U)))
        (is (true? (v/ask? kb (list 'subintervalOf apr-jun jan-jun) U)))
        (is (true? (v/ask? kb (list 'subintervalOf apr-jun apr-sep) U))))
      (testing "neither overlapping range's slice sees the other's fact"
        (is (not (v/ask? kb (list q) h1)))
        (is (not (v/ask? kb (list p) h2))))
      (testing "the intersection's slice sees both"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "and neither overlapping slice sees the intersection's fact"
        (is (not (v/ask? kb (list r) h1)))
        (is (not (v/ask? kb (list r) h2))))
      (testing "May 2000, inside the intersection, sees all three"
        (doseq [s [p q r]]
          (is (true? (v/ask? kb (list s) (slice '(MonthFn 2000 5))))))))))

(tu/deftest-kb ^:red an-instant-in-the-intersection-of-two-overlapping-ranges-sees-both
  ;; The point twin of two-partially-overlapping-ranges-and-their-intersection: moments
  ;; in place of the intersection.  A moment has no extent, so it is in both ranges, in
  ;; one, or in neither, and two moments never overlap; the intersection is the stretch
  ;; whose moments are in both.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [p q JanJun AprSep]
    (range! kb JanJun [2000 1 1 0 0 0] [2000 7 1 0 0 0])
    (range! kb AprSep [2000 4 1 0 0 0] [2000 10 1 0 0 0])
    (v/assert kb (list p) (slice JanJun))
    (v/assert kb (list q) (slice AprSep))
    (let [may (slice '(InstantFn 2000 5 15 12 0 0))
          feb (slice '(InstantFn 2000 2 15 12 0 0))
          aug (slice '(InstantFn 2000 8 15 12 0 0))]
      (testing "a moment in the intersection sees both ranges' facts"
        (is (true? (v/ask? kb (list p) may)))
        (is (true? (v/ask? kb (list q) may))))
      (testing "a moment in the first range only sees only its fact"
        (is (true? (v/ask? kb (list p) feb)))
        (is (not (v/ask? kb (list q) feb))))
      (testing "and a moment in the second range only sees only the second's"
        (is (true? (v/ask? kb (list q) aug)))
        (is (not (v/ask? kb (list p) aug)))))))

(tu/deftest-kb ^:red a-range-and-a-calendar-term-with-the-same-bounds-name-one-context
  ;; A range from the start of 2000 to the start of 2001 is the year 2000, as
  ;; (MonthFn 2000 1) and (DatetimeFn "2000-01") are one month
  ;; (two-spellings-of-one-month-name-one-context).
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (tu/with-terms [Y2000]
    (range! kb Y2000 [2000 1 1 0 0 0] [2001 1 1 0 0 0])
    (testing "the bounds entail that the range and the year are one interval"
      (is (true? (v/ask? kb (list 'intervalEqual Y2000 '(YearFn 2000)) U))))
    (let [{:keys [distinct? first-sees-second? second-sees-first?]}
          (two-spellings kb (slice Y2000) (slice '(YearFn 2000)))]
      (testing "a write through either lands in one cx/ context"
        (is (false? distinct?)))
      (testing "and each sees the other's fact"
        (is (true? first-sees-second?))
        (is (true? second-sees-first?))))))

(tu/deftest-kb ^:red two-ranges-with-the-same-named-bounds-name-one-context
  ;; The reified twin of a-range-and-a-calendar-term-with-the-same-bounds-name-one-context:
  ;; both ranges run between the same two named moments.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :allen :point)
  (tu/with-terms [Start End RangeA RangeB]
    (chain! kb Start End)
    (bounded! kb RangeA Start End)
    (bounded! kb RangeB Start End)
    (testing "the bounds entail that the two ranges are one interval"
      (is (true? (v/ask? kb (list 'intervalEqual RangeA RangeB) U))))
    (let [{:keys [distinct? first-sees-second? second-sees-first?]}
          (two-spellings kb (slice RangeA) (slice RangeB))]
      (testing "a write through either lands in one cx/ context"
        (is (false? distinct?)))
      (testing "and each sees the other's fact"
        (is (true? first-sees-second?))
        (is (true? second-sees-first?))))))

(tu/deftest-kb ^:red a-datetime-range-and-a-calendar-term-with-the-same-bounds-name-one-context
  ;; The DatetimeRangeFn twin of a-range-and-a-calendar-term-with-the-same-bounds-name-one-context:
  ;; January through December 2000 is the year 2000.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (let [jan-dec '(DatetimeRangeFn "2000-01" "2000-12")]
    (testing "control: the range begins and ends where the year does"
      (is (= [['(InstantFn 2000 1 1 0 0 0)] ['(InstantFn 2001 1 1 0 0 0)]] (range-bounds kb jan-dec))))
    (testing "the bounds entail that the range and the year are one interval"
      (is (true? (v/ask? kb (list 'intervalEqual jan-dec '(YearFn 2000)) U))))
    (let [{:keys [distinct? first-sees-second? second-sees-first?]}
          (two-spellings kb (slice jan-dec) (slice '(YearFn 2000)))]
      (testing "a write through either lands in one cx/ context"
        (is (false? distinct?)))
      (testing "and each sees the other's fact"
        (is (true? first-sees-second?))
        (is (true? second-sees-first?))))))

;; =========================================================================
;; CxChange — two transitions in a row
;; =========================================================================

(defn- narrative!
  "A fresh context below CxChange holding `facts`, returned."
  [kb facts]
  (let [ctx (tu/tmp-ctx "Story")]
    (v/assert kb (list 'genlCx ctx 'CxChange) 'CxChange)
    (run! #(v/assert kb % ctx) facts)
    ctx))

(defn- holds-at? [kb ctx f t]
  (v/query? kb (list 'holdsAt f t) ctx {:max-depth 3}))

(defn- narrative-under-genlmonad!
  "A fresh context placed below CxChange by genlMonad rather than genlCx, holding
  `facts`, returned."
  [kb facts]
  (let [ctx (tu/tmp-ctx "Story")]
    (v/assert kb (list 'genlMonad ctx 'CxChange) 'CxChange)
    (run! #(v/assert kb % ctx) facts)
    ctx))

(tu/deftest-kb a-state-that-goes-draft-ready-draft-follows-both-transitions
  ;; A document starts as a draft, is promoted to ready at T1, and demoted back to draft
  ;; at T2.  Each event initiates one state and terminates the other.  Draft holds before
  ;; T1 from `initially`, and after T2 from the demotion's initiation, so the second draft
  ;; is a second stretch of the same fluent.
  (tu/with-terms [DraftFn ReadyFn Doc Promote Demote T0 T1 T15 T2 T3]
    (let [draft (list DraftFn Doc)
          ready (list ReadyFn Doc)
          ctx   (narrative! kb
                            (concat
                             [(list 'result DraftFn 'fluent) (list 'result ReadyFn 'fluent)]
                             (for [t [T0 T1 T15 T2 T3]] (list 'time_point t))
                             [(list 'instantBefore T0 T1) (list 'instantBefore T1 T15)
                              (list 'instantBefore T15 T2) (list 'instantBefore T2 T3)
                              (list 'initially draft)
                              (list 'causal_event Promote) (list 'causal_event Demote)
                              (list 'happens Promote T1)
                              (list 'initiates Promote ready T1)
                              (list 'terminates Promote draft T1)
                              (list 'happens Demote T2)
                              (list 'initiates Demote draft T2)
                              (list 'terminates Demote ready T2)]))]
      (testing "draft before the promotion, ready between the two events"
        (is (holds-at? kb ctx draft T0))
        (is (not (holds-at? kb ctx ready T0)))
        (is (holds-at? kb ctx ready T15))
        (is (not (holds-at? kb ctx draft T15))))
      (testing "draft again after the demotion, and no longer ready"
        (is (holds-at? kb ctx draft T3))
        (is (not (holds-at? kb ctx ready T3))))
      (testing "at the instant of an event the old state still holds and the new one does not"
        (is (holds-at? kb ctx draft T1))
        (is (not (holds-at? kb ctx ready T1)))
        (is (holds-at? kb ctx ready T2))
        (is (not (holds-at? kb ctx draft T2))))
      (testing "the derived reasons are stored: ready was clipped between T1 and T3"
        (is (seq (v/sentexes-matching kb (list 'clipped T1 ready T3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clippedBefore draft T15) ctx)))))))

(tu/deftest-kb a-state-dated-by-calendar-moments-goes-draft-ready-draft-and-follows-both-transitions
  ;; The calendar twin of a-state-that-goes-draft-ready-draft-follows-both-transitions:
  ;; the five named moments become InstantFn moments in the same order, and what the
  ;; original states of them (each a time_point, each before the next) is stated of these.
  (tu/with-terms [DraftFn ReadyFn Doc Promote Demote]
    (let [[t0 t1 t15 t2 t3] (for [d [1 2 3 4 5]] (list 'InstantFn 2000 1 d 12 0 0))
          draft (list DraftFn Doc)
          ready (list ReadyFn Doc)
          ctx   (narrative! kb
                            (concat
                             [(list 'result DraftFn 'fluent) (list 'result ReadyFn 'fluent)]
                             (for [t [t0 t1 t15 t2 t3]] (list 'time_point t))
                             [(list 'instantBefore t0 t1) (list 'instantBefore t1 t15)
                              (list 'instantBefore t15 t2) (list 'instantBefore t2 t3)
                              (list 'initially draft)
                              (list 'causal_event Promote) (list 'causal_event Demote)
                              (list 'happens Promote t1)
                              (list 'initiates Promote ready t1)
                              (list 'terminates Promote draft t1)
                              (list 'happens Demote t2)
                              (list 'initiates Demote draft t2)
                              (list 'terminates Demote ready t2)]))]
      (testing "draft before the promotion, ready between the two events"
        (is (holds-at? kb ctx draft t0))
        (is (not (holds-at? kb ctx ready t0)))
        (is (holds-at? kb ctx ready t15))
        (is (not (holds-at? kb ctx draft t15))))
      (testing "draft again after the demotion, and no longer ready"
        (is (holds-at? kb ctx draft t3))
        (is (not (holds-at? kb ctx ready t3))))
      (testing "at the instant of an event the old state still holds and the new one does not"
        (is (holds-at? kb ctx draft t1))
        (is (not (holds-at? kb ctx ready t1)))
        (is (holds-at? kb ctx ready t2))
        (is (not (holds-at? kb ctx draft t2))))
      (testing "the derived reasons are stored: ready was clipped between the second and fifth moments"
        (is (seq (v/sentexes-matching kb (list 'clipped t1 ready t3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clippedBefore draft t15) ctx)))))))

(tu/deftest-kb ^:red a-state-in-a-narrative-placed-by-genlmonad-goes-draft-ready-draft
  ;; The genlMonad twin of a-state-that-goes-draft-ready-draft-follows-both-transitions:
  ;; the narrative sits under CxChange by a stated genlMonad, so it reads the event
  ;; calculus through its monad.
  (tu/with-terms [DraftFn ReadyFn Doc Promote Demote T0 T1 T15 T2 T3]
    (let [draft (list DraftFn Doc)
          ready (list ReadyFn Doc)
          ctx   (narrative-under-genlmonad!
                 kb
                 (concat
                  [(list 'result DraftFn 'fluent) (list 'result ReadyFn 'fluent)]
                  (for [t [T0 T1 T15 T2 T3]] (list 'time_point t))
                  [(list 'instantBefore T0 T1) (list 'instantBefore T1 T15)
                   (list 'instantBefore T15 T2) (list 'instantBefore T2 T3)
                   (list 'initially draft)
                   (list 'causal_event Promote) (list 'causal_event Demote)
                   (list 'happens Promote T1)
                   (list 'initiates Promote ready T1)
                   (list 'terminates Promote draft T1)
                   (list 'happens Demote T2)
                   (list 'initiates Demote draft T2)
                   (list 'terminates Demote ready T2)]))]
      (testing "draft before the promotion, ready between the two events"
        (is (holds-at? kb ctx draft T0))
        (is (not (holds-at? kb ctx ready T0)))
        (is (holds-at? kb ctx ready T15))
        (is (not (holds-at? kb ctx draft T15))))
      (testing "draft again after the demotion, and no longer ready"
        (is (holds-at? kb ctx draft T3))
        (is (not (holds-at? kb ctx ready T3))))
      (testing "at the instant of an event the old state still holds and the new one does not"
        (is (holds-at? kb ctx draft T1))
        (is (not (holds-at? kb ctx ready T1)))
        (is (holds-at? kb ctx ready T2))
        (is (not (holds-at? kb ctx draft T2))))
      (testing "the derived reasons are stored: ready was clipped between T1 and T3"
        (is (seq (v/sentexes-matching kb (list 'clipped T1 ready T3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clippedBefore draft T15) ctx)))))))

(defn- equality-narrative
  "A fluent started at T1 and stopped at T2, where T2 is ordered before T3 only through
  an `instantEqual`: T1 < T2, T2 = T2b, T2b < T3.  Returns `[ctx fluent T1 T3]`."
  [kb StateFn Thing Start Stop T1 T2 T2b T3]
  (let [f (list StateFn Thing)]
    [(narrative! kb
                 (concat
                  [(list 'result StateFn 'fluent)]
                  (for [t [T1 T2 T2b T3]] (list 'time_point t))
                  [(list 'instantBefore T1 T2) (list 'instantEqual T2 T2b)
                   (list 'instantBefore T2b T3)
                   (list 'causal_event Start) (list 'causal_event Stop)
                   (list 'happens Start T1) (list 'initiates Start f T1)
                   (list 'happens Stop T2) (list 'terminates Stop f T2)]))
     f T1 T3]))

(defn- equality-narrative-under-genlmonad
  "`equality-narrative`, in a context placed below CxChange by genlMonad."
  [kb StateFn Thing Start Stop T1 T2 T2b T3]
  (let [f (list StateFn Thing)]
    [(narrative-under-genlmonad!
      kb
      (concat
       [(list 'result StateFn 'fluent)]
       (for [t [T1 T2 T2b T3]] (list 'time_point t))
       [(list 'instantBefore T1 T2) (list 'instantEqual T2 T2b)
        (list 'instantBefore T2b T3)
        (list 'causal_event Start) (list 'causal_event Stop)
        (list 'happens Start T1) (list 'initiates Start f T1)
        (list 'happens Stop T2) (list 'terminates Stop f T2)]))
     f T1 T3]))

(tu/deftest-kb clipped-reads-an-order-the-point-prover-entails-once-it-is-registered
  ;; docs/time.md ("What clipped can see") and CxChange.txt say an ordering only the
  ;; point calculus entails is not an edge and is not read by clipped.  With :point
  ;; registered it is: the forward join's instantBefore antecedent is answered by the
  ;; point prover, which carries support, so clipped fires through an instantEqual.
  (tu/with-terms [StateFn Thing Start Stop T1 T2 T2b T3]
    (let [[ctx f t1 t3] (equality-narrative kb StateFn Thing Start Stop T1 T2 T2b T3)]
      (testing "without :point, T1 is not ordered before T3, so neither clipped nor inertia reaches T3"
        (is (not (v/ask? kb (list 'instantBefore t1 t3) ctx)))
        (is (empty? (v/sentexes-matching kb (list 'clipped '?a f '?b) ctx)))
        (is (not (holds-at? kb ctx f t3))))))
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Thing Start Stop T1 T2 T2b T3]
    (let [[ctx f t1 t3] (equality-narrative kb StateFn Thing Start Stop T1 T2 T2b T3)]
      (testing "with :point, T1 is before T3 through the equality, clipped fires, and inertia stops"
        (is (true? (v/ask? kb (list 'instantBefore t1 t3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clipped t1 f t3) ctx)))
        (is (not (holds-at? kb ctx f t3)))))))

(tu/deftest-kb ^:red clipped-reads-an-entailed-order-in-a-narrative-placed-by-genlmonad
  ;; The genlMonad twin of clipped-reads-an-order-the-point-prover-entails-once-it-is-registered.
  (tu/with-terms [StateFn Thing Start Stop T1 T2 T2b T3]
    (let [[ctx f t1 t3] (equality-narrative-under-genlmonad kb StateFn Thing Start Stop T1 T2 T2b T3)]
      (testing "without :point, T1 is not ordered before T3, so neither clipped nor inertia reaches T3"
        (is (not (v/ask? kb (list 'instantBefore t1 t3) ctx)))
        (is (empty? (v/sentexes-matching kb (list 'clipped '?a f '?b) ctx)))
        (is (not (holds-at? kb ctx f t3))))))
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Thing Start Stop T1 T2 T2b T3]
    (let [[ctx f t1 t3] (equality-narrative-under-genlmonad kb StateFn Thing Start Stop T1 T2 T2b T3)]
      (testing "with :point, T1 is before T3 through the equality, clipped fires, and inertia stops"
        (is (true? (v/ask? kb (list 'instantBefore t1 t3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clipped t1 f t3) ctx)))
        (is (not (holds-at? kb ctx f t3)))))))

;; =========================================================================
;; Opt-in provers — the calendar clock and the instant-inclusion reader
;; =========================================================================
;; The interval, point, metric and duration provers each already have a test asking the
;; same question through the default registry and the registered prover; see the matrix.
;; The calendar clock and includesInstant did not.

(tu/deftest-kb the-calendar-clock-is-opt-in
  (testing "without :calendar a year has no computed start and 1999 does not meet 2000"
    (is (empty? (v/ask kb '(startOf (YearFn 2000) ?i) U)))
    (is (not (v/ask? kb '(meets (YearFn 1999) (YearFn 2000)) U))))
  (v/add-reasoner kb :calendar)
  (testing "with it, the same goals answer from the fields"
    (is (= [{'?i '(InstantFn 2000 1 1 0 0 0)}] (v/ask kb '(startOf (YearFn 2000) ?i) U)))
    (is (true? (v/ask? kb '(meets (YearFn 1999) (YearFn 2000)) U)))))

(tu/deftest-kb the-calendar-clock-is-opt-in-for-moments
  ;; The point twin of the-calendar-clock-is-opt-in: two InstantFn moments in place of two
  ;; years.
  (testing "without :calendar two moments a year apart are not ordered"
    (is (not (v/ask? kb '(instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 6 1 0 0 0)) U))))
  (v/add-reasoner kb :calendar)
  (testing "with it, the same goal answers from the fields"
    (is (true? (v/ask? kb '(instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 6 1 0 0 0)) U)))))

(tu/deftest-kb the-instant-inclusion-reader-is-opt-in
  (tu/with-terms [Party Noon Dusk]
    (doseq [s [(list 'instantBefore (list 'StartFn Party) Noon)
               (list 'instantBefore Noon (list 'EndFn Party))
               (list 'instantBefore (list 'EndFn Party) Dusk)]]
      (v/assert kb s U))
    (v/add-reasoner kb :point)
    (testing "with only :point, a moment inside a party's bounds is unknown"
      (is (= :unknown (verdict kb (list 'includesInstant Party Noon) U))))
    (v/add-reasoner kb :includes-instant)
    (testing "with :includes-instant, it is inside, and a moment after the end is not"
      (is (= :true (verdict kb (list 'includesInstant Party Noon) U)))
      (is (= :false (verdict kb (list 'includesInstant Party Dusk) U))))))

(tu/deftest-kb the-instant-inclusion-reader-is-opt-in-for-calendar-terms
  ;; The calendar twin of the-instant-inclusion-reader-is-opt-in: the party is a calendar
  ;; day and the two moments InstantFn moments, so the calendar places them and nothing is
  ;; stated.
  (let [day  '(DayFn 2000 1 1)
        noon '(InstantFn 2000 1 1 12 0 0)
        dusk '(InstantFn 2000 1 2 18 0 0)]
    (v/add-reasoner kb :point :calendar)
    (testing "with only :point and :calendar, a moment inside the day is unknown"
      (is (= :unknown (verdict kb (list 'includesInstant day noon) U))))
    (v/add-reasoner kb :includes-instant)
    (testing "with :includes-instant, it is inside, and a moment after the day's end is not"
      (is (= :true (verdict kb (list 'includesInstant day noon) U)))
      (is (= :false (verdict kb (list 'includesInstant day dusk) U))))))

;; =========================================================================
;; What the docs list as not reached, and ought to be
;; =========================================================================

(tu/deftest-kb ^:red a-stated-allen-relation-constrains-the-points
  ;; docs/time.md, "What it does not do": today the narrowing runs from points to
  ;; intervals only.  (before A B) means A ends before B starts.
  (v/add-reasoner kb :allen :point)
  (tu/with-terms [A B]
    (v/assert kb (list 'before A B) U)
    (is (true? (v/ask? kb (list 'before A B) U)))
    (testing "A's end is before B's start, from (before A B)"
      (is (true? (v/ask? kb (list 'instantBefore (list 'EndFn A) (list 'StartFn B)) U))))))

(tu/deftest-kb a-stated-allen-relation-between-calendar-terms-constrains-their-points
  ;; The calendar twin of a-stated-allen-relation-constrains-the-points: the two intervals
  ;; are January and March 2000, and the relation the original states is stated between
  ;; them.  Green today, and not because the stated relation narrows the points: the
  ;; instant network orders the calendar moments a goal mentions by their fields
  ;; (vaelii.impl.timepoint), so the end of January falls before the start of March with
  ;; or without it.  Two named intervals have no such moments, which is the original's
  ;; failure.
  (v/add-reasoner kb :allen :point :calendar)
  (let [jan '(MonthFn 2000 1)
        mar '(MonthFn 2000 3)]
    (v/assert kb (list 'before jan mar) U)
    (is (true? (v/ask? kb (list 'before jan mar) U)))
    (testing "January's end is before March's start, from (before January March)"
      (is (true? (v/ask? kb (list 'instantBefore (list 'EndFn jan) (list 'StartFn mar)) U))))))

(tu/deftest-kb a-stated-point-order-constrains-the-intervals
  ;; The point twin of a-stated-allen-relation-constrains-the-points, which runs the other
  ;; way: the order between A's end and B's start is stated, and the Allen relation
  ;; follows.  docs/time.md names this direction as the one that works today.
  (v/add-reasoner kb :allen :point)
  (tu/with-terms [A B]
    (v/assert kb (list 'instantBefore (list 'EndFn A) (list 'StartFn B)) U)
    (is (true? (v/ask? kb (list 'instantBefore (list 'EndFn A) (list 'StartFn B)) U)))
    (testing "A is before B, from A's end before B's start"
      (is (true? (v/ask? kb (list 'before A B) U))))))

(tu/deftest-kb ^:red a-calendar-term-is-a-node-of-the-allen-network
  ;; docs/time.md: today the clock answers a pair and does not fold its relations into
  ;; the interval network, so a stated relation to one month does not compose with the
  ;; clock's relation between two months.
  (v/add-reasoner kb :allen :calendar)
  (tu/with-terms [Breakfast]
    (v/assert kb (list 'before Breakfast '(MonthFn 2000 1)) U)
    (testing "control: the clock orders the two months"
      (is (true? (v/ask? kb '(before (MonthFn 2000 1) (MonthFn 2000 3)) U))))
    (testing "a stated relation composes with a clock relation"
      (is (true? (v/ask? kb (list 'before Breakfast '(MonthFn 2000 3)) U))))))

(tu/deftest-kb a-stated-relation-composes-with-a-stated-relation-between-named-months
  ;; The reified twin of a-calendar-term-is-a-node-of-the-allen-network: the two months
  ;; are named, so the relation the clock computes between them is stated, and both
  ;; relations are nodes of the Allen network.  What the original asks of the clock this
  ;; asks of a stated fact, and it composes today.
  (v/add-reasoner kb :allen)
  (tu/with-terms [Breakfast Jan2000 Mar2000]
    (times! kb [Jan2000 Mar2000] [] ['before Jan2000 Mar2000])
    (v/assert kb (list 'before Breakfast Jan2000) U)
    (testing "control: the stated relation orders the two named months"
      (is (true? (v/ask? kb (list 'before Jan2000 Mar2000) U))))
    (testing "a stated relation composes with another stated relation"
      (is (true? (v/ask? kb (list 'before Breakfast Mar2000) U))))))

(tu/deftest-kb a-calendar-moment-is-a-node-of-the-point-network
  ;; The point twin of a-calendar-term-is-a-node-of-the-allen-network: a stated order
  ;; between a named moment and a calendar moment composes with the calendar order
  ;; between two calendar moments.  The instant network orders the calendar moments it
  ;; mentions by their fields (vaelii.impl.timepoint), so this passes where the interval
  ;; original fails.
  (v/add-reasoner kb :point :calendar)
  (tu/with-terms [Breakfast]
    (v/assert kb (list 'instantBefore Breakfast '(InstantFn 2000 1 1 0 0 0)) U)
    (testing "control: the clock orders the two calendar moments"
      (is (true? (v/ask? kb '(instantBefore (InstantFn 2000 1 1 0 0 0) (InstantFn 2000 3 1 0 0 0)) U))))
    (testing "a stated order composes with the calendar order"
      (is (true? (v/ask? kb (list 'instantBefore Breakfast '(InstantFn 2000 3 1 0 0 0)) U))))))

(tu/deftest-kb ^:red a-conjunction-that-binds-the-calendar-term-elsewhere-answers
  ;; docs/time.md: today the planner costs the `during` literal by stored facts, finds
  ;; none, runs it first with ?m open, and the clock refuses an open end.  The clock
  ;; refusing an open end is right (calendar_test.clj's
  ;; an-open-end-answers-nothing-rather-than-enumerating-the-calendar); running it first
  ;; is not.
  (v/add-reasoner kb :calendar)
  (tu/with-terms [holiday]
    (v/assert kb (list holiday '(MonthFn 2000 3)) U)
    (testing "control: the ground question answers"
      (is (true? (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) U))))
    (testing "the conjunction binds ?m from the stored fact and the clock answers the rest"
      (is (= [{'?m '(MonthFn 2000 3)}]
             (v/query kb [(list holiday '?m) '(during ?m (YearFn 2000))] U {:max-depth 1}))))))

(tu/deftest-kb a-conjunction-over-a-named-month-binds-it-from-the-stored-fact
  ;; The reified twin of a-conjunction-that-binds-the-calendar-term-elsewhere-answers: the
  ;; month and the year are named and their relation is stated, so no clock is asked and
  ;; the conjunction answers today.  The original's failure is the planner running the
  ;; clock first with ?m open; a named interval goes to no clock.
  (tu/with-terms [holiday Mar2000 Y2000]
    (times! kb [Mar2000 Y2000] [] ['during Mar2000 Y2000])
    (v/assert kb (list holiday Mar2000) U)
    (testing "control: the ground question answers"
      (is (true? (v/ask? kb (list 'during Mar2000 Y2000) U))))
    (testing "the conjunction binds ?m from the stored fact and answers the rest"
      (is (= [{'?m Mar2000}]
             (v/query kb [(list holiday '?m) (list 'during '?m Y2000)] U {:max-depth 1}))))))

(tu/deftest-kb ^:red a-conjunction-that-binds-the-calendar-moment-elsewhere-answers
  ;; The point twin of a-conjunction-that-binds-the-calendar-term-elsewhere-answers: the
  ;; stored fact names a moment, and the literal the clock answers orders it.
  (v/add-reasoner kb :calendar)
  (tu/with-terms [holiday]
    (v/assert kb (list holiday '(InstantFn 2000 3 1 12 0 0)) U)
    (testing "control: the ground question answers"
      (is (true? (v/ask? kb '(instantBefore (InstantFn 2000 3 1 12 0 0) (InstantFn 2001 1 1 0 0 0)) U))))
    (testing "the conjunction binds ?t from the stored fact and the clock answers the rest"
      (is (= [{'?t '(InstantFn 2000 3 1 12 0 0)}]
             (v/query kb [(list holiday '?t) '(instantBefore ?t (InstantFn 2001 1 1 0 0 0))] U {:max-depth 1}))))))

(tu/deftest-kb ^:red a-forward-rule-fires-on-a-clock-answer
  ;; docs/time.md: today a forward antecedent is answered through solve-computed, which
  ;; drops an answer with empty support, and the clock's support is empty by construction.
  (v/add-reasoner kb :calendar)
  (tu/with-terms [CxCal holiday holidayIn2000]
    (v/assert kb (list 'genlCx CxCal U) U)
    (v/assert kb (list holiday '(MonthFn 2000 3)) CxCal)
    (v/assert-rule kb [(list holiday '?m) '(subintervalOf ?m (YearFn 2000))]
                   (list holidayIn2000 '?m) CxCal {:direction :forward})
    (testing "a forward rule whose antecedent only the clock answers fires"
      (is (= [(list holidayIn2000 '(MonthFn 2000 3))]
             (map :sentence (v/sentexes-matching kb (list holidayIn2000 '?m) CxCal)))))))

(tu/deftest-kb a-forward-rule-fires-on-a-stated-subinterval
  ;; The reified twin of a-forward-rule-fires-on-a-clock-answer: the antecedent the clock
  ;; would answer is a stated subintervalOf between two named intervals, which carries
  ;; support, so the rule fires today.
  (tu/with-terms [CxCal holiday holidayIn2000 Mar2000 Y2000]
    (v/assert kb (list 'genlCx CxCal U) U)
    (times! kb [Mar2000 Y2000] [] ['subintervalOf Mar2000 Y2000])
    (v/assert kb (list holiday Mar2000) CxCal)
    (v/assert-rule kb [(list holiday '?m) (list 'subintervalOf '?m Y2000)]
                   (list holidayIn2000 '?m) CxCal {:direction :forward})
    (testing "a forward rule whose antecedent a stated fact answers fires"
      (is (= [(list holidayIn2000 Mar2000)]
             (map :sentence (v/sentexes-matching kb (list holidayIn2000 '?m) CxCal)))))))

(tu/deftest-kb ^:red a-forward-rule-fires-on-a-clock-answer-about-moments
  ;; The point twin of a-forward-rule-fires-on-a-clock-answer: the antecedent only the
  ;; clock answers orders two moments rather than nesting two intervals.
  (v/add-reasoner kb :calendar)
  (tu/with-terms [CxCal holiday holidayBefore2001]
    (v/assert kb (list 'genlCx CxCal U) U)
    (v/assert kb (list holiday '(InstantFn 2000 3 1 12 0 0)) CxCal)
    (v/assert-rule kb [(list holiday '?t) '(instantBefore ?t (InstantFn 2001 1 1 0 0 0))]
                   (list holidayBefore2001 '?t) CxCal {:direction :forward})
    (testing "a forward rule whose antecedent only the clock answers fires"
      (is (= [(list holidayBefore2001 '(InstantFn 2000 3 1 12 0 0))]
             (map :sentence (v/sentexes-matching kb (list holidayBefore2001 '?t) CxCal)))))))

(tu/deftest-kb ^:red metric-gap-and-length-for-calendar-terms
  ;; docs/time.md: today the metric prover's nodes are atomic terms, so an InstantFn moment
  ;; is not one, and nothing converts a field vector to a magnitude.  2000 is a leap year:
  ;; 366 days of 86400 seconds.
  (v/add-reasoner kb :calendar :metric-time :duration)
  (doseq [s ['(dimensionOf Second Duration) '(dimensionOf Hour Duration)
             '(conversionFactor Second Second 1) '(conversionFactor Hour Second 3600)]]
    (v/assert kb s U))
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) U)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) U)
    (testing "control: two stated gaps between named moments compose"
      (is (= [{'?d '(QuantityFn 7200 Second)}]
             (v/ask kb (list 'temporalDistance P R '?d) U)))))
  (testing "the gap between two computed moments an hour apart"
    (is (= [{'?d '(QuantityFn 3600 Second)}]
           (v/ask kb '(temporalDistance (InstantFn 2000 1 1 0 0 0)
                                        (InstantFn 2000 1 1 1 0 0) ?d) U))))
  (testing "the length of a calendar year"
    (is (= [{'?d '(QuantityFn 31622400 Second)}]
           (v/ask kb '(totalDuration (list (YearFn 2000)) ?d) U)))))

;; =========================================================================
;; Time zones
;; =========================================================================
;; Nothing in the time vocabulary names a zone or an offset.  `InstantFn` is six fields
;; read as a java.time LocalDateTime: a wall-clock moment in no zone.  `DatetimeFn`'s
;; reader (vaelii.impl.datetime) admits a date and up to three time fields, each one or
;; two digits, so an ISO string with an offset ("13:00-07:00") or a `Z` is not a time term
;; at all: it has no bounds, orders against nothing and keys a slice the producer cannot
;; read.  time.txt has no zone type and no zoned constructor, so a named zone and its
;; daylight-saving rules cannot be said.  The tests below ask for the classic cases:
;; one moment in two offsets, the offset form against `Z`, a day boundary that moves
;; with the offset, ordering across offsets, and a named zone's daylight-saving gap and
;; repeated hour.  `ZonedDatetimeFn` (a local ISO string and an IANA zone name) and
;; `timezone` (the zone type) are the ruled names for this vocabulary; time.txt does not
;; ship it yet.

(tu/deftest-kb ^:red one-moment-written-in-two-offsets-is-one-moment
  ;; 13:00 at UTC-07:00 and 01:30 the next day at UTC+05:30 are both 20:00 UTC.  The same
  ;; wall-clock time at two offsets is two moments.  The control is the zoneless
  ;; spelling, which the calendar already places.
  (v/add-reasoner kb :point :calendar)
  (testing "control: a zoneless minute's start is the InstantFn moment of the same fields"
    (is (true? (v/ask? kb '(instantEqual (StartFn (DatetimeFn "2000-01-15T20:00")) (InstantFn 2000 1 15 20 0 0)) U))))
  (testing "13:00-07:00 and 01:30+05:30 the next day start at one moment and are one interval"
    (is (true? (v/ask? kb '(instantEqual (StartFn (DatetimeFn "2000-01-15T13:00-07:00"))
                                         (StartFn (DatetimeFn "2000-01-16T01:30+05:30"))) U)))
    (is (true? (v/ask? kb '(intervalEqual (DatetimeFn "2000-01-15T13:00-07:00")
                                          (DatetimeFn "2000-01-16T01:30+05:30")) U))))
  (testing "and 13:00 at two offsets is two moments"
    (is (= :false (verdict kb '(instantEqual (StartFn (DatetimeFn "2000-01-15T13:00-07:00"))
                                             (StartFn (DatetimeFn "2000-01-15T13:00+05:30"))) U)))))

(tu/deftest-kb ^:red the-iso-offset-form-and-the-z-form-name-one-moment
  ;; ISO 8601's two spellings of an absolute moment: …T13:00-07:00 is …T20:00Z, and +00:00
  ;; is Z.
  (v/add-reasoner kb :point :calendar)
  (testing "13:00-07:00 is 20:00Z"
    (is (true? (v/ask? kb '(intervalEqual (DatetimeFn "2000-01-15T13:00-07:00")
                                          (DatetimeFn "2000-01-15T20:00Z")) U))))
  (testing "20:00+00:00 is 20:00Z"
    (is (true? (v/ask? kb '(intervalEqual (DatetimeFn "2000-01-15T20:00+00:00")
                                          (DatetimeFn "2000-01-15T20:00Z")) U))))
  (testing "and 13:00Z is not 13:00-07:00"
    (is (= :false (verdict kb '(intervalEqual (DatetimeFn "2000-01-15T13:00Z")
                                              (DatetimeFn "2000-01-15T13:00-07:00")) U)))))

(tu/deftest-kb ^:red the-day-a-moment-falls-on-depends-on-the-offset
  ;; 21:00 on 31 December 1999 at UTC-08:00 is 05:00 on 1 January 2000 UTC: one hour, on
  ;; the last day of 1999 at one offset and the first day of 2000 at the other.  A day at
  ;; an offset is written as the range of its first and last hours there.  A zoneless
  ;; date names a wall-clock day in no zone, so where an absolute moment falls against it
  ;; is unknown rather than read as UTC.
  (v/add-reasoner kb :point :calendar)
  (let [hour      '(DatetimeFn "1999-12-31T21-08:00")
        utc-jan1  '(DatetimeRangeFn "2000-01-01T00Z" "2000-01-01T23Z")
        utc-dec31 '(DatetimeRangeFn "1999-12-31T00Z" "1999-12-31T23Z")
        pst-dec31 '(DatetimeRangeFn "1999-12-31T00-08:00" "1999-12-31T23-08:00")]
    (testing "the hour is 05:00 UTC on 1 January"
      (is (true? (v/ask? kb (list 'intervalEqual hour '(DatetimeFn "2000-01-01T05Z")) U))))
    (testing "it falls on 1 January in UTC and on 31 December at UTC-08:00"
      (is (true? (v/ask? kb (list 'subintervalOf hour utc-jan1) U)))
      (is (true? (v/ask? kb (list 'subintervalOf hour pst-dec31) U))))
    (testing "and not on 31 December in UTC"
      (is (= :false (verdict kb (list 'subintervalOf hour utc-dec31) U))))
    (testing "against a zoneless 1 January it is unknown, not read as UTC"
      (is (= :unknown (verdict kb (list 'subintervalOf hour '(DatetimeFn "2000-01-01")) U))))))

(tu/deftest-kb ^:red moments-at-different-offsets-are-ordered-by-the-moment-not-the-wall-clock
  ;; 13:00 at UTC+01:00 is 12:00 UTC, so it is before 12:30 UTC though its wall-clock
  ;; reading is later.
  (v/add-reasoner kb :allen :point :calendar)
  (let [paris  '(DatetimeFn "2000-01-15T13:00+01:00")
        london '(DatetimeFn "2000-01-15T12:30Z")]
    (testing "13:00+01:00 is before 12:30Z"
      (is (true? (v/ask? kb (list 'before paris london) U)))
      (is (true? (v/ask? kb (list 'instantBefore (list 'StartFn paris) (list 'StartFn london)) U))))
    (testing "and not after it, as the wall-clock reading would have it"
      (is (= :false (verdict kb (list 'after paris london) U))))))

(tu/deftest-kb ^:red the-kb-declares-a-named-time-zone-and-a-zoned-local-time
  ;; A UTC offset fixes a moment; a named zone (Europe/London) fixes an offset only per
  ;; date, through its daylight-saving rules, and time.txt has no way to say one.  The
  ;; two tests after this one need it.
  (testing "a type for a named time zone, and a constructor of a local time in one"
    (is (true? (v/ask? kb '(arg ZonedDatetimeFn 2 timezone) U)))
    (is (true? (v/ask? kb '(result ZonedDatetimeFn time_interval) U)))))

(tu/deftest-kb ^:red a-local-time-a-daylight-saving-gap-skips-names-no-moment
  ;; On 26 March 2000 London's clocks went from 01:00 GMT to 02:00 BST, so 01:30 that
  ;; night never happened there.  00:30 is 00:30 UTC and 02:30 is 01:30 UTC; 01:30 names
  ;; no moment, rather than being moved silently to either side of the gap.  This is the
  ;; ideal behaviour, and an implementation may defer the gap as an edge case.
  (v/add-reasoner kb :point :calendar)
  (let [at (fn [local] (list 'ZonedDatetimeFn local "Europe/London"))]
    (testing "the times either side of the gap are the moments their offsets give"
      (is (true? (v/ask? kb (list 'intervalEqual (at "2000-03-26T00:30") '(DatetimeFn "2000-03-26T00:30Z")) U)))
      (is (true? (v/ask? kb (list 'intervalEqual (at "2000-03-26T02:30") '(DatetimeFn "2000-03-26T01:30Z")) U))))
    (testing "and the time in the gap has no start"
      (is (empty? (v/query kb (list 'startOf (at "2000-03-26T01:30") '?i) U {:max-depth 3}))))))

(tu/deftest-kb ^:red a-local-time-a-daylight-saving-change-repeats-is-ambiguous-until-its-offset-is-given
  ;; On 29 October 2000 London's clocks went from 02:00 BST back to 01:00 GMT, so 01:30
  ;; happened twice: at 00:30 UTC and at 01:30 UTC.  Without an offset which one is meant
  ;; is unknown, and neither is picked silently; the offset form resolves it.  This is
  ;; the ideal behaviour, and an implementation may defer the repeated hour as an edge
  ;; case.
  (v/add-reasoner kb :point :calendar)
  (let [repeated '(ZonedDatetimeFn "2000-10-29T01:30" "Europe/London")]
    (testing "the zoned local time is neither occurrence, as far as the KB knows"
      (is (= :unknown (verdict kb (list 'intervalEqual repeated '(DatetimeFn "2000-10-29T00:30Z")) U)))
      (is (= :unknown (verdict kb (list 'intervalEqual repeated '(DatetimeFn "2000-10-29T01:30Z")) U))))
    (testing "the offset form names one occurrence each"
      (is (true? (v/ask? kb '(intervalEqual (DatetimeFn "2000-10-29T01:30+01:00") (DatetimeFn "2000-10-29T00:30Z")) U)))
      (is (true? (v/ask? kb '(intervalEqual (DatetimeFn "2000-10-29T01:30+00:00") (DatetimeFn "2000-10-29T01:30Z")) U))))))

;; =========================================================================
;; Resolution — the shortest time a term can name
;; =========================================================================
;; The finest calendar term is one second: DatetimeFn admits at most three time fields,
;; each one or two digits, and InstantFn is six integer fields ending in the second.  So
;; the shortest interval a calendar term names is (DatetimeFn "…Thh:mm:ss"), one second
;; long, and two moments a calendar term can tell apart are at least a second apart.  A
;; named interval with stated bounds can be shorter only by bounds the metric layer
;; states, which no calendar term reads.  The first test below asserts that one second is
;; the finest unit, and the red tests after it ask for the millisecond and the microsecond.

(tu/deftest-kb the-shortest-calendar-interval-is-one-second
  ;; One second is the finest resolution today; the red tests after this one ask for finer.
  (v/add-reasoner kb :calendar)
  (testing "a DatetimeFn to the second begins at that second and ends at the next"
    (is (= [{'?i '(InstantFn 2000 1 15 13 0 0)}] (v/ask kb '(startOf (DatetimeFn "2000-01-15T13:00:00") ?i) U)))
    (is (= [{'?i '(InstantFn 2000 1 15 13 0 1)}] (v/ask kb '(endOf (DatetimeFn "2000-01-15T13:00:00") ?i) U))))
  (testing "a string with a fraction of a second names no interval the clock reads"
    (is (empty? (v/ask kb '(startOf (DatetimeFn "2000-01-15T13:00:00.123") ?i) U))))
  (testing "and an InstantFn with a seventh field or a fractional second is no moment the clock orders"
    (is (not (v/ask? kb '(instantBefore (InstantFn 2000 1 15 13 0 0) (InstantFn 2000 1 15 13 0 0 500)) U)))
    (is (not (v/ask? kb '(instantBefore (InstantFn 2000 1 15 13 0 0) (InstantFn 2000 1 15 13 0 0.5)) U)))))

(tu/deftest-kb ^:red a-millisecond-is-an-interval-inside-its-second
  ;; "2000-01-15T13:00:00.123" names one millisecond, inside the second 13:00:00 and not
  ;; the next, and a slice keyed by it sees a slice keyed by its second.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (let [ms  '(DatetimeFn "2000-01-15T13:00:00.123")
        sec '(DatetimeFn "2000-01-15T13:00:00")]
    (testing "control: a second is inside its minute"
      (is (true? (v/ask? kb (list 'subintervalOf sec '(DatetimeFn "2000-01-15T13:00")) U))))
    (testing "the millisecond is inside its second and not the next"
      (is (true? (v/ask? kb (list 'subintervalOf ms sec) U)))
      (is (not (v/ask? kb (list 'subintervalOf ms '(DatetimeFn "2000-01-15T13:00:01")) U))))
    (testing "and it is one millisecond long"
      (is (true? (v/ask? kb (list 'meets ms '(DatetimeFn "2000-01-15T13:00:00.124")) U))))
    (tu/with-terms [p q]
      (v/assert kb (list p) (slice sec))
      (v/assert kb (list q) (slice ms))
      (testing "a fact in the second's slice is visible from the millisecond's"
        (is (true? (v/ask? kb (list p) (slice ms))))))))

(tu/deftest-kb ^:red two-moments-a-millisecond-apart-are-ordered
  ;; The starts of two consecutive milliseconds are two moments, the first before the
  ;; second.
  (v/add-reasoner kb :point :calendar)
  (testing "control: the starts of two consecutive seconds are ordered"
    (is (true? (v/ask? kb '(instantBefore (StartFn (DatetimeFn "2000-01-15T13:00:00"))
                                          (StartFn (DatetimeFn "2000-01-15T13:00:01"))) U))))
  (testing "the starts of two consecutive milliseconds are ordered, and are not one moment"
    (is (true? (v/ask? kb '(instantBefore (StartFn (DatetimeFn "2000-01-15T13:00:00.123"))
                                          (StartFn (DatetimeFn "2000-01-15T13:00:00.124"))) U)))
    (is (= :false (verdict kb '(instantEqual (StartFn (DatetimeFn "2000-01-15T13:00:00.123"))
                                             (StartFn (DatetimeFn "2000-01-15T13:00:00.124"))) U)))))

(tu/deftest-kb ^:red a-microsecond-is-an-interval-inside-its-millisecond
  ;; "2000-01-15T13:00:00.123456" names one microsecond, inside the millisecond .123 and
  ;; so inside the second.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar)
  (let [us '(DatetimeFn "2000-01-15T13:00:00.123456")
        ms '(DatetimeFn "2000-01-15T13:00:00.123")]
    (testing "the microsecond is inside its millisecond and its second, and not the next millisecond"
      (is (true? (v/ask? kb (list 'subintervalOf us ms) U)))
      (is (true? (v/ask? kb (list 'subintervalOf us '(DatetimeFn "2000-01-15T13:00:00")) U)))
      (is (not (v/ask? kb (list 'subintervalOf us '(DatetimeFn "2000-01-15T13:00:00.124")) U))))
    (testing "and it is one microsecond long"
      (is (true? (v/ask? kb (list 'meets us '(DatetimeFn "2000-01-15T13:00:00.123457")) U))))
    (tu/with-terms [p]
      (v/assert kb (list p) (slice ms))
      (testing "a fact in the millisecond's slice is visible from the microsecond's"
        (is (true? (v/ask? kb (list p) (slice us))))))))

(tu/deftest-kb ^:red two-moments-a-microsecond-apart-are-ordered
  ;; The starts of two consecutive microseconds are two moments, the first before the
  ;; second.
  (v/add-reasoner kb :point :calendar)
  (testing "the starts of two consecutive microseconds are ordered, and are not one moment"
    (is (true? (v/ask? kb '(instantBefore (StartFn (DatetimeFn "2000-01-15T13:00:00.123456"))
                                          (StartFn (DatetimeFn "2000-01-15T13:00:00.123457"))) U)))
    (is (= :false (verdict kb '(instantEqual (StartFn (DatetimeFn "2000-01-15T13:00:00.123456"))
                                             (StartFn (DatetimeFn "2000-01-15T13:00:00.123457"))) U)))))