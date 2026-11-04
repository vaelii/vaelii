;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.datetime-test
  "Calendar containment — docs/context-nat.md.  A reduced-precision ISO string denotes an
  interval, and so does a calendar term `(YearFn 2000)` / `(MonthFn 2000 1)` / `(DayFn 2000
  1 15)`; a finer interval is inside a coarser one it shares every field with, whichever
  of the two spellings each was written in.  Pure and total: `subinterval?` answers any two
  forms and declines whatever is not a time term."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.datetime :as dt]))

(defn- dtf [s] (list 'DatetimeFn s))

(deftest datetime-term-recognition
  (is (dt/datetime-term? (dtf "2000")))
  (is (dt/datetime-term? (dtf "2000-01-15T13:30:00")))
  (testing "not a datetime term"
    (is (not (dt/datetime-term? (dtf "not-a-date"))))
    (is (not (dt/datetime-term? '(QuantityFn 5 Meter))))
    (is (not (dt/datetime-term? (dtf "2000-13-xx"))))
    (is (not (dt/datetime-term? 'Foo)))))

(deftest malformed-shapes-are-not-datetime-terms
  (testing "a time part needs a full date in front of it"
    (is (not (dt/datetime-term? (dtf "2000T13:00"))))
    (is (not (dt/datetime-term? (dtf "2000-01T13"))))
    (is (not (dt/datetime-term? (dtf "T13")))))
  (testing "the date and time halves are each bounded at three fields"
    (is (not (dt/datetime-term? (dtf "2000-01-15-12"))))
    (is (not (dt/datetime-term? (dtf "2000-01-15T13:30:00:00"))))
    (is (dt/datetime-term? (dtf "2000-01-15T13:30:00"))))
  (testing "an empty field is not a field"
    (is (not (dt/datetime-term? (dtf "2000-"))))
    (is (not (dt/datetime-term? (dtf "2000-01-15T"))))
    (is (not (dt/datetime-term? (dtf "")))))
  (testing "fields after the year are range-checked"
    (is (not (dt/datetime-term? (dtf "2000-13"))))
    (is (not (dt/datetime-term? (dtf "2000-00"))))
    (is (not (dt/datetime-term? (dtf "2000-01-32"))))
    (is (not (dt/datetime-term? (dtf "2000-01-15T24"))))
    (is (not (dt/datetime-term? (dtf "2000-01-15T13:60"))))
    (is (not (dt/datetime-term? (dtf "2000-01-15T13:30:60"))))
    (is (dt/datetime-term? (dtf "2000-12-31T23:59:59"))))
  (testing "so a mis-shaped pair nests nothing"
    (is (not (dt/subinterval? (dtf "2000T13:00") (dtf "2000-13"))))
    (is (not (dt/subinterval? (dtf "2000-01-15-12") (dtf "2000-01-15"))))))

(deftest every-field-is-bounded-by-its-own-width
  ;; The parse runs inside the structural `genlCx` producer, in the settle/relabel loop,
  ;; where nothing may throw.  A field wider than its own width is what would make it:
  ;; the read of an unbounded run of digits overflows before any range check is reached.
  ;; So the widths are the refusal, and every rejection here is a nil rather than a throw.
  (testing "a year wider than four digits is refused, not read"
    (is (not (dt/datetime-term? (dtf "99999"))))
    (is (not (dt/datetime-term? (dtf "99999999999999999999"))))
    (is (not (dt/subinterval? (dtf "99999999999999999999-01") (dtf "99999999999999999999")))
        "and the pair declines rather than throwing on either side"))
  (testing "and so is a later field, which the range check alone could not survive"
    (is (not (dt/datetime-term? (dtf "2000-001"))))
    (is (not (dt/datetime-term? (dtf "2000-99999999999999999999"))))
    (is (not (dt/datetime-term? (dtf "2000-01-15T99999999999999999999")))))
  (testing "the four-digit year itself still parses, padded or not"
    (is (dt/datetime-term? (dtf "2000")))
    (is (dt/datetime-term? (dtf "0001")))
    (is (dt/datetime-term? (dtf "999")))))

(deftest the-basic-iso-format-is-refused-rather-than-misread
  ;; `"20260821"` is ISO 8601's *basic* format for the 21st of August 2026.  Read as an
  ;; extended-format year it is the year 20,260,821 — a term that looks like a day, nests
  ;; under nothing anyone wrote, and silently names a different interval from
  ;; `"2026-08-21"`.  This namespace reads the extended format alone, so the basic one is
  ;; refused; the year's width is what refuses it.
  (is (not (dt/datetime-term? (dtf "20260821"))))
  (is (not (dt/datetime-term? (dtf "202608"))))
  (is (not (dt/subinterval? (dtf "20260821") (dtf "2026")))
      "so it nests under nothing, rather than nesting somewhere unrelated")
  (testing "the extended spelling of the same day is the one that reads"
    (is (dt/datetime-term? (dtf "2026-08-21")))
    (is (dt/subinterval? (dtf "2026-08-21") (dtf "2026")))))

(deftest containment-nests-by-field
  (testing "a finer interval is inside a coarser one it shares fields with"
    (is (dt/subinterval? (dtf "2000-01") (dtf "2000")))
    (is (dt/subinterval? (dtf "2000-01-15") (dtf "2000-01")))
    (is (dt/subinterval? (dtf "2000-01-15") (dtf "2000")))
    (is (dt/subinterval? (dtf "2000-01-15T13") (dtf "2000-01-15"))))
  (testing "reflexive"
    (is (dt/subinterval? (dtf "2000-01") (dtf "2000-01"))))
  (testing "field values are numeric, so zero-padding does not matter"
    (is (dt/subinterval? (dtf "2000-1") (dtf "2000-01")))
    (is (dt/subinterval? (dtf "2000-01") (dtf "2000-1")))))

(deftest non-containment
  (testing "a coarser interval is not inside a finer one"
    (is (not (dt/subinterval? (dtf "2000") (dtf "2000-01")))))
  (testing "different fields never nest"
    (is (not (dt/subinterval? (dtf "2001") (dtf "2000"))))
    (is (not (dt/subinterval? (dtf "2000-02") (dtf "2000-01"))))
    (is (not (dt/subinterval? (dtf "2000-01-16") (dtf "2000-01-15")))))
  (testing "non-datetime terms decline rather than throw"
    (is (not (dt/subinterval? (dtf "2000") '(QuantityFn 5 Meter))))
    (is (not (dt/subinterval? 'Foo (dtf "2000"))))))

;; ---- the calendar constructors ------------------------------------------

(deftest calendar-term-recognition
  (testing "one integer field per argument, coarsest first"
    (is (dt/calendar-term? '(YearFn 2000)))
    (is (dt/calendar-term? '(MonthFn 2000 1)))
    (is (dt/calendar-term? '(DayFn 2000 1 15))))
  (testing "the arity IS the precision, so a wrong one names nothing"
    (is (not (dt/calendar-term? '(YearFn 2000 1))))
    (is (not (dt/calendar-term? '(MonthFn 2000))))
    (is (not (dt/calendar-term? '(DayFn 2000 1)))))
  (testing "the fields are numbers, not strings and not variables"
    (is (not (dt/calendar-term? '(YearFn "2000"))))
    (is (not (dt/calendar-term? '(MonthFn 2000 ?m))))
    (is (not (dt/calendar-term? 'Foo)))
    (is (not (dt/calendar-term? '(QuantityFn 5 Meter)))))
  (testing "and each is range-checked, the year by the width ISO gives it"
    (is (not (dt/calendar-term? '(MonthFn 2000 13))))
    (is (not (dt/calendar-term? '(MonthFn 2000 0))))
    (is (not (dt/calendar-term? '(DayFn 2000 1 32))))
    (is (not (dt/calendar-term? '(YearFn 20260821))))
    (is (dt/calendar-term? '(DayFn 2000 12 31))))
  (testing "a calendar term is not an ISO one, and neither claims the other"
    (is (not (dt/datetime-term? '(MonthFn 2000 1))))
    (is (not (dt/calendar-term? (dtf "2000"))))))

(deftest a-calendar-month-is-inside-its-year-and-not-beside-it
  ;; The containment a time-keyed context is ordered by: January 2000 is inside 2000, the
  ;; fifteenth is inside January, and February is inside neither January nor the fifteenth.
  (testing "finer sits inside coarser"
    (is (dt/subinterval? '(MonthFn 2000 1) '(YearFn 2000)))
    (is (dt/subinterval? '(DayFn 2000 1 15) '(MonthFn 2000 1)))
    (is (dt/subinterval? '(DayFn 2000 1 15) '(YearFn 2000))))
  (testing "reflexive, and never the other way"
    (is (dt/subinterval? '(MonthFn 2000 1) '(MonthFn 2000 1)))
    (is (not (dt/subinterval? '(YearFn 2000) '(MonthFn 2000 1)))))
  (testing "siblings nest neither way — which is what keeps January out of February"
    (is (not (dt/subinterval? '(MonthFn 2000 1) '(MonthFn 2000 2))))
    (is (not (dt/subinterval? '(MonthFn 2000 2) '(MonthFn 2000 1))))
    (is (not (dt/subinterval? '(YearFn 2001) '(YearFn 2000))))
    (is (not (dt/subinterval? '(DayFn 2000 1 15) '(MonthFn 2000 2))))))

(deftest the-two-spellings-name-the-same-intervals
  ;; A calendar term and the reduced-precision ISO string read to one field vector, so the
  ;; comparator never learns which constructor it was handed.
  (testing "each nests under the other's coarser interval"
    (is (dt/subinterval? '(MonthFn 2000 1) (dtf "2000")))
    (is (dt/subinterval? (dtf "2000-01") '(YearFn 2000)))
    (is (dt/subinterval? '(DayFn 2000 1 15) (dtf "2000-01")))
    (is (dt/subinterval? (dtf "2000-01-15") '(MonthFn 2000 1))))
  (testing "and the same interval written both ways contains itself both ways"
    (is (dt/subinterval? '(MonthFn 2000 1) (dtf "2000-01")))
    (is (dt/subinterval? (dtf "2000-01") '(MonthFn 2000 1))))
  (testing "a finer ISO field still nests under a calendar day"
    (is (dt/subinterval? (dtf "2000-01-15T13") '(DayFn 2000 1 15)))
    (is (not (dt/subinterval? '(DayFn 2000 1 15) (dtf "2000-01-15T13"))))))

(deftest a-zoned-term-that-starts-or-ends-on-a-clock-change-spans-the-instants-its-clock-reads
  (let [zoned (fn [local zone] (dt/utc-extent (list 'ZonedDatetimeFn local zone)))]
    (doseq [[local zone clock extent]
            [["2018-11-04" "America/Sao_Paulo" "00:00 skips to 01:00: 23 hours"
              [[2018 11 4 3 0 0] [2018 11 5 2 0 0]]]
             ["2019-02-16" "America/Sao_Paulo" "24:00 goes back to 23:00: 25 hours"
              [[2019 2 16 2 0 0] [2019 2 17 3 0 0]]]
             ["2018-11-05" "America/Sao_Paulo" "no change" [[2018 11 5 2 0 0] [2018 11 6 2 0 0]]]
             ["2000-03-26" "Europe/London" "01:00 skips to 02:00: 23 hours"
              [[2000 3 26 0 0 0] [2000 3 26 23 0 0]]]
             ["2000-03-26T01" "Europe/London" "the hour is skipped" nil]
             ["2000-03-26T01:30" "Europe/London" "the minute is skipped" nil]
             ["2000-10-29T01" "Europe/London" "the hour repeats" nil]
             ["2000-10-29T01:30" "Europe/London" "the minute repeats" nil]]]
      (is (= extent (zoned local zone)) (str local " " zone ", " clock)))))
