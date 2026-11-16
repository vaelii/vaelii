;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.correspondence-functionality-test
  "A function's corresponding predicate is functional at the value position.
  (functionCorrespondingPredicate F P N) concludes (functionalInArg P N): F maps its
  arguments to at most one value, so P holds of those arguments with at most one thing
  at N."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)
(def ^:private mono {:strength :monotonic})

(tu/deftest-kb a-correspondence-makes-its-predicate-functional-at-the-value-position
  (testing "a ternary correspondence, value last"
    (tu/with-terms [HiveCellFn hiveCellOf]
      (v/assert kb (list 'binary_function HiveCellFn) U mono)
      (v/assert kb (list 'ternary_predicate hiveCellOf) U mono)
      (v/assert kb (list 'functionCorrespondingPredicate HiveCellFn hiveCellOf 3) U mono)
      (is (true? (v/ask? kb (list 'functionalInArg hiveCellOf 3) U)))
      (is (not (v/ask? kb (list 'functionalInArg hiveCellOf 1) U)))))
  (testing "a binary correspondence, through the ternary it concludes"
    (tu/with-terms [HiveQueenFn hiveQueenOf]
      (v/assert kb (list 'unary_function HiveQueenFn) U mono)
      (v/assert kb (list 'binary_predicate hiveQueenOf) U mono)
      (v/assert kb (list 'functionCorrespondingBinaryPredicate HiveQueenFn hiveQueenOf) U mono)
      (is (true? (v/ask? kb (list 'functionalInArg hiveQueenOf 2) U)))))
  (testing "a correspondence the upper ontology ships"
    (doseq [[predicate position] '[[startOf 2] [endOf 2] [calendarYear 2] [listOf 1]
                                   [measureInUnit 3] [calendarInstant 7]]]
      (is (true? (v/ask? kb (list 'functionalInArg predicate position) U))
          (str predicate " at " position)))))

(tu/deftest-kb two-values-of-a-corresponding-predicate-name-one-thing
  (tu/with-terms [HiveQueenFn hiveQueenOf Hive Queen Regent]
    (v/assert kb (list 'unary_function HiveQueenFn) U mono)
    (v/assert kb (list 'binary_predicate hiveQueenOf) U mono)
    (v/assert kb (list 'functionCorrespondingBinaryPredicate HiveQueenFn hiveQueenOf) U mono)
    (v/assert kb (list hiveQueenOf Hive Queen) U mono)
    (v/assert kb (list hiveQueenOf Hive Regent) U mono)
    (is (v/same-class? kb Queen Regent))))

(tu/deftest-kb motherhood-and-fatherhood-are-not-functional
  (doseq [predicate '[motherOf fatherOf]]
    (testing (str predicate)
      (is (not (v/ask? kb (list 'functionalInArg predicate 2) U)))
      (is (not (v/ask? kb (list 'functional predicate) U)))
      (is (true? (v/ask? kb (list 'not (list 'functional predicate)) U)))
      (is (empty? (v/ask kb (list 'functionCorrespondingPredicate '?function predicate '?position) U))
          "no function corresponds to it")
      (is (empty? (v/ask kb (list 'functionCorrespondingPredicate '?function
                                  (list 'GeneticKinFn predicate) '?position) U))
          "no function corresponds to its genetic reading")
      (is (not (v/ask? kb (list 'functionalInArg (list 'GeneticKinFn predicate) 2) U))))))
