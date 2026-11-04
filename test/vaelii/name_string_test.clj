;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.name-string-test
  "`nameString` in CxTra: a thing's name as a string.  Position 1 takes any thing and
  position 2 a string, so a string name is stored and a non-string one is refused."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(defn- holds-ask [s ctx] (boolean (v/ask? tu/*kb* s ctx)))

(defn- problem-types
  "The `:type` of each problem `check` reports for `sentence` in `ctx`, or of the argument
  conviction `assert` holds it inert under."
  [sentence ctx]
  (tu/without-entailing
   (or (not-empty (mapv :type (v/check tu/*kb* sentence ctx)))
       (into [] (keep :type) [(tu/write-conviction tu/*kb* sentence ctx)]))))

(tu/deftest-kb name-string-is-declared-in-the-theory
  (is (= 1 (count (v/sentexes-matching kb '(comment nameString ?c) CPT))))
  (is (holds-ask '(binary_predicate nameString) CPT))
  (is (holds-ask '(arg nameString 1 thing) CPT))
  (is (holds-ask '(quotedArg nameString 2 string) CPT))
  (is (empty? (v/sentexes-matching kb '(comment nameString ?c) 'CxWell))
      "CxWell does not read the vocabulary"))

(tu/deftest-kb a-name-string-is-a-string
  (tu/with-terms [CxDesk Ann Pebble]
    (v/assert kb (list 'genlCx CxDesk 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDesk CPT) 'CxUniverse)
    (v/assert kb (list 'human Ann) CxDesk)
    (testing "a string name passes the type check and is stored"
      (is (empty? (problem-types (list 'nameString Ann "Ann Example") CxDesk)))
      (v/assert kb (list 'nameString Ann "Ann Example") CxDesk)
      (is (holds-ask (list 'nameString Ann "Ann Example") CxDesk)))
    (testing "a thing can carry more than one name string"
      (v/assert kb (list 'nameString Ann "A. Example") CxDesk)
      (is (= #{"Ann Example" "A. Example"}
             (set (map #(get % '?n) (v/ask kb (list 'nameString Ann '?n) CxDesk))))))
    (testing "a non-string position 2 is refused"
      (is (= [:quoted-arg-type] (problem-types (list 'nameString Ann 5) CxDesk)))
      (is (= [:quoted-arg-type] (problem-types (list 'nameString Ann Pebble) CxDesk))))))
