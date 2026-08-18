;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.query-helpers-test
  "Tests for first-if-singleton and sentex-matching in test-util."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest first-if-singleton-returns-sole-element
  (is (= :a (tu/first-if-singleton [:a])))
  (is (nil? (tu/first-if-singleton [])))
  (is (nil? (tu/first-if-singleton [:a :b])))
  (is (nil? (tu/first-if-singleton nil))))

(tu/deftest-kb sentex-matching-returns-unique-match
  (let [dog (tu/tmp-type) Muffet (tu/tmp-ind)]
    (testing "nil before assert — no match"
      (is (nil? (tu/sentex-matching kb (list dog Muffet) 'CxUniverse))))
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (testing "returns the sentex after assert"
      (let [sx (tu/sentex-matching kb (list dog Muffet) 'CxUniverse)]
        (is (some? sx))
        (is (= (list dog Muffet) (:sentence sx)))))))
