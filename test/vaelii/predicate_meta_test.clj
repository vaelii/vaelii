;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicate-meta-test
  "Predicate metadata: transitive / symmetric / inverse / reflexive generic
  provers, and the functional constraint."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb transitive-predicate
  (let [tangiblePartOf (tu/tmp-pred)
        wheel (tu/tmp-ind) car (tu/tmp-ind) vehicle (tu/tmp-ind) machine (tu/tmp-ind)]
    (v/assert kb (list 'transitive tangiblePartOf) 'CxNaturalWorld)
    (v/assert kb (list tangiblePartOf wheel car)     'CxNaturalWorld)
    (v/assert kb (list tangiblePartOf car vehicle)   'CxNaturalWorld)
    (v/assert kb (list tangiblePartOf vehicle machine) 'CxNaturalWorld)
    (testing "transitive closure over facts"
      (is (v/ask? kb (list tangiblePartOf wheel machine) 'CxNaturalWorld))   ; 3 steps
      (is (= #{car vehicle machine}
             (set (map #(get % '?w) (v/ask kb (list tangiblePartOf wheel '?w) 'CxNaturalWorld))))))
    (testing "non-parts are not derived"
      (is (not (v/ask? kb (list tangiblePartOf machine wheel) 'CxNaturalWorld))))))

(tu/deftest-kb symmetric-predicate
  (let [siblingOf (tu/tmp-pred) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert kb (list 'symmetric siblingOf) 'CxNaturalWorld)
    (v/assert kb (list siblingOf bob ann) 'CxNaturalWorld)
    (testing "the relation holds both ways though asserted once"
      (is (v/ask? kb (list siblingOf bob ann) 'CxNaturalWorld))
      (is (v/ask? kb (list siblingOf ann bob) 'CxNaturalWorld))     ; via the symmetric prover
      (is (= #{ann} (set (map #(get % '?x) (v/ask kb (list siblingOf '?x bob) 'CxNaturalWorld))))))))

(tu/deftest-kb inverse-predicate
  (let [parentOf (tu/tmp-pred) childOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert kb (list 'inverse parentOf childOf) 'CxNaturalWorld)
    (v/assert kb (list parentOf tom bob) 'CxNaturalWorld)
    (testing "the inverse is answerable from the forward facts"
      (is (v/ask? kb (list childOf bob tom) 'CxNaturalWorld))
      (is (= #{tom} (set (map #(get % '?p) (v/ask kb (list childOf bob '?p) 'CxNaturalWorld))))))))

(tu/deftest-kb reflexive-predicate
  (let [sameRegionAs (tu/tmp-pred) paris (tu/tmp-ind) rome (tu/tmp-ind)]
    (v/assert kb (list 'reflexive sameRegionAs) 'CxNaturalWorld)
    (testing "everything is in the relation with itself"
      (is (v/ask? kb (list sameRegionAs paris paris) 'CxNaturalWorld))
      (is (not (v/ask? kb (list sameRegionAs paris rome) 'CxNaturalWorld))))))

(tu/deftest-kb functional-constraint
  (let [birthYearOf (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (list 'functional birthYearOf) 'CxNaturalWorld)
    (v/assert kb (list birthYearOf tom 1980) 'CxNaturalWorld)
    (testing "a second, different value is a clash"
      (is (tu/stored-in-clash? kb (list birthYearOf tom 1990) 'CxNaturalWorld)))
    (testing "re-asserting the same value is fine"
      (is (v/assert kb (list birthYearOf tom 1980) 'CxNaturalWorld)))))
