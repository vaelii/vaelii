;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argue-test
  "Tests for vaelii.impl.argue — four-valued epistemic status queries."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.argue :as argue]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb argue-true-for-asserted-fact
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (is (= :true (:verdict (argue/argue kb (list dog Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-unknown-for-unasserted-fact
  (tu/with-terms [hungry Muffet]
    (is (= :unknown (:verdict (argue/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-false-for-explicitly-negated-fact
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :false (:verdict (argue/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-contradiction-for-both-sides-at-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list hungry Muffet) 'CxUniverse)
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :contradiction (:verdict (argue/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-true-via-genl
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (is (= :true (:verdict (argue/argue kb (list animal Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-rule-expansion-with-max-depth
  (tu/with-terms [dog hasFur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list hasFur '?x) 'CxUniverse {:direction :backward})
    (testing "without opts: ask does not fire backward rules"
      (is (= :unknown (:verdict (argue/argue kb (list hasFur Muffet) 'CxUniverse)))))
    (testing "with max-depth: rules fire"
      (is (= :true (:verdict (argue/argue kb (list hasFur Muffet) 'CxUniverse {:max-depth 3})))))))

(tu/deftest-kb argue-monotonic-wins-over-default
  (tu/with-terms [hungry Muffet]
    (let [kb2 (v/fork kb)]
      (v/assert kb2 (list 'not (list hungry Muffet)) 'CxUniverse {:strength :default})
      (v/assert kb2 (list hungry Muffet) 'CxUniverse {:strength :monotonic})
      (is (= :true (:verdict (argue/argue kb2 (list hungry Muffet) 'CxUniverse)))))))
