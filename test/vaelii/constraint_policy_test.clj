;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-policy-test
  "Disjoint clash behavior under both :refuse and :arbitrate constraint policies.
  Verifies that v/check, v/assert, and v/disjoint? behave consistently with
  each policy, and that compatible individuals are unaffected in both modes."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- disjoint-kb
  "Set up a KB with a disjoint clash ready to fire: dog/cat disjoint,
  Muffet212 is a dog. Returns [kb dog cat Muffet212 Whiskers213]."
  [constraint-policy]
  (let [kb (v/open-kb (merge tu/scratch-space {:constraints constraint-policy}))
        _ (tu/clear-kb! kb)
        dog (tu/tmp-type) cat (tu/tmp-type)
        Muffet212 (tu/tmp-ind) Whiskers213 (tu/tmp-ind)]
    (v/assert kb (list 'genlContext 'NaturalWorldContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (v/assert kb (list dog Muffet212) 'NaturalWorldContext)
    [kb dog cat Muffet212 Whiskers213]))

(defn- common-assertions
  "Assertions that hold under both constraint policies."
  [kb cat Whiskers213]
  (testing "a compatible individual is unaffected"
    (is (v/assert kb (list cat Whiskers213) 'NaturalWorldContext))))

(deftest disjoint-clash-under-refuse
  (let [[kb dog cat Muffet212 Whiskers213] (disjoint-kb :refuse)]
    (common-assertions kb cat Whiskers213)
    (testing "check catches the clash before assert"
      (is (seq (v/check kb (list cat Muffet212) 'NaturalWorldContext))
          "check should return problems for a disjoint membership"))
    (testing "assert throws under :refuse"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat Muffet212) 'NaturalWorldContext))))
    (testing "Muffet212 is still only a dog"
      (is (v/ask? kb (list dog Muffet212) 'NaturalWorldContext))
      (is (not (v/ask? kb (list cat Muffet212) 'NaturalWorldContext))))))

(deftest disjoint-clash-under-arbitrate
  (let [[kb dog cat Muffet212 Whiskers213] (disjoint-kb :arbitrate)]
    (common-assertions kb cat Whiskers213)
    (testing "check returns no problems under :arbitrate — clashes are settled, not refused"
      (is (empty? (v/check kb (list cat Muffet212) 'NaturalWorldContext))))
    (testing "assert succeeds under :arbitrate"
      (is (v/assert kb (list cat Muffet212) 'NaturalWorldContext)))
    (testing "at least one side survives arbitration"
      (is (or (v/ask? kb (list dog Muffet212) 'NaturalWorldContext)
              (v/ask? kb (list cat Muffet212) 'NaturalWorldContext))
          "at least one side survives"))))
