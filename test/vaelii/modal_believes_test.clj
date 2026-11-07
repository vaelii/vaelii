;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.modal-believes-test
  "Assertion boundaries and four-valued answers for modal belief sentences."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb asserting-a-belief-stores-the-wrapper-without-routing-the-proposition
  (tu/with-terms [sings Lark Listener CxAsker]
    (let [proposition (list sings Lark)
          goal (list 'believes Listener proposition)
          agent-context (symbol (str "CxAgent" Listener))
          h (v/assert kb goal CxAsker)]
      (is (= goal (:sentence (v/sentex kb h))))
      (is (= CxAsker (:context (v/sentex kb h))))
      (is (v/ask? kb goal CxAsker))
      (is (not (v/ask? kb proposition CxAsker)))
      (is (not (v/ask? kb proposition agent-context)))
      (is (nil? (v/handle-of kb proposition agent-context)))
      (v/retract! kb h)
      (is (not (v/ask? kb goal CxAsker))))))

(tu/deftest-kb a-modal-wrapper-does-not-close-free-variables
  (tu/with-terms [sings Lark Listener CxAsker]
    (doseq [goal [(list 'believes '?agent (list sings Lark))
                  (list 'believes Listener (list sings '?bird))]]
      (let [before (tu/sentex-ids kb)]
        (is (= :not-ground
               (tu/refusal-type #(v/assert kb goal CxAsker))))
        (is (= before (tu/sentex-ids kb))
            "a refused belief leaves no stored sentence")))))

(tu/deftest-kb argue-distinguishes-a-projected-belief-from-its-explicit-denial
  (tu/with-terms [sings Lark Listener CxAsker]
    (let [proposition (list sings Lark)
          goal (list 'believes Listener proposition)
          agent-context (symbol (str "CxAgent" Listener))]
      (doseq [opts [nil {:max-depth 2}]]
        (testing "without evidence neither side is known"
          (let [r (v/argue kb goal CxAsker opts)]
            (is (= :unknown (:verdict r)))
            (is (empty? (:for r)))
            (is (empty? (:against r))))))
      (let [negative (v/assert kb (list 'not proposition) agent-context)]
        (testing "believing not-P does not assert not-believes-P"
          (is (= :true (:verdict (v/argue kb (list 'believes Listener (list 'not proposition)) CxAsker))))
          (is (= :unknown (:verdict (v/argue kb goal CxAsker)))))
        (v/retract! kb negative))
      (let [denial (v/assert kb (list 'not goal) CxAsker)]
        (doseq [opts [nil {:max-depth 2}]]
          (let [r (v/argue kb goal CxAsker opts)]
            (is (= :false (:verdict r)))
            (is (empty? (:for r)))
            (is (seq (:against r)))))
        (v/assert kb proposition agent-context)
        (doseq [opts [nil {:max-depth 2}]]
          (let [r (v/argue kb goal CxAsker opts)]
            (is (= :contradiction (:verdict r)))
            (is (seq (:for r)))
            (is (seq (:against r)))))
        (v/retract! kb denial))
      (doseq [opts [nil {:max-depth 2}]]
        (let [r (v/argue kb goal CxAsker opts)]
          (is (= :true (:verdict r)))
          (is (seq (:for r)))
          (is (empty? (:against r))))))))
