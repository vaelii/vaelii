;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.able-may-can-test
  "`able`, `may` and `can` in life.txt: ability, permission, and the two together.

  `(able ?doer ?kind)` is dynamic ability: ?doer has what it takes to be the doer of a
  happening of kind ?kind.  `(may ?doer ?kind)` is deontic permission: ?doer is allowed
  to be that doer.  Neither is the epistemic reading of the English word.  `(can ?doer
  ?kind)` holds when both do, and gives each of them back.  These tests assert the three
  links and the independence of the two halves: ability without permission, or
  permission without ability, concludes no `can`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- setting!
  "Place context `ctx` under CxWell, make `kind` a happening kind and each of `doers`
  causal there, and return `ctx`."
  [kb ctx kind doers]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert kb (list 'genl kind 'happening) ctx)
  (doseq [d doers] (v/assert kb (list 'causal d) ctx))
  ctx)

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(tu/deftest-kb may-and-can-are-declared-like-able
  (doseq [p '[able may can]]
    (is (tu/holds-ask (list 'binary_predicate p) 'CxUniverse) (str p " is binary"))
    (is (tu/holds-ask (list 'arg p 1 'causal) 'CxUniverse) (str p " takes a causal doer first"))
    (is (tu/holds-ask (list 'genlArg p 2 'happening) 'CxUniverse)
        (str p " takes a happening kind second"))
    (is (= 1 (count (v/sentexes-matching kb (list 'comment p '?c) 'CxUniverse)))
        (str p " carries one comment"))))

(tu/deftest-kb ability-and-permission-together-conclude-can
  (tu/with-terms [CxRota kayaking Alice]
    (let [ctx (setting! kb CxRota kayaking [Alice])]
      (v/assert kb (list 'able Alice kayaking) ctx)
      (v/assert kb (list 'may Alice kayaking) ctx)
      (is (tu/holds-ask (list 'can Alice kayaking) ctx)))))

(tu/deftest-kb can-gives-back-ability
  (tu/with-terms [CxRota kayaking Bob]
    (let [ctx (setting! kb CxRota kayaking [Bob])]
      (v/assert kb (list 'can Bob kayaking) ctx)
      (is (tu/holds-ask (list 'able Bob kayaking) ctx)))))

(tu/deftest-kb can-gives-back-permission
  (tu/with-terms [CxRota kayaking Bob]
    (let [ctx (setting! kb CxRota kayaking [Bob])]
      (v/assert kb (list 'can Bob kayaking) ctx)
      (is (tu/holds-ask (list 'may Bob kayaking) ctx)))))

(tu/deftest-kb ability-without-permission-is-not-can
  (tu/with-terms [CxRota kayaking Alice]
    (let [ctx (setting! kb CxRota kayaking [Alice])]
      (v/assert kb (list 'able Alice kayaking) ctx)
      (testing "the ability holds"
        (is (tu/holds-ask (list 'able Alice kayaking) ctx)))
      (testing "and neither permission nor can follows from it"
        (is (not (tu/holds-ask (list 'may Alice kayaking) ctx)))
        (is (not (tu/holds-ask (list 'can Alice kayaking) ctx)))))))

(tu/deftest-kb permission-without-ability-is-not-can
  (tu/with-terms [CxRota kayaking Bob]
    (let [ctx (setting! kb CxRota kayaking [Bob])]
      (v/assert kb (list 'may Bob kayaking) ctx)
      (testing "the permission holds"
        (is (tu/holds-ask (list 'may Bob kayaking) ctx)))
      (testing "and neither ability nor can follows from it"
        (is (not (tu/holds-ask (list 'able Bob kayaking) ctx)))
        (is (not (tu/holds-ask (list 'can Bob kayaking) ctx)))))))

(tu/deftest-kb ability-and-permission-of-two-doers-do-not-combine
  (tu/with-terms [CxRota kayaking Alice Bob]
    (let [ctx (setting! kb CxRota kayaking [Alice Bob])]
      (v/assert kb (list 'able Alice kayaking) ctx)
      (v/assert kb (list 'may Bob kayaking) ctx)
      (is (not (tu/holds-ask (list 'can Alice kayaking) ctx)))
      (is (not (tu/holds-ask (list 'can Bob kayaking) ctx))))))
