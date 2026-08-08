;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.semantics-test
  "The transitivity uses: isa? via genl, argIsa constraint checking, specificity
  in matching, genlContext context placement, and rule-as-sentex retraction."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- type-hierarchy [kb {:keys [animal thing physical-object person dog]}]
  ;; make NaturalWorldContext see UniverseContext so context-scoped constraint checks apply
  (v/assert kb (list 'genlContext 'NaturalWorldContext 'UniverseContext) 'UniverseContext)
  (doseq [g [(list 'genl animal thing) (list 'genl physical-object thing)
             (list 'genl animal physical-object) (list 'genl person animal)
             (list 'genl dog animal)]]
    (v/assert kb g 'UniverseContext)))

(tu/deftest-kb isa-via-genl
  (let [animal (tu/tmp-type) thing 'thing physical-object (tu/tmp-type)
        person (tu/tmp-type) dog (tu/tmp-type)
        fido (tu/tmp-ind) tom (tu/tmp-ind)]
    (type-hierarchy kb {:animal animal :thing thing :physical-object physical-object
                        :person person :dog dog})
    (v/assert kb (list dog fido) 'NaturalWorldContext)
    (v/assert kb (list person tom) 'NaturalWorldContext)
    (testing "transitive type membership"
      (is (v/isa? kb fido animal))
      (is (v/isa? kb fido thing))
      (is (v/isa? kb tom thing))
      (is (not (v/isa? kb tom dog)))
      (is (not (v/isa? kb fido person))))))

(tu/deftest-kb arg-constraints-use-transitivity
  (let [animal (tu/tmp-type) thing 'thing physical-object (tu/tmp-type)
        person (tu/tmp-type) dog (tu/tmp-type)
        likesPet (tu/tmp-pred) tom (tu/tmp-ind) fido (tu/tmp-ind)]
    (type-hierarchy kb {:animal animal :thing thing :physical-object physical-object
                        :person person :dog dog})
    (v/assert kb (list 'argIsa likesPet 1 person) 'UniverseContext)
    (v/assert kb (list person tom) 'NaturalWorldContext)
    (v/assert kb (list dog fido) 'NaturalWorldContext)
    (testing "a person satisfies the arg-1 person constraint"
      (is (v/assert kb (list likesPet tom fido) 'NaturalWorldContext)))
    (testing "a dog in arg 1 violates it (dog is-a thing but not is-a person)"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list likesPet fido tom) 'NaturalWorldContext))))))

(tu/deftest-kb specificity-in-matching
  (let [dog (tu/tmp-type) animal (tu/tmp-type) breathes (tu/tmp-pred) fido (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'UniverseContext)
    (v/assert kb (list dog fido) 'UniverseContext)
    (testing "a rule about animals fires on a dog (subtype), without materializing (animal Muffet)"
      (is (seq (v/sentexes-matching kb (list breathes fido) 'UniverseContext)))
      (is (empty? (v/sentexes-matching kb (list animal fido) 'UniverseContext))))))

(tu/deftest-kb context-placement-in-forward-inference
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert kb (list 'genlContext 'BioContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext 'CoreContext 'UniverseContext) 'UniverseContext)
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z)
                   'UniverseContext {:chain? false})            ; universal rule
    (v/assert kb (list parentOf tom bob) 'BioContext)             ; specific facts
    (v/assert kb (list parentOf bob ann) 'BioContext)
    (testing "justification lands in the maximal context that sees rule + facts"
      (is (seq   (v/sentexes-matching kb (list grandparentOf tom ann) 'BioContext)))
      (is (empty? (v/sentexes-matching kb (list grandparentOf tom ann) 'UniverseContext))))))

(tu/deftest-kb forward-combines-specificity-and-context
  (let [dog (tu/tmp-type) animal (tu/tmp-type) breathes (tu/tmp-pred) fido (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert kb (list 'genlContext 'BioContext 'UniverseContext) 'UniverseContext)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'UniverseContext {:chain? false})  ; universal rule
    (v/assert kb (list dog fido) 'BioContext)                    ; specific, subtype fact
    (testing "the dog (subtype) fires the animal rule, and the justification lands in BioContext"
      (is (seq   (v/sentexes-matching kb (list breathes fido) 'BioContext)))
      (is (empty? (v/sentexes-matching kb (list breathes fido) 'UniverseContext))))))

(tu/deftest-kb retracting-a-rule-removes-its-justifications
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)
        rule-h (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'UniverseContext)]
    (v/assert kb (list parentOf tom bob) 'UniverseContext)
    (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'UniverseContext)))
    (v/retract! kb rule-h)
    (testing "the rule's derivation vanishes but the fact remains"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'UniverseContext)))
      (is (seq (v/sentexes-matching kb (list parentOf tom bob) 'UniverseContext))))))
