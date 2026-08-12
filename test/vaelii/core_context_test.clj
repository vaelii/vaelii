;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.core-context-test
  "The CxCore ontology loads and documents the core predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(tu/deftest-kb core-predicates-are-documented
  (testing "every core predicate has a comment sentex in CxCore"
    (doseq [term '[thing genl genlCx argIsa comment implies]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term))))))
  (testing "comments are ordinary sentexes living in CxCore"
    (is (seq (v/sentexes-matching kb '(comment genl ?text) 'CxCore)))))

(tu/deftest-kb extended-core-vocabulary-is-documented
  (testing "metadata, negation, and virtual rule wrappers each have a comment"
    (doseq [term '[not contradicts ist disjoint disjointMetatype and lessThan greaterThan
                   transitive symmetric reflexive functional inverse arity
                   decontextualizedPredicate
                   predicate unaryPredicate binaryPredicate ternaryPredicate
                   symmetricPredicate transitivePredicate reflexivePredicate functionalPredicate
                   set/forwardRule set/backwardRule set/inertRule set/defaultRule]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term)))))))

(tu/deftest-kb argisa-constraints-are-enforced-on-assert
  ;; argIsa is a core predicate the engine interprets, so a constraint on it is checked
  ;; on assert.  (The starter's domain argIsa live in the upper CxRelation now, not
  ;; the vocabulary head, so this defines its own vocabulary — wiring a data context to
  ;; see CxCore directly, since a CxCore-only KB has no spindle bands.)
  (let [animal (tu/tmp-type) rock (tu/tmp-type) kin (tu/tmp-pred)
        tom (tu/tmp-ind) boulder (tu/tmp-ind)]
    (v/assert kb '(genlCx CxData CxCore) 'CxUniverse)   ; a data context that sees core
    (v/assert kb (list 'genl animal 'thing) 'CxCore)
    (v/assert kb (list 'genl rock   'thing) 'CxCore)
    (v/assert kb (list 'argIsa kin 1 animal) 'CxCore)                  ; the constraint
    (v/assert kb (list animal tom)    'CxData)
    (v/assert kb (list rock   boulder) 'CxData)
    (testing "the argIsa constraint applies on assert"
      (is (v/assert kb (list kin tom tom) 'CxData))                    ; tom is an animal: OK
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list kin boulder tom) 'CxData))))))   ; a rock is not an animal

(tu/deftest-kb arity-is-declared-functional
  ;; a predicate has one arity, and the two spellings derive each other — so a second,
  ;; different (arity P N) is a clash rather than a second belief.  Two numbers can
  ;; never merge into one thing, so this is the hard rejection, not an equality.
  (is (v/has-prop? kb :functional 'arity))
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binaryPredicate rel) 'CxCore)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'arity rel 7) 'CxCore)))))

(tu/deftest-kb arity-is-guarded-across-predicate-specialization
  ;; v0.8.0: the genl edge guards arity consistency — a child predicate
  ;; cannot declare a different arity than its parent, since every child
  ;; tuple is a parent tuple and tuples of different lengths cannot be the
  ;; same tuples.  The guard rejects rather than inherits: the child is not
  ;; given the parent's arity, but it cannot contradict it.
  (tu/with-terms [parent child]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl child parent) 'CxCore)
      (v/assert kb (list 'arity parent 2) 'CxCore))
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'arity child 3) 'CxCore)))))

(tu/deftest-kb meta-constraints-inherit-through-predicate-and-type-hierarchies
  (tu/with-terms [parent child mammal animal food]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl child parent) 'CxCore)
      (v/assert kb (list 'genl mammal animal) 'CxCore)
      (v/assert kb (list 'genl animal 'thing) 'CxCore)
      (v/assert kb (list 'genl food 'thing) 'CxCore)
      (v/assert kb (list 'argIsa parent 1 mammal) 'CxCore)
      (v/assert kb (list 'argGenl parent 2 mammal) 'CxCore)
      (v/assert kb (list 'interArgIsa parent 1 animal 2 food) 'CxCore))
    (testing "constraints on a predicate reach its specializations"
      (is (v/ask? kb (list 'argIsa child 1 mammal) 'CxCore))
      (is (v/ask? kb (list 'argGenl child 2 mammal) 'CxCore))
      (is (v/ask? kb (list 'interArgIsa child 1 animal 2 food) 'CxCore)))
    (testing "unconditional constraint types answer through their supertypes"
      (is (v/ask? kb (list 'argIsa parent 1 animal) 'CxCore))
      (is (v/ask? kb (list 'argGenl parent 2 animal) 'CxCore)))
    (testing "conditional constraints narrow the trigger and widen the target"
      (is (v/ask? kb (list 'interArgIsa parent 1 mammal 2 food) 'CxCore))
      (is (v/ask? kb (list 'interArgIsa parent 1 animal 2 'thing) 'CxCore))
      (is (v/ask? kb (list 'interArgIsa parent 1 mammal 2 'thing) 'CxCore))
      (is (not (v/ask? kb (list 'interArgIsa parent 1 'thing 2 food) 'CxCore))
          "a constraint triggered by animal says nothing about non-animal things"))))
