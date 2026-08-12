;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.core-context-test
  "The CoreContext ontology loads and documents the core predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(tu/deftest-kb core-predicates-are-documented
  (testing "every core predicate has a comment sentex in CoreContext"
    (doseq [term '[thing genl genlContext argIsa comment implies]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term))))))
  (testing "comments are ordinary sentexes living in CoreContext"
    (is (seq (v/sentexes-matching kb '(comment genl ?text) 'CoreContext)))))

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
  ;; on assert.  (The starter's domain argIsa live in the upper RelationContext now, not
  ;; the vocabulary head, so this defines its own vocabulary — wiring a data context to
  ;; see CoreContext directly, since a CoreContext-only KB has no spindle bands.)
  (let [animal (tu/tmp-type) rock (tu/tmp-type) kin (tu/tmp-pred)
        tom (tu/tmp-ind) boulder (tu/tmp-ind)]
    (v/assert kb '(genlContext DataContext CoreContext) 'UniverseContext)   ; a data context that sees core
    (v/assert kb (list 'genl animal 'thing) 'CoreContext)
    (v/assert kb (list 'genl rock   'thing) 'CoreContext)
    (v/assert kb (list 'argIsa kin 1 animal) 'CoreContext)                  ; the constraint
    (v/assert kb (list animal tom)    'DataContext)
    (v/assert kb (list rock   boulder) 'DataContext)
    (testing "the argIsa constraint applies on assert"
      (is (v/assert kb (list kin tom tom) 'DataContext))                    ; tom is an animal: OK
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list kin boulder tom) 'DataContext))))))   ; a rock is not an animal

(tu/deftest-kb arity-is-declared-functional
  ;; a predicate has one arity, and the two spellings derive each other — so a second,
  ;; different (arity P N) is a clash rather than a second belief.  Two numbers can
  ;; never merge into one thing, so this is the hard rejection, not an equality.
  (is (v/has-prop? kb :functional 'arity))
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binaryPredicate rel) 'CoreContext)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'arity rel 7) 'CoreContext)))))

(tu/deftest-kb arity-does-not-inherit-across-predicate-specialization
  ;; Predicate specialization does not currently require a child to share its
  ;; parent's signature.  Preserving arity down genl would therefore let this
  ;; functional relation answer both 2 and 3 for child.
  (tu/with-terms [parent child]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl child parent) 'CoreContext)
      (v/assert kb (list 'arity parent 2) 'CoreContext)
      (v/assert kb (list 'arity child 3) 'CoreContext))
    (is (v/ask? kb (list 'arity child 3) 'CoreContext))
    (is (not (v/ask? kb (list 'arity child 2) 'CoreContext)))))

(tu/deftest-kb meta-constraints-inherit-through-predicate-and-type-hierarchies
  (tu/with-terms [parent child mammal animal food]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl child parent) 'CoreContext)
      (v/assert kb (list 'genl mammal animal) 'CoreContext)
      (v/assert kb (list 'genl animal 'thing) 'CoreContext)
      (v/assert kb (list 'genl food 'thing) 'CoreContext)
      (v/assert kb (list 'argIsa parent 1 mammal) 'CoreContext)
      (v/assert kb (list 'argGenl parent 2 mammal) 'CoreContext)
      (v/assert kb (list 'interArgIsa parent 1 animal 2 food) 'CoreContext))
    (testing "constraints on a predicate reach its specializations"
      (is (v/ask? kb (list 'argIsa child 1 mammal) 'CoreContext))
      (is (v/ask? kb (list 'argGenl child 2 mammal) 'CoreContext))
      (is (v/ask? kb (list 'interArgIsa child 1 animal 2 food) 'CoreContext)))
    (testing "unconditional constraint types answer through their supertypes"
      (is (v/ask? kb (list 'argIsa parent 1 animal) 'CoreContext))
      (is (v/ask? kb (list 'argGenl parent 2 animal) 'CoreContext)))
    (testing "conditional constraints narrow the trigger and widen the target"
      (is (v/ask? kb (list 'interArgIsa parent 1 mammal 2 food) 'CoreContext))
      (is (v/ask? kb (list 'interArgIsa parent 1 animal 2 'thing) 'CoreContext))
      (is (v/ask? kb (list 'interArgIsa parent 1 mammal 2 'thing) 'CoreContext))
      (is (not (v/ask? kb (list 'interArgIsa parent 1 'thing 2 food) 'CoreContext))
          "a constraint triggered by animal says nothing about non-animal things"))))
