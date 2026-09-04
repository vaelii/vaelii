;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arity-vocabulary-test
  "The relation-wide arity vocabulary, including the current absence of WFF/query
  readers for arityMin and admitsArgnum."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb relation-is-the-common-parent
  (is (v/genl? kb 'predicate 'relation))
  (is (v/genl? kb 'function 'relation))
  (is (v/genl? kb 'relation 'thing))
  (is (v/isa? kb 'lessThan 'relation))
  (is (v/isa? kb 'MotherFn 'relation)))

(tu/deftest-kb exact-arity-entails-the-same-minimum
  (testing "the existing exact declaration entails a minimum"
    (is (v/ask? kb '(arityMin interArg 5) 'CxCore)))
  (testing "the four current variable-arity relations state their lower bounds"
    (doseq [relation '[functionCorrespondingPredicate greaterThan lessThan termsRelated]]
      (is (some? (v/handle-of kb (list 'arityMin relation 2) 'CxCore))
          (str relation " has an asserted minimum")))))

(tu/deftest-kb fixed-and-variable-arity-have-relation-kind-specializations
  (testing "the historically direct fixed predicate is classified"
    (is (v/isa? kb 'interArg 'fixed_arity_predicate))
    (is (v/isa? kb 'interArg 'fixed_arity))
    (is (v/isa? kb 'interArg 'relation)))
  (testing "all current variable predicates carry the predicate specialization"
    (doseq [relation '[functionCorrespondingPredicate greaterThan lessThan termsRelated]]
      (is (v/isa? kb relation 'variable_arity_predicate))
      (is (v/isa? kb relation 'variable_arity))
      (is (v/isa? kb relation 'relation))))
  (testing "the function specializations exist without inventing instances"
    (is (v/genl? kb 'fixed_arity_function 'fixed_arity))
    (is (v/genl? kb 'fixed_arity_function 'function))
    (is (v/genl? kb 'variable_arity_function 'variable_arity))
    (is (v/genl? kb 'variable_arity_function 'function)))
  (testing "a function may use the relation-wide variable vocabulary"
    (tu/with-terms [RepeatFn]
      (v/assert kb (list 'variable_arity_function RepeatFn) 'CxUniverse)
      (v/assert kb (list 'arityMin RepeatFn 2) 'CxUniverse)
      (is (v/isa? kb RepeatFn 'function))
      (is (v/isa? kb RepeatFn 'variable_arity))
      (is (v/isa? kb RepeatFn 'at_least_binary_relation)))))

(tu/deftest-kb arity-minimum-classifies-relations-generically
  (testing "a minimum of two derives only the binary floor"
    (is (v/isa? kb 'lessThan 'at_least_binary_relation))
    (is (not (v/isa? kb 'lessThan 'at_least_ternary_relation))))
  (testing "an exact arity of five reaches both floors through arityMin"
    (is (v/isa? kb 'interArg 'at_least_binary_relation))
    (is (v/isa? kb 'interArg 'at_least_ternary_relation)))
  (testing "the ternary floor specializes the binary floor"
    (is (v/genl? kb 'at_least_ternary_relation 'at_least_binary_relation))))

(tu/deftest-kb admits-argnum-is-vocabulary-only
  (is (v/isa? kb 'admitsArgnum 'binary_predicate))
  (is (v/ask? kb '(arg admitsArgnum 1 relation) 'CxCore))
  (is (v/ask? kb '(arg admitsArgnum 2 positive_integer) 'CxCore))
  (is (not (v/ask? kb '(admitsArgnum lessThan 212) 'CxCore))
      "no parallel finite rule set answers the documentary position query"))

(tu/deftest-kb fixed-and-variable-classifications-remain-independent
  (is (not (v/isa? kb 'comment 'fixed_arity))
      "exact arity does not classify every relation as fixed")
  (is (nil? (v/handle-of kb '(disjoint fixed_arity variable_arity) 'CxCore))
      "the classes have no disjointness declaration"))
