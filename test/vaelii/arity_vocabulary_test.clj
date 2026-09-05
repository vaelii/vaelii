;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arity-vocabulary-test
  "The relation-wide exact/variable arity partition and its documentary floor vocabulary."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- refusal-data [f]
  (try
    (f)
    nil
    (catch clojure.lang.ExceptionInfo e
      (ex-data e))))

(tu/deftest-kb relation-is-the-common-parent
  (is (v/genl? kb 'predicate 'relation))
  (is (v/genl? kb 'function 'relation))
  (is (v/genl? kb 'relation 'thing))
  (is (v/isa? kb 'lessThan 'relation))
  (is (v/isa? kb 'MotherFn 'relation)))

(tu/deftest-kb exact-arity-and-variable-floors-are-distinct
  (testing "an exact declaration is fixed, not an overloaded floor"
    (is (v/ask? kb '(fixed_arity interArg) 'CxCore))
    (is (not (v/ask? kb '(arityMin interArg 5) 'CxCore))))
  (testing "the four current variable-arity predicates state only their lower bounds"
    (doseq [relation '[functionCorrespondingPredicate greaterThan lessThan termsRelated]]
      (is (some? (v/handle-of kb (list 'arityMin relation 2) 'CxCore))
          (str relation " has an asserted minimum"))
      (is (not (v/isa? kb relation 'binary_predicate))
          (str relation " is not overloaded as exactly binary")))))

(tu/deftest-kb relation-wide-types-own-the-arity-rules
  (doseq [[type arity] '[[unary 1] [binary 2] [ternary 3]]]
    (is (v/ask? kb (list 'relationTypeByArity type arity) 'CxCore)))
  (doseq [[type arity] '[[unary_predicate 1]
                         [binary_predicate 2]
                         [ternary_predicate 3]]]
    (is (v/ask? kb (list 'predicateTypeByArity type arity) 'CxCore))
    (is (v/ask? kb (list 'relationTypeByArity type arity) 'CxCore)
        "the predicate mapping specializes the relation mapping"))
  (doseq [[type arity] '[[unary_function 1]
                         [binary_function 2]
                         [ternary_function 3]]]
    (is (v/ask? kb (list 'functionTypeByArity type arity) 'CxCore))
    (is (v/ask? kb (list 'relationTypeByArity type arity) 'CxCore)
        "the function mapping specializes the relation mapping"))
  (is (v/genl? kb 'unary_predicate 'unary))
  (is (v/genl? kb 'binary_predicate 'binary))
  (is (v/genl? kb 'ternary_predicate 'ternary))
  (is (v/genl? kb 'unary_function 'unary))
  (is (v/genl? kb 'binary_function 'binary))
  (is (v/genl? kb 'ternary_function 'ternary))
  (doseq [type '[unary_predicate binary_predicate ternary_predicate]]
    (is (v/genl? kb type 'fixed_arity_predicate)))
  (doseq [type '[unary_function binary_function ternary_function]]
    (is (v/genl? kb type 'fixed_arity_function)))
  (is (v/isa? kb 'parentOf 'fixed_arity_predicate))
  (is (v/isa? kb 'MotherFn 'fixed_arity_function)))

(tu/deftest-kb disjoint-arity-policies-refuse-the-second-write
  (doseq [[first-policy second-policy] '[[fixed_arity variable_arity]
                                         [variable_arity fixed_arity]]]
    (tu/with-terms [candidateRelation]
      (v/assert kb (list first-policy candidateRelation) 'CxUniverse)
      (let [second-sentence (list second-policy candidateRelation)
            refusal         (refusal-data #(v/assert kb second-sentence 'CxUniverse))]
        (is (= :disjoint (:type refusal)))
        (is (nil? (v/handle-of kb second-sentence 'CxUniverse))
            "the refused policy is not stored")
        (is (v/ask? kb (list first-policy candidateRelation) 'CxUniverse)
            "the compatible first policy remains believed"))))
  (tu/with-terms [compatiblePredicate]
    (v/assert kb (list 'unary_predicate compatiblePredicate) 'CxUniverse)
    (is (v/assert kb (list 'fixed_arity_predicate compatiblePredicate) 'CxUniverse)
        "a predicate specialization and its fixed policy are compatible")))

(tu/deftest-kb relation-wide-exact-classes-refuse-each-other
  (doseq [[first-type second-type] '[[unary binary] [binary unary]
                                     [unary ternary] [ternary unary]
                                     [binary ternary] [ternary binary]]]
    (tu/with-terms [candidateRelation]
      (v/assert kb (list first-type candidateRelation) 'CxUniverse)
      (let [second-sentence (list second-type candidateRelation)
            refusal         (refusal-data #(v/assert kb second-sentence 'CxUniverse))]
        (is (= :disjoint (:type refusal)))
        (is (nil? (v/handle-of kb second-sentence 'CxUniverse))
            "the refused exact class is not stored"))))
  (tu/with-terms [compatibleRelation]
    (v/assert kb (list 'unary compatibleRelation) 'CxUniverse)
    (is (v/assert kb (list 'fixed_arity compatibleRelation) 'CxUniverse)
        "an exact class and its fixed policy are compatible")))

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
  (testing "the shipped functions use their exact relation-wide specializations"
    (doseq [[function type] '[[FatherFn unary_function]
                              [MotherFn unary_function]
                              [YearFn unary_function]
                              [MonthFn binary_function]
                              [QuantityFn binary_function]
                              [DayFn ternary_function]
                              [QuantityIntervalFn ternary_function]
                              [PredAllExistsFn ternary_function]
                              [PredExistsAllFn ternary_function]
                              [PredExistsInstanceFn ternary_function]
                              [PredInstanceExistsFn ternary_function]]]
      (is (v/isa? kb function type) (str function " is " type)))
    (is (v/isa? kb 'InstantFn 'fixed_arity_function)
        "the six-argument function stays explicitly fixed without minting a named family"))
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
  (testing "an exact arity is not also a variable floor"
    (is (not (v/isa? kb 'interArg 'at_least_binary_relation)))
    (is (not (v/isa? kb 'interArg 'at_least_ternary_relation))))
  (testing "the ternary floor specializes the binary floor"
    (is (v/genl? kb 'at_least_ternary_relation 'at_least_binary_relation))))

(tu/deftest-kb admits-argnum-is-vocabulary-only
  (is (v/isa? kb 'admitsArgnum 'binary_predicate))
  (is (v/ask? kb '(arg admitsArgnum 1 relation) 'CxCore))
  (is (v/ask? kb '(arg admitsArgnum 2 positive_integer) 'CxCore))
  (is (not (v/ask? kb '(admitsArgnum lessThan 212) 'CxCore))
      "no parallel finite rule set answers the documentary position query"))

(tu/deftest-kb every-relation-has-exactly-one-arity-policy
  (let [relations  (->> (v/query kb '(relation ?relation) 'CxInference)
                        (map #(get % '?relation))
                        set)
        violations (into (sorted-map)
                         (keep (fn [relation]
                                 (let [fixed?    (v/ask? kb (list 'fixed_arity relation)
                                                         'CxInference)
                                       variable? (v/ask? kb (list 'variable_arity relation)
                                                         'CxInference)]
                                   (when (= fixed? variable?)
                                     [relation {:fixed fixed? :variable variable?}]))))
                         relations)]
    (is (> (count relations) 300)
        "the oracle enumerates the loaded CxInference vocabulary, not an empty fixture")
    (is (empty? violations)
        (str "relations outside the exactly-one arity-policy partition: "
             (pr-str violations)))
    (is (some? (v/handle-of kb '(disjoint fixed_arity variable_arity) 'CxCore))
        "the partition is declared in KB data")))
