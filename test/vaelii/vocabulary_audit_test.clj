;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vocabulary-audit-test
  "Declared and enforced, against declared and ignored.

  Nothing about a declaration's *shape* says whether anything reads it.
  `(maxCardinality parentOf 2)` is a well-formed ternary fact, storable, believed, and
  read by nobody — so a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented.  `vaelii.impl.vocabulary` answers the
  question for the engine's own grammar, and these tests are what keep the answer true:
  a `definitional_predicate` or `syncategorematic` term the classification says nothing
  about fails here, and so does an entry naming a term the grammar has retired.

  An upper-layer baseline holds the whole population, which is why this is its own
  namespace — the constraint tests beside it (`constraint-vocabulary-test`) need a cleared
  KB."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.vocabulary :as vocab]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb every-term-the-grammar-declares-is-classified
  ;; The durable half.  A block predicate or syntax constant added without anybody
  ;; deciding whether the engine reads it lands in `:unclassified`, and this fails — which
  ;; is the whole point: `interArg` sat in the design notes as a plausible declaration for
  ;; as long as nothing was checking.
  (let [a (v/vocabulary-audit kb)]
    (is (empty? (:unclassified a))
        "a definitional_predicate or syncategorematic term vocabulary/classification says nothing about")
    (is (empty? (:retired a))
        "a classification entry naming a term core.txt no longer declares")
    (is (empty? (:contradicted a))
        "a term the special-predicate table gives an arm to and the classification calls inert")
    (is (seq (:enforced a)))
    (is (seq (:inert a)) "and the inert set is not empty — the classification calls some terms inert")))

(tu/deftest-kb a-new-grammar-declaration-nobody-classified-is-reported
  ;; The test above only fails if this mechanism works, so drive it: a term added to either
  ;; population shows up unclassified, and leaves it when the membership is retracted.
  (doseq [marker vocab/population-markers]
    (tu/with-terms [maxCardinality]
      (let [h (v/assert kb (list marker maxCardinality) 'CxUniverse)]
        (is (= [maxCardinality] (:unclassified (v/vocabulary-audit kb))) (str marker))
        (v/retract! kb h)
        (is (empty? (:unclassified (v/vocabulary-audit kb))) (str marker))))))

(tu/deftest-kb the-population-is-the-block-and-the-syntax
  ;; describe's :definitional-block parts, and the syntax the KB marks syncategorematic.
  (let [{:keys [enforced inert]} (v/vocabulary-audit kb)
        audited (into #{} (map first) (concat enforced inert))]
    (doseq [t '[comment positiveExampleComment negativeExampleComment genl disjoint
                orthogonal arity unary_predicate arg genlArg transitive functional
                termsRelated seeAlso]]
      (is (contains? audited t) (str t " is a part of the definitional block")))
    (doseq [t '[Quote set/monotonic set/inert set/defaultRule]]
      (is (contains? audited t) (str t " is syntax the engine reads")))
    (doseq [t '[genlCx implies CxUniverse thing]]
      (is (not (contains? audited t)) (str t " is in no term's block")))))

(defn- audited
  "Every term `vocabulary-audit` reports on, classified or not: the audit's population."
  [kb]
  (let [{:keys [enforced inert unclassified]} (v/vocabulary-audit kb)]
    (into (set unclassified) (map first) (concat enforced inert))))

(defn- derived-definitional
  "Assert each of `terms` is a `definitional_predicate` that the audit reads, `why` naming
  the classifier it is derived from."
  [kb terms why]
  (let [population (audited kb)]
    (doseq [t terms]
      (let [answered (v/ask? kb (list 'definitional_predicate t) 'CxUniverse)
            read     (contains? population t)]
        (is answered (str t " is a definitional_predicate " why))
        (is read (str t " is in vocabulary-audit's population, " why))))))

(tu/deftest-kb the-orders-are-definitional-through-type_type_by_order
  (derived-definitional kb '[type metatype meta_metatype] "through type_type_by_order"))

(tu/deftest-kb the-placement-predicates-are-definitional-through-ontology_predicate
  (derived-definitional kb '[genl disjoint separating partition orthogonal]
                        "through ontology_predicate"))

(tu/deftest-kb the-argument-declarations-are-definitional-through-arg_constraint
  (derived-definitional kb '[arg genlArg quotedArg interArg interArgEqual argArg]
                        "through arg_constraint"))

(tu/deftest-kb the-relation-properties-are-definitional-through-algebraic_predicate_property
  (derived-definitional kb '[transitive symmetric asymmetric reflexive functional]
                        "through algebraic_predicate_property"))

(tu/deftest-kb the-exact-arity-classes-are-definitional-through-their-mapping-facts
  (derived-definitional kb '[unary binary ternary quaternary quinary]
                        "through relationTypeByArity")
  (derived-definitional kb '[unary_predicate binary_predicate ternary_predicate
                             quaternary_predicate quinary_predicate]
                        "through predicateTypeByArity")
  (derived-definitional kb '[unary_function binary_function ternary_function
                             quaternary_function quinary_function]
                        "through functionTypeByArity")
  (let [population (audited kb)]
    (doseq [t '[at_least_binary at_least_ternary at_least_quaternary at_least_quinary]]
      (is (not (v/ask? kb (list 'definitional_predicate t) 'CxUniverse))
          (str t " is the subject of no mapping fact, so no rule makes it definitional"))
      (is (not (contains? population t)) (str t " is not in vocabulary-audit's population")))))

;; A test asserting the special-predicate table and the classification agree stood here and is gone.  It walked
;; `special/entries` asserting no functor with an arm was classified inert — which is
;; `audit`'s `:contradicted` restated, and the test above already asserts that empty.  The
;; half of it that was about two hand-written lists agreeing went with the hand-kept list: the
;; prose now sits on the term's own declaration and the class is read off that entry's
;; facets, so there is no second list for the table to disagree with.

(tu/deftest-kb the-two-new-constraints-are-on-the-enforced-side
  ;; Ties the implementations in `constraint-vocabulary-test` to the classification, so removing
  ;; one and leaving the claim is a failing test rather than a stale sentence.
  (is (:enforced (v/interpreted 'interArg)))
  (is (:enforced (v/interpreted 'arity)))
  (is (nil? (v/interpreted 'maxCardinality))
      "a term the grammar does not declare is out of scope, not answered")
  (is (:inert (v/interpreted 'typeToInstancePred))
      "and a declared term nothing reads says so rather than reading as enforced"))

(deftest the-classification-answers-in-exactly-one-of-the-two-classes
  (doseq [[term entry] vocab/classification]
    (is (= 1 (count (select-keys entry [:enforced :inert])))
        (str term " must be enforced or inert, and say which"))
    (is (seq (or (:enforced entry) (:inert entry)))
        (str term " carries no reason"))))
