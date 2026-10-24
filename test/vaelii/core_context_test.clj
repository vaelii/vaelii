;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.core-context-test
  "The upper ontology loads into CxUniverse and documents the core predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb core-predicates-are-documented
  (testing "every core predicate has a comment sentex in CxUniverse"
    (doseq [term '[thing genl genlCx arg comment implies]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term))))))
  (testing "comments are ordinary sentexes living in CxUniverse"
    (is (seq (v/sentexes-matching kb '(comment genl ?text) 'CxUniverse)))))

(tu/deftest-kb extended-core-vocabulary-is-documented
  (testing "metadata, negation, and virtual rule wrappers each have a comment"
    (doseq [term '[not contradicts ist disjoint disjoint_metatype and lessThan greaterThan
                   transitive symmetric asymmetric reflexive functional inverse arity
                   decontextualized_predicate
                   predicate unary_predicate binary_predicate ternary_predicate
                   set/forwardRule set/backwardRule set/inertRule set/defaultRule]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term)))))))

(tu/deftest-kb argisa-constraints-are-enforced-on-assert
  ;; the constraint-only reading: the conviction is the subject
  (tu/without-entailing
   ;; arg is a core predicate the engine interprets, so a constraint on it is checked
   ;; on assert.  The test defines its own vocabulary in CxUniverse and wires a data
   ;; context below it.
   (let [animal (tu/tmp-type) rock (tu/tmp-type) kin (tu/tmp-pred)
         tom (tu/tmp-ind) boulder (tu/tmp-ind)]
     (v/assert kb '(genlCx CxData CxUniverse) 'CxUniverse)   ; a data context below the upper layer
     (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
     (v/assert kb (list 'genl rock   'thing) 'CxUniverse)
     (v/assert kb (list 'disjoint animal rock) 'CxUniverse)
     (v/assert kb (list 'arg kin 1 animal) 'CxUniverse)                  ; the constraint
     (v/assert kb (list animal tom)    'CxData)
     (v/assert kb (list rock   boulder) 'CxData)
     (testing "the arg constraint applies on assert"
       (is (v/assert kb (list kin tom tom) 'CxData))                    ; tom is an animal: OK
       (is (= :arg-type                                                ; a rock is not an animal
              (tu/write-type kb #(v/assert kb (list kin boulder tom) 'CxData))))))))

(tu/deftest-kb argument-declarations-accept-functions-and-predicates
  (tu/with-terms [ReviewFn reviewRelation]
    (v/assert kb (list 'ternary_function ReviewFn) 'CxUniverse)
    (v/assert kb (list 'ternary_predicate reviewRelation) 'CxUniverse)
    (doseq [relation [ReviewFn reviewRelation]
            [position projection] [[1 'arg1] [2 'arg2] [3 'arg3]]]
      (v/assert kb (list 'arg relation position 'integer) 'CxUniverse)
      (is (true? (v/ask? kb (list projection relation 'integer) 'CxUniverse)))
      (is (empty? (v/check kb (list projection relation 'integer) 'CxUniverse))))))

(tu/deftest-kb the-four-and-five-position-projections-derive-each-other-with-arg
  (tu/with-terms [SurveyFn surveyRelation tmpScore]
    (v/assert kb (list 'genl tmpScore 'thing) 'CxUniverse)
    (v/assert kb (list 'quinary_function SurveyFn) 'CxUniverse)
    (v/assert kb (list 'quinary_predicate surveyRelation) 'CxUniverse)
    (testing "arg at position 4 or 5 concludes the projection"
      (doseq [relation [SurveyFn surveyRelation]
              [position projection] [[4 'arg4] [5 'arg5]]]
        (let [h (v/assert kb (list 'arg relation position 'integer) 'CxUniverse)]
          (is (true? (v/ask? kb (list projection relation 'integer) 'CxUniverse))
              (str projection " of " relation))
          (is (empty? (v/check kb (list projection relation 'integer) 'CxUniverse)))
          (v/retract! kb h))))
    (testing "the projection concludes arg at its position"
      (doseq [[position projection] [[4 'arg4] [5 'arg5]]]
        (let [h (v/assert kb (list projection surveyRelation tmpScore) 'CxUniverse)]
          (is (true? (v/ask? kb (list 'arg surveyRelation position tmpScore) 'CxUniverse))
              (str projection " concludes arg " position))
          (v/retract! kb h))))
    (testing "a projection past the relation's arity is refused as arg is"
      (tu/with-terms [pairRelation]
        (v/assert kb (list 'binary_predicate pairRelation) 'CxUniverse)
        (doseq [projection '[arg4 arg5]]
          (is (seq (v/check kb (list projection pairRelation 'integer) 'CxUniverse))
              (str projection " of a binary predicate")))))))

(tu/deftest-kb remaining-argument-metadata-accepts-relations
  ;; A temporary type rather than `integer`, because the declarations are the subject and
  ;; the type is incidental.  With subsumed mints pruned, the default, a `quotedArg` written
  ;; of `integer` gives it a type more specific than `thing`, which withdraws CxUniverse's own
  ;; minted `(thing integer)`; the re-mint after the teardown allocates a fresh handle, so
  ;; the baseline would come back saying the same thing under a different one, and
  ;; `assert-neutral!` refuses to call that restored (docs/argtypes.md).
  (tu/with-terms [ReviewFn reviewRelation tmpScalar]
    (v/assert kb (list 'genl tmpScalar 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_function ReviewFn) 'CxUniverse)
    (v/assert kb (list 'binary_predicate reviewRelation) 'CxUniverse)
    (doseq [relation [ReviewFn reviewRelation]
            declaration [(list 'genlArg relation 1 'thing)
                         (list 'quotedArg relation 1 tmpScalar)
                         (list 'interArg relation 1 tmpScalar 2 tmpScalar)]]
      (is (empty? (v/check kb declaration 'CxUniverse)))
      (v/assert kb declaration 'CxUniverse)
      (is (true? (v/ask? kb declaration 'CxUniverse))))))

(tu/deftest-kb arity-is-declared-functional
  ;; a relation has one arity, and the arity and its relation-wide exact class derive
  ;; each other — so a second, different (arity R N) is a clash rather than a second
  ;; belief.  Two numbers can never merge into one thing, so this is a nogood, not an
  ;; equality.  Two convictions reach it: (functional arity) on the table, and
  ;; (disjoint binary ternary) on the classes the two numbers derive.
  (is (v/has-prop? kb :functional 'arity))
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (is (integer? (v/assert kb (list 'arity rel 7) 'CxUniverse)))
    (is (not (and (v/ask? kb (list 'arity rel 2) 'CxUniverse)
                  (v/ask? kb (list 'arity rel 7) 'CxUniverse)))
        "the two values are one nogood, and not both believed")))

(tu/deftest-kb exact-arity-derives-fixed-policy-without-argument-entailment
  (binding [argument/*assertive-arg-types?* false]
    (tu/with-terms [freshRelation]
      (let [h (v/assert kb (list 'arity freshRelation 4) 'CxUniverse)]
        (is (v/ask? kb (list 'fixed_arity freshRelation) 'CxUniverse))
        (is (v/isa? kb freshRelation 'fixed_arity 'CxUniverse))
        (v/retract! kb h)
        (is (not (v/ask? kb (list 'fixed_arity freshRelation) 'CxUniverse)))
        (is (not (v/isa? kb freshRelation 'fixed_arity 'CxUniverse)))))))

(tu/deftest-kb the-upper-vocabulary-is-the-size-docs-kbs-says
  ;; A bound, not an exact count.  The exact number moves whenever a shipped upper file
  ;; gains a term on purpose, and `vocabulary-audit` already fails a functor nobody
  ;; classified.  The bound catches the load going wrong in bulk: an empty classpath, or a file read twice.
  (let [n (v/sentex-count kb)]
    (is (< 2000 n 5000)
        (str "the upper layer loaded " n " sentexes; docs/kbs.md's vocabulary row says 3,000+."
             "  A number outside this band means the load is wrong, not that the"
             "  vocabulary grew: check the classpath before touching the row."))))

(tu/deftest-kb an-edge-asserted-in-another-context-is-stored-in-cxuniverse
  ;; `(forced_decontextualized_predicate genlCx)` in core.txt stores every edge in
  ;; CxUniverse, so an edge written to a data context is the sentex a second assert finds.
  (tu/with-terms [CxLow CxHigh]
    (let [h (v/assert kb (list 'genlCx CxLow CxHigh) CxLow)]
      (is (= 'CxUniverse (:context (v/sentex kb h))))
      (is (= h (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))))
    (let [n (v/sentex-count kb)]
      (v/assert kb (list 'genlCx CxLow CxHigh) CxHigh)
      (is (= n (v/sentex-count kb)) "re-asserting the edge finds the one stored"))))
