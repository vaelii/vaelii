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
    (doseq [term '[thing genl genlCx arg comment implies]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term))))))
  (testing "comments are ordinary sentexes living in CxCore"
    (is (seq (v/sentexes-matching kb '(comment genl ?text) 'CxCore)))))

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
  ;; arg is a core predicate the engine interprets, so a constraint on it is checked
  ;; on assert.  (The starter's domain arg live in the upper CxRelation now, not
  ;; the vocabulary head, so this defines its own vocabulary — wiring a data context to
  ;; see CxCore directly, since a CxCore-only KB has no spindle bands.)
  (let [animal (tu/tmp-type) rock (tu/tmp-type) kin (tu/tmp-pred)
        tom (tu/tmp-ind) boulder (tu/tmp-ind)]
    (v/assert kb '(genlCx CxData CxCore) 'CxUniverse)   ; a data context that sees core
    (v/assert kb (list 'genl animal 'thing) 'CxCore)
    (v/assert kb (list 'genl rock   'thing) 'CxCore)
    (v/assert kb (list 'arg kin 1 animal) 'CxCore)                  ; the constraint
    (v/assert kb (list animal tom)    'CxData)
    (v/assert kb (list rock   boulder) 'CxData)
    (testing "the arg constraint applies on assert"
      (is (v/assert kb (list kin tom tom) 'CxData))                    ; tom is an animal: OK
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list kin boulder tom) 'CxData))))))   ; a rock is not an animal

(tu/deftest-kb arity-is-declared-functional
  ;; a predicate has one arity, and the two spellings derive each other — so a second,
  ;; different (arity P N) is a clash rather than a second belief.  Two numbers can
  ;; never merge into one thing, so this is the hard rejection, not an equality.
  (is (v/has-prop? kb :functional 'arity))
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binary_predicate rel) 'CxCore)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'arity rel 7) 'CxCore)))))

(tu/deftest-kb the-core-vocabulary-is-the-size-docs-kbs-says
  ;; A bound, not a pin.  docs/kbs.md's row says "~920", and the exact number moves
  ;; whenever CxCore gains a term on purpose — which made an equality here pure churn:
  ;; it failed on every deliberate change and caught nothing else, because
  ;; `vocabulary-audit` already fails a functor nobody classified.  What a count *can*
  ;; catch is the load going wrong in bulk — an empty classpath, a file read twice — so
  ;; that is what this asserts.
  (let [n (v/sentex-count kb)]
    (is (< 500 n 1800)
        (str "CxCore loaded " n " sentexes; docs/kbs.md's Core vocabulary row says ~920."
             "  A number outside this band means the load is wrong, not that the"
             "  vocabulary grew — check the classpath before touching the row."))))
