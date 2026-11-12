;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.engine-vocabulary-test
  "The terms the engine reads by name are declared in CxUniverse, so a KB can query what the
  engine answers and the vocabulary audit classifies each one.  Each row checks one
  declaration against the engine behaviour it describes."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

;; ---- different -------------------------------------------------------------

(tu/deftest-kb different-is-declared-at-the-arity-its-prover-answers
  (testing "the declaration loads and the vocabulary audit classifies the term"
    (is (:enforced (v/interpreted 'different)))
    (is (true? (v/ask? kb '(variable_arity_predicate different) U)))
    (is (true? (v/ask? kb '(arityMin different 2) U)))
    (is (true? (v/ask? kb '(args different thing) U)) "every side is a term of any kind")
    (is (true? (v/ask? kb '(commutative different) U))))
  (testing "two distinct names are different in either order"
    (tu/with-terms [Alpha Beta]
      (is (true? (v/ask? kb (list 'different Alpha Beta) U)))
      (is (true? (v/ask? kb (list 'different Beta Alpha) U)))
      (is (false? (v/ask? kb (list 'different Alpha Alpha) U))))))

;; ---- the equality relations and the rule and strength wrappers -------------

(tu/deftest-kb the-equality-relations-are-declared-binary-with-thing-positions
  (doseq [r '[sameAs equals]]
    (is (:enforced (v/interpreted r)) (str r " is classified enforced"))
    (is (true? (v/ask? kb (list 'binary_predicate r) U)) (str r " is a binary_predicate"))
    (is (= #{[1 'thing] [2 'thing]}
           (set (for [{[_ _ n t] :sentence} (v/sentexes-matching kb (list 'arg r '?n '?t) '?ctx)]
                  [n t])))
        (str r " declares thing at both positions: either side is a term of any kind")))
  (testing "a merge under either relation still answers from the closure"
    (tu/with-terms [Alpha Beta Gamma Delta]
      (v/assert kb (list 'sameAs Alpha Beta) U)
      (v/assert kb (list 'equals Gamma Delta) U)
      (is (true? (v/ask? kb (list 'sameAs Beta Alpha) U)))
      (is (true? (v/ask? kb (list 'equals Delta Gamma) U)))
      (is (false? (v/ask? kb (list 'different Alpha Beta) U))))))

(tu/deftest-kb every-wrapper-the-engine-peels-is-commented-and-classified
  (doseq [w '[set/forwardRule set/backwardRule set/defaultRule set/inertRule
              set/forwardOnlyRule set/solveRule set/assumptionRule
              set/hardConstraint set/softConstraint set/monotonic set/inert]]
    (is (:enforced (v/interpreted w)) (str w " is classified enforced"))))

;; ---- the signed integer types ----------------------------------------------

(tu/deftest-kb integer-is-partitioned-by-sign-twice
  (testing "each part is below integer through its partition"
    (doseq [t '[positive_integer non_positive_integer negative_integer non_negative_integer]]
      (is (true? (v/ask? kb (list 'genl t 'integer) U)) (str t " is below integer"))))
  (testing "the parts of one partition are disjoint, and the two partitions cross"
    (is (true? (v/ask? kb '(disjoint positive_integer non_positive_integer) U)))
    (is (true? (v/ask? kb '(disjoint negative_integer non_negative_integer) U)))
    (is (not (true? (v/ask? kb '(disjoint non_negative_integer non_positive_integer) U)))
        "zero is in both non_ types"))
  (testing "a literal is admitted by the sign types it has"
    (is (true? (v/ask? kb '(non_negative_integer 0) U)))
    (is (true? (v/ask? kb '(non_positive_integer 0) U)))
    (is (true? (v/ask? kb '(negative_integer -3) U)))
    (is (true? (v/ask? kb '(non_positive_integer -3) U)))
    (is (false? (v/ask? kb '(non_negative_integer -3) U)))))

;; ---- argN --------------------------------------------------------------------

(tu/deftest-kb argN-is-declared-with-position-0-admitted
  (is (:enforced (v/interpreted 'argN)) "provers/ArgPositionProver answers argN")
  (is (true? (v/ask? kb '(ternary_predicate argN) U)))
  (is (empty? (v/sentexes-matching kb '(arg argN 1 ?t) '?ctx)) "the term found declares no type")
  (is (true? (v/ask? kb '(arg argN 2 non_negative_integer) U))
      "position 0, the relation or operator, is in the type")
  (is (true? (v/ask? kb '(non_negative_integer 0) U)))
  (is (true? (v/ask? kb '(quotedArg argN 3 formula) U))))

(tu/deftest-kb an-argN-fact-is-refused-and-the-prover-answers-it-at-position-0
  (tu/with-terms [likes Fred Mary]
    (let [s (list likes Fred Mary)]
      (is (= :not-well-formed (tu/refusal-type #(v/assert kb (list 'argN Mary 2 s) U))))
      (is (= :not-well-formed (tu/refusal-type #(v/assert kb (list 'argN Fred 2 s) U)))
          "a false argN fact is refused as a true one is")
      (is (true? (v/ask? kb (list 'argN likes 0 s) U)))
      (is (true? (v/ask? kb (list 'argN Mary 2 s) U)))
      (is (not (v/ask? kb (list 'argN Fred 2 s) U))))))

;; ---- not_assertible ------------------------------------------------------------

(defn- marked-not-assertible
  "The predicates CxUniverse declares `not_assertible`, as a set."
  [kb]
  (into #{} (map #(second (:sentence %))) (v/sentexes-matching kb '(not_assertible ?p) U)))

(tu/deftest-kb every-query-only-term-is-declared-not-assertible
  (is (:enforced (v/interpreted 'not_assertible)))
  (is (= #{} (set/difference pr/query-only (marked-not-assertible kb)))
      "a term the engine refuses as query-only and the KB does not declare"))

(tu/deftest-kb every-term-cxuniverse-declares-not-assertible-is-refused
  (let [tax (reasoning/taxonomy kb)]
    (doseq [t (marked-not-assertible kb)]
      (is (seq (special/wff-problems tax (list t 'Alpha 'Beta) U)) (str t " is stored"))
      (is (seq (special/wff-problems tax (list 'not (list t 'Alpha 'Beta)) U))
          (str "a denial of " t " is stored")))))

(tu/deftest-kb a-fact-of-a-not-assertible-predicate-is-believed-in-neither-arrival-order
  (tu/with-terms [likes Alpha Beta Gamma Delta]
    (let [fact (list likes Alpha Beta)
          h    (v/assert kb fact U)
          mark #(v/assert kb (list 'not_assertible likes) U)]
      (is (true? (v/ask? kb fact U)))
      (let [m (mark)]
        (testing "a mark arriving after the fact holds the fact inert"
          (is (false? (v/believed? kb h U))))
        (testing "a fact or a denial written after the mark is refused"
          (is (= :not-well-formed (tu/refusal-type #(v/assert kb (list likes Gamma Delta) U))))
          (is (= :not-well-formed (tu/refusal-type #(v/assert kb (list 'not (list likes Gamma Delta)) U)))))
        (v/retract! kb m)
        (testing "the mark retracted, the fact stored before it is believed again"
          (is (true? (v/believed? kb h U)))))
      (v/retract! kb h))))

(tu/deftest-kb a-fact-held-inert-by-a-late-not-assertible-mark-stays-inert-after-recover
  (tu/with-terms [likes Alpha Beta swims Nemo]
    (let [fact (list likes Alpha Beta)
          hs   [(v/assert kb fact U) (v/assert kb (list 'not_assertible likes) U)]]
      (doseq [reopen? [false true]]
        (testing (if reopen? "reopened" "in place")
          (is (= [false false false]
                 (mapv :loser (tu/recovered-readings kb reopen? [fact U]
                                                     #(v/assert % (list swims Nemo) U))))
              "unbelieved in the source, after the recover and after an unrelated write")))
      (doseq [h (rseq hs)] (v/retract! kb h)))))

;; ---- the forced-monotonic set ------------------------------------------------

(tu/deftest-kb every-predicate-the-engine-holds-forced-monotonic-is-declared-so
  (doseq [[kind decl] {:forced-monotonic          'forced_monotonic_predicate
                       :forced-between-predicates 'forced_monotonic_between_predicates}]
    (is (= #{} (set/difference (decide/baseline-forced kind)
                               (into #{} (map #(second (:sentence %)))
                                     (v/sentexes-matching kb (list decl '?p) U))))
        (str "held as " kind " and not declared " decl " in CxUniverse"))))
