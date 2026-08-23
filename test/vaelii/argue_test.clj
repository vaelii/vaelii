;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argue-test
  "Tests for vaelii.core/argue — four-valued epistemic status queries."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb argue-true-for-asserted-fact
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (is (= :true (:verdict (v/argue kb (list dog Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-unknown-for-unasserted-fact
  (tu/with-terms [hungry Muffet]
    (is (= :unknown (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-false-for-explicitly-negated-fact
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :false (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-contradiction-for-both-sides-at-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list hungry Muffet) 'CxUniverse)
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :contradiction (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-true-via-genl
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (is (= :true (:verdict (v/argue kb (list animal Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-rule-expansion-with-max-depth
  (tu/with-terms [dog hasFur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list hasFur '?x) 'CxUniverse {:direction :backward})
    (testing "without opts: ask does not fire backward rules"
      (is (= :unknown (:verdict (v/argue kb (list hasFur Muffet) 'CxUniverse)))))
    (testing "with max-depth: rules fire"
      (is (= :true (:verdict (v/argue kb (list hasFur Muffet) 'CxUniverse {:max-depth 3})))))
    (testing "and the rule-derived side carries the search's derivation, not a JTMS why"
      ;; the conclusion of a backward rule is never stored, so the JTMS has nothing to
      ;; explain it with and `:for-why` is the wrong key to look under
      (let [r (v/argue kb (list hasFur Muffet) 'CxUniverse {:max-depth 3})]
        (is (nil? (:for-why r)))
        (is (seq (:for-derivation r)))
        (is (= (list hasFur Muffet) (:goal (first (:for-derivation r)))))
        (is (= :rule (:via (first (:for-derivation r)))))))))

(tu/deftest-kb argue-a-stored-side-carries-the-jtms-why-and-no-derivation
  ;; the two explanations are a fallback, not a pair: where the JTMS answers, the search
  ;; is not run at all — a tree nobody reads costs a whole query
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [r (v/argue kb (list dog Muffet) 'CxUniverse {:max-depth 3})]
      (is (= :true (:verdict r)))
      (is (true? (:believed? (:for-why r))))
      (is (nil? (:for-derivation r))))))

(tu/deftest-kb argue-derives-no-tree-for-a-pattern-or-at-depth-zero
  (tu/with-terms [dog hasFur Muffet Rex]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list hasFur '?x) 'CxUniverse {:direction :backward})
    (testing "a pattern answers once per binding, so one tree off the front names none of them"
      (let [r (v/argue kb (list hasFur '?who) 'CxUniverse {:max-depth 3})]
        (is (= :true (:verdict r)))
        (is (= 2 (count (:for r))) "both answers are reported")
        (is (nil? (:for-derivation r)) "and no tree claims to explain them")))
    (testing "depth 0 expands no rule, so a side it still answers has no derivation"
      ;; the goal has to be provable at depth 0 for this to say anything: an unprovable
      ;; one carries no derivation because it carries no `:for` either
      (let [r (v/argue kb (list dog Muffet) 'CxUniverse {:max-depth 0})]
        (is (= :true (:verdict r)))
        (is (nil? (:for-derivation r)))))))

(tu/deftest-kb argue-a-prover-answered-side-carries-the-one-node-the-search-took
  ;; `genl` transitivity is the registry's answer, not a rule's — nothing is stored, so
  ;; the JTMS has no why, and the search's tree is the single `:leaf` node it walked.
  ;; True, and as much as the search knows: pinned because it is the shape every
  ;; taxonomy-, evaluatable- and calculus-answered side reports
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (let [r (v/argue kb (list animal Muffet) 'CxUniverse {:max-depth 3})]
      (is (= :true (:verdict r)))
      (is (nil? (:for-why r)) "the transitive conclusion is not stored")
      (is (= [{:goal (list animal Muffet) :via :leaf}] (:for-derivation r))))))

(tu/deftest-kb argue-explains-both-sides-of-a-contradiction
  ;; the asymmetry this pair of keys exists to close: before, a side a rule derived was
  ;; reported as provable and left unexplained, so an adjudicating caller saw evidence
  ;; for the stored side and silence for the other
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(list dog '?x)] (list barks '?x) 'CxUniverse
                   {:direction :backward :strength :default})
    (v/assert kb (list 'not (list barks Muffet)) 'CxUniverse {:strength :monotonic})
    (let [r (v/argue kb (list barks Muffet) 'CxUniverse {:max-depth 3})]
      (is (= :contradiction (:verdict r)))
      (testing "the stored side reads from the JTMS"
        (is (= :monotonic (:defeat-class (:against-why r))))
        (is (nil? (:against-derivation r))))
      (testing "the derived side reads from the search"
        (is (nil? (:for-why r)))
        (is (= :rule (:via (first (:for-derivation r)))))))))

(tu/deftest-kb argue-monotonic-wins-over-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse {:strength :default})
    (v/assert kb (list hungry Muffet) 'CxUniverse {:strength :monotonic})
    (is (= :true (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-refuses-an-option-it-does-not-read-at-its-own-door
  ;; `argue` reaches `query` only when `:max-depth` is there and takes the
  ;; no-rule-expansion `ask` arm otherwise, so a roster checked downstream is not checked
  ;; at all for exactly the misspelling that matters: `{:max-deph 3}` would answer
  ;; `:unknown` for a sentence a rule derives, which is the failure the docstring says
  ;; must not happen.  The check is `argue`'s own, and the roster is `query`'s.
  (tu/with-terms [dog hasFur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list hasFur '?x) 'CxUniverse {:direction :backward})
    (let [goal    (list hasFur Muffet)
          refusal (fn [opts]
                    (try (v/argue kb goal 'CxUniverse opts) nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (testing "a misspelt depth is refused rather than taking the facts-only arm"
        (doseq [opts [{:max-deph 3} {:max-depth 3 :max-deph 4} {:nonsense 1}]]
          (let [d (refusal opts)]
            (is (= :unknown-option (:type d)) (pr-str opts))
            (is (= (vec (sort v/query-opt-keys)) (:options d)) "and the refusal names the roster")
            (is (seq (:unknown d))))))
      (testing "a non-map opts too"
        (is (= :unknown-option (:type (refusal :oops))))
        (is (= :unknown-option (:type (refusal [:max-depth 3])))))
      (testing "and every rostered key still answers"
        (is (= :true (:verdict (v/argue kb goal 'CxUniverse {:max-depth 3}))))
        (is (= :true (:verdict (v/argue kb goal 'CxUniverse
                                        {:max-depth 3 :strategy :depth-first}))))
        (is (= :unknown (:verdict (v/argue kb goal 'CxUniverse nil))))))))
