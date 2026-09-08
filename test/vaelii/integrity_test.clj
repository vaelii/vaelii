;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.integrity-test
  "The bounded public KB-integrity sweep: declared specified-population obligations and
  query-only definition clashes over a caller-owned finite ground term set."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb a-passing-sufficient-and-failing-necessary-is-reported
  (tu/with-terms [widget qualifies required]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required  (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  widget (list required  '?x)) 'CxUniverse)
    (let [report (v/kb-integrity kb #{7} 'CxUniverse)
          finding (first (:definition-inconsistencies report))]
      (is (= :gap (:status report)))
      (is (= 1 (:candidate-count report)))
      (is (= [widget 7] ((juxt :collection :term) finding)))
      (is (= [{:defined-collection widget :condition (list qualifies '?x)}]
             (:passing-sufficient finding)))
      (is (= [{:defined-collection widget :condition (list required '?x)}]
             (:failing-necessary finding)))
      ;; Independent oracle: the public query surface really does answer both halves.
      (is (v/ask? kb (list widget 7) 'CxUniverse))
      (is (v/ask? kb (list 'not (list widget 7)) 'CxUniverse)))))

(tu/deftest-kb the-caller-owned-term-set-is-the-exact-bound
  (tu/with-terms [widget qualifies required]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required  (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  widget (list required  '?x)) 'CxUniverse)
    (is (= [[widget 7]]
           (mapv (juxt :collection :term)
                 (:definition-inconsistencies
                  (v/kb-integrity kb #{7} 'CxUniverse))))
        "8 would clash too, but the sweep never invents or enumerates it")
    (is (= {:status :audited :candidate-count 0}
           (v/kb-integrity kb #{} 'CxUniverse))
        "the empty finite bound is a real, clean audit")))

(tu/deftest-kb ordinary-represented-contradictions-are-not-definition-findings
  (tu/with-terms [widget]
    (v/assert kb (list widget 7) 'CxUniverse {:strength :default})
    (v/assert kb (list 'not (list widget 7)) 'CxUniverse {:strength :default})
    (is (seq (v/contradictions kb)) "the ordinary contradiction reader sees it")
    (is (= {:status :audited :candidate-count 1}
           (v/kb-integrity kb #{7} 'CxUniverse))
        "the definition audit neither aliases nor broadens contradictions")))

(tu/deftest-kb a-strict-genl-necessary-fast-fail-is-not-a-dual-answer
  (tu/with-terms [animal dog dogLike animalRequired dogRequired]
    (v/add-evaluatable kb dogLike        (constantly true))
    (v/add-evaluatable kb animalRequired (constantly false))
    (v/add-evaluatable kb dogRequired    (constantly false))
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'defnSufficient dog (list dogLike '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary animal (list animalRequired '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary dog (list dogRequired '?x)) 'CxUniverse)
    (is (not (v/ask? kb (list dog 7) 'CxUniverse))
        "the strict animal necessary fast-fails dog's positive definition prover")
    (is (v/ask? kb (list 'not (list dog 7)) 'CxUniverse))
    (let [report (v/kb-integrity kb #{7} 'CxUniverse)]
      (is (= [[animal 7]]
             (mapv (juxt :collection :term)
                   (:definition-inconsistencies report)))
          "animal answers both via dog's sufficient and its own failing necessary")
      (is (not-any? #(= dog (:collection %))
                    (:definition-inconsistencies report))
          "dog itself has only the negative answer because the strict ancestor fast-fails"))))

(tu/deftest-kb candidate-boundaries-fail-before-query-work
  (doseq [bad [(range) [7] '(7)]]
    (try
      (v/kb-integrity kb bad 'CxUniverse)
      (is false "only an explicitly finite set is accepted")
      (catch clojure.lang.ExceptionInfo e
        (is (= {:type :bad-args :op 'definition-inconsistencies
                :arg :candidate-terms}
               (ex-data e))))))
  (try
    (v/kb-integrity kb #{'?x} 'CxUniverse)
    (is false "an open term would turn the check into an enumerator")
    (catch clojure.lang.ExceptionInfo e
      (is (= {:type :bad-args :op 'definition-inconsistencies
              :arg :candidate-terms :term '?x}
             (ex-data e))))))

(tu/deftest-kb definition-findings-respect-context-visibility
  (tu/with-terms [widget qualifies required CxLeft CxRight]
    (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required  (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) CxLeft)
    (v/assert kb (list 'defnNecessary widget (list required '?x)) CxLeft)
    (is (= :gap (:status (v/kb-integrity kb #{7} CxLeft))))
    (is (= {:status :audited :candidate-count 1}
           (v/kb-integrity kb #{7} CxRight))
        "a sibling context cannot leak another theory's definitions into its report")))

(tu/deftest-kb specified-gaps-compose-with-definition-findings
  (tu/with-terms [widget qualifies required likes person Alice]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required  (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
    (v/assert kb (list 'binary_predicate likes) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likes person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [report (v/kb-integrity kb #{7} 'CxUniverse)]
      (is (= :gap (:status report)))
      (is (seq (:definition-inconsistencies report)))
      (is (= {:status :gap :gap :missing-slot-typing
              :pred likes :position 2}
             (get (:all-specified-violations report)
                  ['predAllSpecified likes person]))))))
