;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.integrity-test
  "The bounded public KB-integrity sweep: declared specified-population obligations and
  query-only definition clashes over a caller-owned finite ground term set."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- state-snapshot [kb]
  (let [handles (tu/sentex-ids kb)]
    {:sentexes handles
     :belief  (into {} (map (fn [h] [h (v/believed? kb h 'CxUniverse)])) handles)
     :violations (v/violations kb)}))

(defn- blocking-applicability-prover [block? entered release]
  (reify provers/Prover
    (applicable? [_ _ goal _]
      (when (block? goal)
        (deliver entered true)
        @release)
      false)
    (est-bindings [_ _ _ _] 0)
    (cost [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 0)
    (solve [_ _ _ _] [])))

(defn- observing-applicability-prover [observe? observed]
  (reify provers/Prover
    (applicable? [_ _ goal _]
      (when (observe? goal) (swap! observed inc))
      false)
    (est-bindings [_ _ _ _] 0)
    (cost [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 0)
    (solve [_ _ _ _] [])))

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

(tu/deftest-kb aggregate-errors-raised-by-the-audit-stay-local
  (tu/with-terms [widget valueOf Subject BadValue]
    (v/assert kb (list valueOf Subject BadValue) 'CxUniverse)
    ;; The aggregate binds the definition member ?x, but reducing a symbol as a sum is
    ;; an aggregate violation and therefore no sufficient answer.
    (v/assert kb (list 'defnSufficient widget
                       (list 'agg/sum '?x '?v (list valueOf Subject '?v)))
              'CxUniverse)
    (v/clear-violations! kb)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{7} 'CxUniverse)]
      (is (= :audited (:status report)))
      (is (= before (state-snapshot kb))
          "sentexes, contextual belief, and the live violations ledger are unchanged")
      (is (empty? (v/violations kb)) "the aggregate diagnostic was audit-local"))))

(tu/deftest-kb witness-vectors-include-every-and-only-matching-definition
  (tu/with-terms [animal dog cat ownPass dogPassA dogPassB catMiss
                  needFailA needFailB needPass]
    (doseq [[pred answer] [[ownPass true] [dogPassA true] [dogPassB true]
                           [catMiss false] [needFailA false] [needFailB false]
                           [needPass true]]]
      (v/add-evaluatable kb pred (constantly answer)))
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'genl cat animal) 'CxUniverse)
    (doseq [[coll pred] [[animal ownPass] [dog dogPassA] [dog dogPassB] [cat catMiss]]]
      (v/assert kb (list 'defnSufficient coll (list pred '?x)) 'CxUniverse))
    (doseq [pred [needFailA needFailB needPass]]
      (v/assert kb (list 'defnNecessary animal (list pred '?x)) 'CxUniverse))
    (let [finding (first (filter #(= animal (:collection %))
                                 (:definition-inconsistencies
                                  (v/kb-integrity kb #{7} 'CxUniverse))))]
      (is (= [{:defined-collection animal :condition (list ownPass '?x)}
              {:defined-collection dog :condition (list dogPassA '?x)}
              {:defined-collection dog :condition (list dogPassB '?x)}]
             (:passing-sufficient finding))
          "all passing own/inherited sufficients are present; the failing cat one is absent")
      (is (= [{:defined-collection animal :condition (list needFailA '?x)}
              {:defined-collection animal :condition (list needFailB '?x)}]
             (:failing-necessary finding))
          "all failing necessaries are present; the passing one is absent"))))

(tu/deftest-kb exhausted-bounds-never-answer-audited
  (tu/with-terms [widget qualifies required]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
    (doseq [[options reason] [[{:max-work 0} :max-work]
                              [{:max-ms 0} :max-ms]
                              [{:max-results 0} :max-results]]]
      (let [report (v/kb-integrity kb #{7} 'CxUniverse options)]
        (is (= :truncated (:status report)) (pr-str options))
        (is (= reason (:reason report)) (pr-str options))
        (is (not= :audited (:status report)))))))

(tu/deftest-kb work-budget-reaches-inside-an-aggregate-condition
  (tu/with-terms [sized valueOf Subject]
    (doseq [n (range 100)]
      (v/assert kb (list valueOf Subject n) 'CxUniverse))
    (v/assert kb (list 'defnSufficient sized
                       (list 'agg/count '?x '?v (list valueOf Subject '?v)))
              'CxUniverse)
    (let [report (v/kb-integrity kb #{100} 'CxUniverse {:max-work 20})]
      (is (= :truncated (:status report)))
      (is (= :max-work (:reason report)))
      (is (= 1 (:candidate-count report))
          "one candidate still carries KB-owned aggregate extent cost")
      (is (= 20 (:work report)) "the cooperative meter stops at the exact bound"))))

(tu/deftest-kb elapsed-applicability-stops-traversal-and-keeps-completed-definitions
  (tu/with-terms [widget qualifies required]
    (let [entered  (promise)
          release  (promise)
          observed (atom 0)
          second-candidate? #(and (= qualifies (first %)) (= 8 (second %)))]
      (v/add-evaluatable kb qualifies (constantly true))
      (v/add-evaluatable kb required (constantly false))
      (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
      (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
      (v/add-prover kb (blocking-applicability-prover second-candidate? entered release))
      (v/add-prover kb (observing-applicability-prover second-candidate? observed))
      (let [audit (future (v/kb-integrity kb #{7 8} 'CxUniverse {:max-ms 200}))]
        (try
          (is (= true (deref entered 2000 ::timeout))
              "the deliberately slow applicable? callback was reached")
          (Thread/sleep 220)
          (finally (deliver release true)))
        (let [report (deref audit 2000 ::timeout)]
          (is (not= ::timeout report))
          (is (= :truncated (:status report)))
          (is (= :max-ms (:reason report)))
          (is (= [[widget 7]]
                 (mapv (juxt :collection :term)
                       (:definition-inconsistencies report)))
              "the first candidate's completed finding survives the second's timeout")
          (is (zero? @observed)
              "dispatch traversal stopped before the prover after the elapsed callback"))))))

(tu/deftest-kb result-exhaustion-keeps-completed-definition-findings
  (tu/with-terms [widget qualifies required]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
    (let [report (v/kb-integrity kb #{7 8} 'CxUniverse {:max-results 1})]
      (is (= :truncated (:status report)))
      (is (= :max-results (:reason report)))
      (is (= [[widget 7]]
             (mapv (juxt :collection :term) (:definition-inconsistencies report)))))))

(tu/deftest-kb elapsed-specified-audit-keeps-earlier-declaration-gaps
  (tu/with-terms [likesUntyped peopleA likesTyped peopleB person Alice]
    (let [entered (promise)
          release (promise)]
      (v/assert kb (list 'binary_predicate likesUntyped) 'CxUniverse)
      (v/assert kb (list 'binary_predicate likesTyped) 'CxUniverse)
      (v/assert kb (list 'unary_predicate peopleA) 'CxUniverse)
      (v/assert kb (list 'unary_predicate peopleB) 'CxUniverse)
      (v/assert kb (list 'predAllSpecified likesUntyped peopleA) 'CxUniverse)
      (v/assert kb (list 'predAllSpecified likesTyped peopleB) 'CxUniverse)
      ;; Learn the audit's own stable declaration order, then make its first row a gap
      ;; and its second row enter the timed callback. The oracle is about preservation,
      ;; not an incidental index insertion order.
      (let [[[first-pred first-indep] [second-pred second-indep]]
            (mapv (juxt '?pred '?indep)
                  (v/ask kb '(predAllSpecified ?pred ?indep) 'CxUniverse))
            second-declaration? #(= second-indep (first %))]
        (v/assert kb (list 'unary_predicate person) 'CxUniverse)
        (v/assert kb (list 'arg second-pred 2 person) 'CxUniverse)
        (v/assert kb (list second-indep Alice) 'CxUniverse)
        (v/add-prover kb (blocking-applicability-prover second-declaration? entered release))
        (let [audit (future (v/kb-integrity kb #{} 'CxUniverse {:max-ms 200}))]
          (try
            (is (= true (deref entered 2000 ::timeout)))
            (Thread/sleep 220)
            (finally (deliver release true)))
          (let [report (deref audit 2000 ::timeout)]
            (is (not= ::timeout report))
            (is (= :truncated (:status report)))
            (is (= :max-ms (:reason report)))
            (is (= {['predAllSpecified first-pred first-indep]
                    {:status :gap :gap :missing-slot-typing
                     :pred first-pred :position 2}}
                   (:all-specified-violations report))
                "the completed first declaration survives exhaustion in the second")))))))

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
