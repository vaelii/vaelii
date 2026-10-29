;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.integrity-test
  "The bounded public KB-integrity sweep: declared specified-population obligations and
  query-only definition clashes over a caller-owned finite ground term set."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- sans-meter
  "`report` without the `:work` and `:elapsed-ms` every answer carries."
  [report]
  (dissoc report :work :elapsed-ms))

(defn- state-snapshot [kb]
  (let [handles (tu/sentex-ids kb)]
    {:sentexes handles
     :belief  (into {} (map (fn [h] [h (v/believed? kb h 'CxUniverse)])) handles)
     :violations (v/violations kb)}))

(defn- clock-moving-prover
  "A prover whose `applicable?` moves the clock past any deadline when `move?` holds of
  the goal, then declines."
  [move? skew]
  (reify prover-types/Prover
    (applicable? [_ _ goal _]
      (when (move? goal) (swap! skew + 3600000000000))
      false)
    (est-bindings [_ _ _ _] 0)
    (cost [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 0)
    (solve [_ _ _ _] [])))

(defn- with-skewed-clock
  "`(f skew)` with `budget/now` reading the real clock plus the nanoseconds in `skew`, so
  a callback passes a deadline by moving `skew` and the test sleeps for nothing."
  [f]
  (let [skew (atom 0)]
    (with-redefs [budget/now #(+ (System/nanoTime) (long @skew))]
      (f skew))))

(defn- observing-applicability-prover [observe? observed]
  (reify prover-types/Prover
    (applicable? [_ _ goal _]
      (when (observe? goal) (swap! observed inc))
      false)
    (est-bindings [_ _ _ _] 0)
    (cost [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 0)
    (solve [_ _ _ _] [])))

(defn- chunked-answer-prover
  "A prover answering `pred` from one 32-element chunk, whose first element moves the
  clock past any deadline."
  [pred skew produced]
  (reify prover-types/Prover
    (applicable? [_ _ goal _] (= pred (first goal)))
    (est-bindings [_ _ _ _] 32)
    (cost [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 100)
    (solve [_ _ _ _]
      (map (fn [n]
             (when (zero? n) (swap! skew + 3600000000000))
             (swap! produced inc)
             {})
           (range 32)))))

(def ^:private without-missing-arg
  "Every category but `:missing-arg`, for a fixture whose bare declarations would
  otherwise report their untyped positions beside the finding under test."
  #{:definition-inconsistencies :all-specified-violations :genl-arg-widening
    :not-under-thing :implicit-genl :implicit-arity-class :orthogonal-over-separation
    :twin-genls :derivable-stated-edge :disjoint-could-be-partition})

(defn- content-order
  "Declaration tuples in the content order the specified pass reads them in."
  [tuples]
  (sort-by #(apply list %) nm/compare-form tuples))

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
           (sans-meter (v/kb-integrity kb #{} 'CxUniverse)))
        "the empty finite bound is a real, clean audit")))

(tu/deftest-kb every-answer-carries-the-work-and-time-it-spent
  (tu/with-terms [widget qualifies required]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required  (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  widget (list required  '?x)) 'CxUniverse)
    (let [audited (v/kb-integrity kb #{} 'CxUniverse)
          gap     (v/kb-integrity kb #{7} 'CxUniverse)
          lifted  (v/kb-integrity kb #{7} 'CxUniverse {:max-work nil})]
      (is (= [:audited :gap :gap] (mapv :status [audited gap lifted])))
      (is (every? #(and (nat-int? (:work %)) (number? (:elapsed-ms %)))
                  [audited gap lifted]))
      (is (pos? (:work gap)) "a sweep that read a definition spent work on it"))))

(tu/deftest-kb ordinary-represented-contradictions-are-not-definition-findings
  (tu/with-terms [widget]
    (v/assert kb (list widget 7) 'CxUniverse {:strength :default})
    (v/assert kb (list 'not (list widget 7)) 'CxUniverse {:strength :default})
    (is (seq (v/contradictions kb)) "the ordinary contradiction reader sees it")
    (is (= {:status :audited :candidate-count 1}
           (sans-meter (v/kb-integrity kb #{7} 'CxUniverse)))
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
        (is (= {:type :bad-args :op 'kb-integrity
                :arg :candidate-terms}
               (ex-data e))))))
  (try
    (v/kb-integrity kb #{'?x} 'CxUniverse)
    (is false "an open term would turn the check into an enumerator")
    (catch clojure.lang.ExceptionInfo e
      (is (= {:type :bad-args :op 'kb-integrity
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
           (sans-meter (v/kb-integrity kb #{7} CxRight)))
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
        (is (= :definition-inconsistencies (:pass report)) (pr-str options))
        (is (not= :audited (:status report)))))))

(tu/deftest-kb a-truncated-sweep-names-the-pass-it-stopped-in
  (tu/with-terms [widget gadget]
    (v/assert kb (list 'genl widget gadget) 'CxUniverse)
    ;; the definition pass runs first and spends nothing here, with no defnSufficient
    (is (= [:truncated :max-work :implicit-genl]
           ((juxt :status :reason :pass)
            (v/kb-integrity kb #{widget} 'CxUniverse
                            {:categories #{:definition-inconsistencies :implicit-genl}
                             :max-work 1}))))))

(tu/deftest-kb a-nil-bound-is-no-bound-and-a-bad-one-is-refused
  (is (= {:status :audited :candidate-count 0}
         (sans-meter (v/kb-integrity kb #{} 'CxUniverse {:max-work nil :max-ms nil :max-results nil}))))
  (doseq [options [{:max-work -1} {:max-ms "5"} {:max-results 1.5}
                   {:categories [:implicit-genl]} {:categories #{:not-a-category}}]]
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/kb-integrity kb #{} 'CxUniverse options)))]
      (is (= [:unknown-option :bad-value] ((juxt :type :mismatch) (ex-data e)))
          (pr-str options)))))

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
    (let [observed (atom 0)
          second-candidate? #(and (= qualifies (first %)) (= 8 (second %)))]
      (v/add-evaluatable kb qualifies (constantly true))
      (v/add-evaluatable kb required (constantly false))
      (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
      (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
      (with-skewed-clock
        (fn [skew]
          (v/add-prover kb (clock-moving-prover second-candidate? skew))
          (v/add-prover kb (observing-applicability-prover second-candidate? observed))
          (let [report (v/kb-integrity kb #{7 8} 'CxUniverse {:max-results 1 :max-ms 200})]
            (is (= :truncated (:status report)))
            (is (= :max-ms (:reason report)))
            (is (= [[widget 7]]
                   (mapv (juxt :collection :term)
                         (:definition-inconsistencies report)))
                "the first candidate's completed finding survives the second's timeout")
            (is (= 1 (count (:definition-inconsistencies report)))
                "time exhaustion cannot leak progress beyond the full result allowance")
            (is (zero? @observed)
                "dispatch traversal stopped before the prover after the elapsed callback")))))))

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

(tu/deftest-kb a-clean-sweep-at-zero-results-is-complete
  (is (= {:status :audited :candidate-count 0}
         (sans-meter (v/kb-integrity kb #{} 'CxUniverse {:max-results 0})))
      "an empty result allowance is not exhaustion when the sweep finds nothing"))

(tu/deftest-kb a-sweep-within-its-work-budget-finishes
  (is (= {:status :audited :candidate-count 0}
         (sans-meter (v/kb-integrity kb #{} 'CxUniverse {:categories #{:implicit-genl} :max-work 0})))
      "a sweep that spends no unit finishes at a budget of none"))

(tu/deftest-kb an-exact-definition-result-cap-is-complete
  (tu/with-terms [widget qualifies required]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
    (let [report (v/kb-integrity kb #{7} 'CxUniverse {:max-results 1})]
      (is (= :gap (:status report)))
      (is (= [[widget 7]]
             (mapv (juxt :collection :term) (:definition-inconsistencies report)))))))

(tu/deftest-kb an-exact-specified-result-cap-is-complete
  (tu/with-terms [likes person]
    (v/assert kb (list 'binary_predicate likes) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likes person) 'CxUniverse)
    (let [report (v/kb-integrity kb #{} 'CxUniverse {:max-results 1 :categories without-missing-arg})]
      (is (= :gap (:status report)))
      (is (= #{['predAllSpecified likes person]}
             (set (keys (:all-specified-violations report))))))))

(tu/deftest-kb source-context-updates-count-as-one-specified-result
  (tu/with-terms [notes item_kind Base Child CxA CxB]
    (doseq [form [(list 'binary_predicate notes) (list 'unary_predicate item_kind)
                  (list 'arg notes 2 'thing) (list 'genlCx CxA 'CxUniverse)
                  (list 'genlCx CxB CxA)]]
      (v/assert kb form 'CxUniverse))
    (v/assert kb (list 'predAllSpecified notes item_kind) CxA)
    (v/assert kb (list 'predAllSpecified notes item_kind) CxB)
    (v/assert kb (list item_kind Base) CxA)
    (v/assert kb (list item_kind Child) CxB)
    (let [report (v/kb-integrity kb #{} CxB
                                 {:categories #{:all-specified-violations} :max-results 1})]
      (is (= :gap (:status report)) "two sources of one declaration do not exceed one result")
      (is (= {['predAllSpecified notes item_kind]
              {:status :audited :violations #{Base Child}}}
             (:all-specified-violations report))))))

(tu/deftest-kb opaque-chunk-overrun-is-observed-before-another-pull
  (tu/with-terms [widget chunkAnswers required]
    (let [produced (atom 0)]
      (v/add-evaluatable kb required (constantly false))
      (v/assert kb (list 'defnSufficient widget (list chunkAnswers '?x)) 'CxUniverse)
      (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
      (with-skewed-clock
        (fn [skew]
          (v/add-prover kb (chunked-answer-prover chunkAnswers skew produced))
          (let [report (v/kb-integrity kb #{7} 'CxUniverse {:max-ms 200})]
            (is (= :truncated (:status report)))
            (is (= :max-ms (:reason report)))
            (is (= 32 @produced)
                "one opaque chunk is one cooperative pull and may overrun before returning")
            (is (empty? (:definition-inconsistencies report []))
                "the elapsed post-pull checkpoint returns no unaudited answer")))))))

(tu/deftest-kb sweep-decomposes-global-censuses-into-focused-audits
  (tu/with-terms [widget qualifies required likes person]
    (v/add-evaluatable kb qualifies (constantly true))
    (v/add-evaluatable kb required (constantly false))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary widget (list required '?x)) 'CxUniverse)
    (v/assert kb (list 'binary_predicate likes) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likes person) 'CxUniverse)
    (let [original @#'res/matches-visible
          defn-queries (atom [])]
      (with-redefs [v/all-specified-violations
                    (fn [& _] (throw (ex-info "monolithic audit called" {})))
                    res/matches-visible
                    (fn [& args]
                      (let [sentence (second args)]
                        (when (#{'defnSufficient 'defnNecessary} (first sentence))
                          (swap! defn-queries conj sentence)))
                      (apply original args))]
        (let [report (v/kb-integrity kb #{7} 'CxUniverse)]
          (is (= :gap (:status report)))
          (is (contains? report :definition-inconsistencies))
          (is (contains? report :all-specified-violations))))
      ;; Two open reads are declaration censuses rather than domain reads: the sweep's
      ;; own collection census, and the definition provers' applicability check
      ;; (`provers/defn-declaring-colls`), which reads the declaring collections off the
      ;; functor posting, one per declaration, before any taxonomy walk.
      (let [censuses #{'(defnSufficient ?collection ?condition)
                       '(defnSufficient ?coll ?cond)
                       '(defnNecessary ?coll ?cond)}]
        (is (contains? (set @defn-queries) '(defnSufficient ?collection ?condition))
            "the sweep reads its collection census")
        (is (every? censuses (filter #(sx/variable? (second %)) @defn-queries))
            (str "only the declaration censuses leave the collection open: "
                 (pr-str @defn-queries)))
        (is (every? #(or (censuses %) (not (sx/variable? (second %))))
                    @defn-queries)
            "every definition validation after the censuses names one collection")))))

(tu/deftest-kb specified-audit-stream-pulls-one-declaration-at-a-time
  (tu/with-terms [likesA peopleA likesB peopleB]
    (doseq [pred [likesA likesB]]
      (v/assert kb (list 'binary_predicate pred) 'CxUniverse))
    (doseq [coll [peopleA peopleB]]
      (v/assert kb (list 'unary_predicate coll) 'CxUniverse))
    (v/assert kb (list 'predAllSpecified likesA peopleA) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likesB peopleB) 'CxUniverse)
    (let [original @#'predall/specified-violations
          calls    (atom [])]
      (with-redefs [predall/specified-violations
                    (fn [& args]
                      (swap! calls conj [(second args) (nth args 2)])
                      (apply original args))]
        (let [audits (predall/specified-declaration-audits kb 'CxUniverse)]
          (is (some? (first audits)))
          (is (= 1 (count @calls)) "the first pull performs exactly one focused audit")
          (is (some? (first (rest audits))))
          (is (= 2 (count @calls)) "the second audit waits for the second pull"))))))

(tu/deftest-kb mixed-bounds-stop-after-the-first-over-cap-audit
  (tu/with-terms [likesA peopleA likesB peopleB likesC peopleC]
    (doseq [pred [likesA likesB likesC]]
      (v/assert kb (list 'binary_predicate pred) 'CxUniverse))
    (doseq [coll [peopleA peopleB peopleC]]
      (v/assert kb (list 'unary_predicate coll) 'CxUniverse))
    ;; Stored against content order, so a cut that kept arrival order keeps likesC.
    (v/assert kb (list 'predAllSpecified likesC peopleC) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likesB peopleB) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likesA peopleA) 'CxUniverse)
    (let [[first-pred first-indep]
          (first (content-order [[likesA peopleA] [likesB peopleB] [likesC peopleC]]))
          original @#'predall/specified-violations
          calls    (atom [])]
      (with-redefs [predall/specified-violations
                    (fn [& args]
                      (swap! calls conj [(second args) (nth args 2)])
                      (apply original args))]
        (let [report (v/kb-integrity kb #{} 'CxUniverse
                                     {:max-results 1 :max-work 10000 :max-ms 1000})]
          (is (= :truncated (:status report)))
          (is (= :max-results (:reason report)))
          (is (= {['predAllSpecified first-pred first-indep]
                  {:status :gap :gap :missing-slot-typing
                   :pred first-pred :position 2}}
                 (:all-specified-violations report)))
          (is (= 1 (count (:all-specified-violations report)))
              "the work and time options do not weaken the absolute result cap")
          (is (= 2 (count @calls))
              "the first over-cap audit is performed but not retained; the third never runs"))))))

(tu/deftest-kb elapsed-specified-audit-keeps-earlier-declaration-gaps
  (tu/with-terms [likesUntyped peopleA likesTyped peopleB person Alice]
    (with-skewed-clock
      (fn [skew]
        (v/assert kb (list 'binary_predicate likesUntyped) 'CxUniverse)
        (v/assert kb (list 'binary_predicate likesTyped) 'CxUniverse)
        (v/assert kb (list 'unary_predicate peopleA) 'CxUniverse)
        (v/assert kb (list 'unary_predicate peopleB) 'CxUniverse)
        (v/assert kb (list 'predAllSpecified likesUntyped peopleA) 'CxUniverse)
        (v/assert kb (list 'predAllSpecified likesTyped peopleB) 'CxUniverse)
        ;; The audit reads declarations in content order: make its first row a gap and its
        ;; second row enter the clock-moving callback.
        (let [[[first-pred first-indep] [second-pred second-indep]]
              (content-order [[likesUntyped peopleA] [likesTyped peopleB]])
              second-declaration? #(= second-indep (first %))]
          (v/assert kb (list 'unary_predicate person) 'CxUniverse)
          (v/assert kb (list 'arg second-pred 2 person) 'CxUniverse)
          (v/assert kb (list second-indep Alice) 'CxUniverse)
          (v/add-prover kb (clock-moving-prover second-declaration? skew))
          (let [report (v/kb-integrity kb #{} 'CxUniverse {:max-ms 200})]
            (is (= :truncated (:status report)))
            (is (= :max-ms (:reason report)))
            (is (= {['predAllSpecified first-pred first-indep]
                    {:status :gap :gap :missing-slot-typing
                     :pred first-pred :position 2}}
                   (:all-specified-violations report))
                "the completed first declaration survives exhaustion in the second")))))))

(tu/deftest-kb elapsed-source-context-audit-retains-the-completed-context
  (tu/with-terms [notes item_kind Base Child CxA CxB]
    (doseq [form [(list 'binary_predicate notes) (list 'unary_predicate item_kind)
                  (list 'arg notes 2 'thing) (list 'genlCx CxA 'CxUniverse)
                  (list 'genlCx CxB CxA)]]
      (v/assert kb form 'CxUniverse))
    (v/assert kb (list 'predAllSpecified notes item_kind) CxA)
    (v/assert kb (list 'predAllSpecified notes item_kind) CxB)
    (v/assert kb (list item_kind Base) CxA)
    (v/assert kb (list item_kind Child) CxB)
    (with-skewed-clock
      (fn [skew]
        (let [original @#'predall/specified-violations]
          (with-redefs [predall/specified-violations
                        (fn [kb pred indep context & args]
                          (when (= CxB context)
                            (swap! skew + 3600000000000)
                            (budget/spend!))
                          (apply original kb pred indep context args))]
            (let [report (v/kb-integrity kb #{} CxB
                                         {:categories #{:all-specified-violations}
                                          :max-ms 60000})]
              (is (= :truncated (:status report)))
              (is (= :max-ms (:reason report)))
              (is (= {['predAllSpecified notes item_kind]
                      {:status :audited :violations #{Base}}}
                     (:all-specified-violations report))
                  "the first context's finding survives exhaustion in the next context"))))))))

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

;; ---- genl-arg-widening ----------------------------------------------------

(defn- declare-types!
  "Declare each of `types` a `unary_predicate`, so the undeclared-arity category does
  not report a fixture's types."
  [kb & types]
  (doseq [t types] (v/assert kb (list 'unary_predicate t) 'CxUniverse)))

(defn- declare-binary! [kb pred t1 t2]
  (v/assert kb (list 'binary_predicate pred) 'CxUniverse)
  (v/assert kb (list 'arg pred 1 t1) 'CxUniverse)
  (v/assert kb (list 'arg pred 2 t2) 'CxUniverse))

(tu/deftest-kb a-genl-edge-that-widens-an-argument-type-is-reported
  ;; The shape the sweep exists to find: every animal parentage would be an
  ;; originatorOf tuple, and originatorOf admits only persons.
  (tu/with-terms [animal person parentOf originatorOf Fido Rex]
    (v/assert kb (list 'genl person animal) 'CxUniverse)
    (declare-binary! kb parentOf animal animal)
    (declare-binary! kb originatorOf person person)
    (v/assert kb (list 'genl parentOf originatorOf) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{Fido Rex} 'CxUniverse)]
      (is (= :gap (:status report)))
      (is (= [{:spec parentOf :genl originatorOf :arg 1 :spec-type animal :genl-type person}
              {:spec parentOf :genl originatorOf :arg 2 :spec-type animal :genl-type person}]
             (:genl-arg-widening report)))
      (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing"))))

(tu/deftest-kb a-genl-edge-that-narrows-or-keeps-an-argument-type-is-not-reported
  (tu/with-terms [animal person fatherOf parentOf siblingOf relatedTo]
    (declare-types! kb animal person)
    (v/assert kb (list 'genl person animal) 'CxUniverse)
    (declare-binary! kb fatherOf person person)
    (declare-binary! kb parentOf animal animal)
    (declare-binary! kb siblingOf animal animal)
    (declare-binary! kb relatedTo animal animal)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)   ; narrower ⊆ wider
    (v/assert kb (list 'genl siblingOf relatedTo) 'CxUniverse) ; the same type
    (is (= {:status :audited :candidate-count 0}
           (sans-meter (v/kb-integrity kb #{} 'CxUniverse))))))

(tu/deftest-kb a-spec-that-declares-nothing-at-a-position-widens-nothing-there
  ;; With no declaration of its own, the spec's position is typed by the genl's
  ;; constraint alone, so there is no declared domain for the edge to widen.
  (tu/with-terms [animal person parentOf originatorOf]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 1 animal) 'CxUniverse)
    (declare-binary! kb originatorOf animal person)
    (v/assert kb (list 'genl parentOf originatorOf) 'CxUniverse)
    (is (= :audited (:status (v/kb-integrity kb #{} 'CxUniverse))))))

(tu/deftest-kb a-type-demanded-above-the-direct-genl-names-where-it-is-declared
  (tu/with-terms [animal person parentOf ancestorOf originatorOf]
    (declare-binary! kb parentOf animal animal)
    (v/assert kb (list 'binary_predicate ancestorOf) 'CxUniverse)
    (declare-binary! kb originatorOf person 'thing)
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl person animal) 'CxUniverse)
    (v/assert kb (list 'genl parentOf ancestorOf) 'CxUniverse)
    (v/assert kb (list 'genl ancestorOf originatorOf) 'CxUniverse)
    (is (= [{:spec parentOf :genl ancestorOf :arg 1 :spec-type animal :genl-type person
             :genl-type-declared-on originatorOf}]
           (:genl-arg-widening (v/kb-integrity kb #{} 'CxUniverse))))))

(tu/deftest-kb widening-findings-respect-context-visibility
  (tu/with-terms [animal person parentOf originatorOf CxHidden]
    (declare-types! kb animal person)
    (v/assert kb (list 'genl person animal) 'CxUniverse)
    (declare-binary! kb parentOf animal animal)
    (declare-binary! kb originatorOf person person)
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl parentOf originatorOf) CxHidden)
    (is (= :audited (:status (v/kb-integrity kb #{} 'CxUniverse)))
        "an edge asserted below the audit context is not seen from it")
    (is (= 2 (count (:genl-arg-widening (v/kb-integrity kb #{} CxHidden)))))))

(tu/deftest-kb widening-findings-truncate-under-every-bound
  (tu/with-terms [animal person parentOf originatorOf]
    (declare-types! kb animal person)
    (v/assert kb (list 'genl person animal) 'CxUniverse)
    (declare-binary! kb parentOf animal animal)
    (declare-binary! kb originatorOf person person)
    (v/assert kb (list 'genl parentOf originatorOf) 'CxUniverse)
    (testing "a result cap below the finding count keeps the completed prefix"
      (let [report (v/kb-integrity kb #{} 'CxUniverse {:max-results 1})]
        (is (= :truncated (:status report)))
        (is (= :max-results (:reason report)))
        (is (= [{:spec parentOf :genl originatorOf :arg 1 :spec-type animal
                 :genl-type person}]
               (:genl-arg-widening report)))))
    (testing "an exact result cap is complete"
      (is (= :gap (:status (v/kb-integrity kb #{} 'CxUniverse {:max-results 2})))))
    (testing "work exhaustion inside the pass is truncated, never audited, and keeps the
              findings completed before it"
      (let [run    #(v/kb-integrity kb #{} 'CxUniverse {:max-work %})
            needed (first (filter #(= :gap (:status (run %))) (range 0 1000)))]
        (is (some? needed) "some finite work budget completes the sweep")
        (let [partials (map run (range 0 needed))]
          (is (every? #(and (= :truncated (:status %)) (= :max-work (:reason %))) partials))
          (is (some #(= 1 (count (:genl-arg-widening %))) partials)
              "a budget exhausted between the two positions keeps the first finding"))))))

;; ---- not-under-thing ------------------------------------------------------

(tu/deftest-kb a-unary-predicate-with-no-genl-path-to-thing-is-reported
  (tu/with-terms [orphan_kind_fixture]
    (v/assert kb (list 'unary_predicate orphan_kind_fixture) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{orphan_kind_fixture} 'CxUniverse)]
      (is (= :gap (:status report)))
      (is (= [{:term orphan_kind_fixture}] (:not-under-thing report)))
      (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing"))))

(tu/deftest-kb a-unary-predicate-under-thing-is-not-reported
  (tu/with-terms [placed_kind_fixture nested_kind_fixture]
    (declare-types! kb 'thing)
    (v/assert kb (list 'unary_predicate placed_kind_fixture) 'CxUniverse)
    (v/assert kb (list 'unary_predicate nested_kind_fixture) 'CxUniverse)
    (v/assert kb (list 'genl placed_kind_fixture 'thing) 'CxUniverse)        ; directly
    (v/assert kb (list 'genl nested_kind_fixture placed_kind_fixture) 'CxUniverse) ; transitively
    (is (= {:status :audited :candidate-count 3}
           (sans-meter (v/kb-integrity kb #{placed_kind_fixture nested_kind_fixture 'thing}
                                       'CxUniverse)))
        "thing itself is never a finding")))

(tu/deftest-kb a-unary-predicate-outside-the-candidate-terms-is-not-reported
  (tu/with-terms [orphan_kind_fixture]
    (v/assert kb (list 'unary_predicate orphan_kind_fixture) 'CxUniverse)
    (is (= {:status :audited :candidate-count 1}
           (sans-meter (v/kb-integrity kb #{7} 'CxUniverse {:categories without-missing-arg})))
        "the caller-owned term set is the bound; the sweep enumerates no types")))

(tu/deftest-kb a-non-unary-term-is-not-reported
  (tu/with-terms [linksFixture relatesFixture]
    (v/assert kb (list 'binary_predicate linksFixture) 'CxUniverse)
    (v/assert kb (list 'binary_predicate relatesFixture) 'CxUniverse)
    (v/assert kb (list 'genl linksFixture relatesFixture) 'CxUniverse)
    (is (= {:status :audited :candidate-count 2}
           (sans-meter (v/kb-integrity kb #{linksFixture relatesFixture} 'CxUniverse
                                       {:categories without-missing-arg}))))))

(tu/deftest-kb not-under-thing-findings-respect-context-visibility
  (tu/with-terms [orphan_kind_fixture CxHidden]
    (declare-types! kb 'thing)
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'unary_predicate orphan_kind_fixture) 'CxUniverse)
    (v/assert kb (list 'genl orphan_kind_fixture 'thing) CxHidden)
    (is (= [{:term orphan_kind_fixture}]
           (:not-under-thing (v/kb-integrity kb #{orphan_kind_fixture} 'CxUniverse)))
        "a genl edge asserted below the audit context is not seen from it")
    (is (= :audited (:status (v/kb-integrity kb #{orphan_kind_fixture} CxHidden))))))

(tu/deftest-kb not-under-thing-findings-truncate-under-every-bound
  (tu/with-terms [orphan_kind_fixture stray_kind_fixture]
    (v/assert kb (list 'unary_predicate orphan_kind_fixture) 'CxUniverse)
    (v/assert kb (list 'unary_predicate stray_kind_fixture) 'CxUniverse)
    (let [terms    #{orphan_kind_fixture stray_kind_fixture}
          in-order (mapv (fn [t] {:term t}) (sort-by nm/print-key terms))]
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (v/kb-integrity kb terms 'CxUniverse {:max-results 1 :categories without-missing-arg})]
          (is (= :truncated (:status report)))
          (is (= :max-results (:reason report)))
          (is (= (subvec in-order 0 1) (:not-under-thing report)))))
      (testing "an exact result cap is complete"
        (let [report (v/kb-integrity kb terms 'CxUniverse {:max-results 2 :categories without-missing-arg})]
          (is (= :gap (:status report)))
          (is (= in-order (:not-under-thing report)))))
      (testing "work exhaustion inside the pass is truncated, never audited, and keeps the
                findings completed before it"
        (let [run    #(v/kb-integrity kb terms 'CxUniverse {:max-work % :categories without-missing-arg})
              needed (first (filter #(= :gap (:status (run %))) (range 0 1000)))]
          (is (some? needed) "some finite work budget completes the sweep")
          (let [partials (map run (range 0 (or needed 0)))]
            (is (every? #(and (= :truncated (:status %)) (= :max-work (:reason %)))
                        partials))
            (is (some #(= (subvec in-order 0 1) (:not-under-thing %)) partials)
                "a budget exhausted between the two terms keeps the first finding")))))))

;; ---- implicit-genl --------------------------------------------------------

(defn- two-partition-shape!
  "Assert the facts that produce a partition coverage gap: `thing` partitioned two ways,
  one part of the first partition placed under one part of the second, and `kind` placed
  under the other part of the second."
  [kb {:keys [tangible intangible spatiotemporal temporal atemporal kind]}]
  (v/assert kb (list 'partition 'thing tangible intangible) 'CxUniverse)
  (v/assert kb (list 'genl tangible spatiotemporal) 'CxUniverse)
  (v/assert kb (list 'genl spatiotemporal temporal) 'CxUniverse)
  (v/assert kb (list 'partition 'thing temporal atemporal) 'CxUniverse)
  (v/assert kb (list 'genl kind atemporal) 'CxUniverse))

(tu/deftest-kb a-type-separated-from-every-part-but-one-is-suggested-under-that-part
  (tu/with-terms [tangible_like intangible_like spatiotemporal_like temporal_like
                  atemporal_like novel_kind]
    (two-partition-shape! kb {:tangible tangible_like :intangible intangible_like
                              :spatiotemporal spatiotemporal_like :temporal temporal_like
                              :atemporal atemporal_like :kind novel_kind})
    (let [stated (list 'genl novel_kind intangible_like)]
      (v/assert kb stated 'CxUniverse)
      (v/retract! kb (v/handle-of kb stated 'CxUniverse))
      (let [before  (state-snapshot kb)
            report  (v/kb-integrity kb #{novel_kind} 'CxUniverse)
            [found & more] (:implicit-genl report)]
        (is (= :gap (:status report)))
        (is (nil? more) "exactly one suggestion")
        (is (= {:term novel_kind :genl intangible_like}
               (select-keys found [:term :genl]))
            "the retracted edge is suggested again")
        (is (= [(set (list 'partition 'thing tangible_like intangible_like))]
               (map set (:cover found)))
            "the evidence names the partition whose coverage forces the edge")
        (is (= [tangible_like] (map :part (:disjoint-from found)))
            "every other part is excluded")
        (is (= [(set (list 'partition 'thing temporal_like atemporal_like))]
               (map set (:grounds (first (:disjoint-from found)))))
            "the exclusion names the separation it rests on")
        (is (= before (state-snapshot kb)) "a suggestion asserts nothing")))))

(tu/deftest-kb categories-reach-a-candidate-pass-the-census-passes-would-starve
  (tu/with-terms [tangible_like intangible_like spatiotemporal_like temporal_like
                  atemporal_like novel_kind]
    (two-partition-shape! kb {:tangible tangible_like :intangible intangible_like
                              :spatiotemporal spatiotemporal_like :temporal temporal_like
                              :atemporal atemporal_like :kind novel_kind})
    (let [run    #(v/kb-integrity kb #{novel_kind} 'CxUniverse %)
          only   #{:implicit-genl}
          needed (first (filter #(not= :truncated (:status (run {:categories only :max-work %})))
                                (range 0 2000)))]
      (is (= [:implicit-genl] (keys (dissoc (run {:categories only}) :status :candidate-count :work :elapsed-ms)))
          "the other categories' passes do not run")
      (is (some? needed))
      (is (= [novel_kind] (map :term (:implicit-genl (run {:categories only :max-work needed})))))
      (is (= :truncated (:status (run {:max-work needed})))
          "every category at the same budget spends it in the census passes ahead"))))

(tu/deftest-kb a-stated-or-derivable-genl-is-not-suggested
  (tu/with-terms [tangible_like intangible_like spatiotemporal_like temporal_like
                  atemporal_like novel_kind abstract_kind]
    (two-partition-shape! kb {:tangible tangible_like :intangible intangible_like
                              :spatiotemporal spatiotemporal_like :temporal temporal_like
                              :atemporal atemporal_like :kind novel_kind})
    (v/assert kb (list 'genl novel_kind intangible_like) 'CxUniverse)        ; stated
    (v/assert kb (list 'genl abstract_kind novel_kind) 'CxUniverse)          ; derivable
    (is (nil? (:implicit-genl (v/kb-integrity kb #{novel_kind abstract_kind}
                                              'CxUniverse))))))

(tu/deftest-kb a-type-left-with-two-candidate-parts-is-not-suggested
  (tu/with-terms [first_part second_part third_part loose_kind narrowed_kind disjoint_kind]
    (v/assert kb (list 'partition 'thing first_part second_part third_part) 'CxUniverse)
    (doseq [k [loose_kind narrowed_kind disjoint_kind]]
      (v/assert kb (list 'genl k 'thing) 'CxUniverse))
    (v/assert kb (list 'disjoint narrowed_kind first_part) 'CxUniverse)
    (v/assert kb (list 'disjoint disjoint_kind first_part) 'CxUniverse)
    (v/assert kb (list 'disjoint disjoint_kind second_part) 'CxUniverse)
    (let [report (v/kb-integrity kb #{loose_kind narrowed_kind disjoint_kind first_part}
                                 'CxUniverse)]
      (is (= [{:term disjoint_kind :genl third_part}]
             (map #(select-keys % [:term :genl]) (:implicit-genl report)))
          "disjoint from no part, or from one part of three, leaves two candidates and
           no suggestion; a part itself is never a suggestion")
      (is (= [[first_part [(list 'disjoint disjoint_kind first_part)]]
              [second_part [(list 'disjoint disjoint_kind second_part)]]]
             (sort-by (comp nm/print-key first)
                      (map (juxt :part #(mapv (partial apply list) (:grounds %)))
                           (:disjoint-from (first (:implicit-genl report))))))
          "an explicit disjoint pair is its own ground"))))

(tu/deftest-kb implicit-genl-findings-truncate-under-every-bound
  (tu/with-terms [left_part right_part one_kind two_kind]
    (declare-types! kb 'thing one_kind two_kind)
    (v/assert kb (list 'partition 'thing left_part right_part) 'CxUniverse)
    (doseq [k [one_kind two_kind]]
      (v/assert kb (list 'genl k 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint k left_part) 'CxUniverse))
    (let [terms    #{one_kind two_kind}
          in-order (mapv (fn [t] {:term t :genl right_part}) (sort-by nm/print-key terms))
          shown    #(mapv (fn [f] (select-keys f [:term :genl])) (:implicit-genl %))]
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (v/kb-integrity kb terms 'CxUniverse {:max-results 1})]
          (is (= :truncated (:status report)))
          (is (= :max-results (:reason report)))
          (is (= (subvec in-order 0 1) (shown report)))))
      (testing "an exact result cap is complete"
        (let [report (v/kb-integrity kb terms 'CxUniverse {:max-results 2})]
          (is (= :gap (:status report)))
          (is (= in-order (shown report)))))
      (testing "work exhaustion inside the pass is truncated, never audited, and keeps the
                findings completed before it"
        (let [run    #(v/kb-integrity kb terms 'CxUniverse {:max-work %})
              needed (first (filter #(= :gap (:status (run %))) (range 0 2000)))]
          (is (some? needed) "some finite work budget completes the sweep")
          (let [partials (map run (range 0 (or needed 0)))]
            (is (every? #(and (= :truncated (:status %)) (= :max-work (:reason %)))
                        partials))
            (is (some #(= (subvec in-order 0 1) (shown %)) partials)
                "a budget exhausted between the two terms keeps the first finding")))))))

;; ---- implicit-arity-class ---------------------------------------------------

(def ^:private arity-class-only
  "The implicit-arity-class pass alone, so a fixture's bare declarations report nothing
  else beside the finding under test."
  {:categories #{:implicit-arity-class}})

(tu/deftest-kb a-predicate-with-an-arity-and-no-class-is-suggested-the-class
  (tu/with-terms [pairOf pairedWith]
    (v/assert kb '(predicateTypeByArity binary_predicate 2) 'CxUniverse)
    (v/assert kb (list 'predicate pairOf) 'CxUniverse)
    (v/assert kb (list 'arity pairOf 2) 'CxUniverse)
    (v/assert kb (list 'predicate pairedWith) 'CxUniverse)
    (v/assert kb (list 'arity pairedWith 2) 'CxUniverse)
    (v/assert kb (list 'binary_predicate pairedWith) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{pairOf pairedWith} 'CxUniverse arity-class-only)]
      (is (= :gap (:status report)))
      (is (= [{:term pairOf :kind 'predicate :arity 2 :class 'binary_predicate
               :mapping '(predicateTypeByArity binary_predicate 2)}]
             (:implicit-arity-class report))
          "one finding, for the predicate whose class is not stated")
      (is (= before (state-snapshot kb)) "a suggestion asserts nothing"))
    (v/assert kb (list 'binary_predicate pairOf) 'CxUniverse)
    (is (= :audited (:status (v/kb-integrity kb #{pairOf pairedWith} 'CxUniverse
                                             arity-class-only)))
        "and none once the class is stated")))

(tu/deftest-kb a-function-is-suggested-its-function-class-and-never-a-predicate-one
  (tu/with-terms [PairFn pairRel]
    (v/assert kb '(predicateTypeByArity binary_predicate 2) 'CxUniverse)
    (v/assert kb '(functionTypeByArity binary_function 2) 'CxUniverse)
    (v/assert kb (list 'function PairFn) 'CxUniverse)
    (v/assert kb (list 'arity PairFn 2) 'CxUniverse)
    (v/assert kb (list 'relation pairRel) 'CxUniverse)
    (v/assert kb (list 'arity pairRel 2) 'CxUniverse)
    (is (= [{:term PairFn :kind 'function :arity 2 :class 'binary_function
             :mapping '(functionTypeByArity binary_function 2)}]
           (:implicit-arity-class
            (v/kb-integrity kb #{PairFn pairRel} 'CxUniverse arity-class-only)))
        "a relation of neither kind is suggested no class")))

(tu/deftest-kb an-arity-no-mapping-names-is-suggested-nothing
  (tu/with-terms [quadOf]
    (v/assert kb '(predicateTypeByArity binary_predicate 2) 'CxUniverse)
    (v/assert kb (list 'predicate quadOf) 'CxUniverse)
    (v/assert kb (list 'arity quadOf 4) 'CxUniverse)
    (is (= :audited (:status (v/kb-integrity kb #{quadOf} 'CxUniverse arity-class-only))))))

(tu/deftest-kb implicit-arity-class-findings-respect-context-visibility
  (tu/with-terms [pairOf CxHidden]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'predicate pairOf) 'CxUniverse)
    (v/assert kb (list 'arity pairOf 2) 'CxUniverse)
    (v/assert kb '(predicateTypeByArity binary_predicate 2) CxHidden)
    (is (= :audited (:status (v/kb-integrity kb #{pairOf} 'CxUniverse arity-class-only)))
        "a mapping asserted below the audit context is not seen from it")
    (is (= 1 (count (:implicit-arity-class (v/kb-integrity kb #{pairOf} CxHidden
                                                           arity-class-only)))))))

(tu/deftest-kb implicit-arity-class-findings-truncate-under-every-bound
  (tu/with-terms [pairOf pairedWith]
    (v/assert kb '(predicateTypeByArity binary_predicate 2) 'CxUniverse)
    (doseq [p [pairOf pairedWith]]
      (v/assert kb (list 'predicate p) 'CxUniverse)
      (v/assert kb (list 'arity p 2) 'CxUniverse))
    (let [terms    #{pairOf pairedWith}
          in-order (mapv (fn [t] {:term t :class 'binary_predicate}) (sort-by nm/print-key terms))
          shown    #(mapv (fn [f] (select-keys f [:term :class])) (:implicit-arity-class %))
          run      #(v/kb-integrity kb terms 'CxUniverse (merge arity-class-only %))]
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results] [(:status report) (:reason report)]))
          (is (= (subvec in-order 0 1) (shown report)))))
      (testing "an exact result cap is complete"
        (let [report (run {:max-results 2})]
          (is (= :gap (:status report)))
          (is (= in-order (shown report)))))
      (testing "work exhaustion inside the pass is truncated, never audited, and keeps the
                findings completed before it"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %}))) (range 0 2000)))]
          (is (some? needed) "some finite work budget completes the sweep")
          (let [partials (map #(run {:max-work %}) (range 0 (or needed 0)))]
            (is (every? #(and (= :truncated (:status %)) (= :max-work (:reason %)))
                        partials))
            (is (some #(= (subvec in-order 0 1) (shown %)) partials)
                "a budget exhausted between the two terms keeps the first finding")))))))

;; ---- orthogonal-over-separation ---------------------------------------------

(defn- shown-orthogonals
  "Each `:orthogonal-over-separation` finding of `report` as its `orthogonal` sentence
  and the set of the sentences separating the pair, unordered pairs read as sets."
  [report]
  (mapv (fn [{:keys [orthogonal separated-by]}]
          [(set (:sentence orthogonal)) (into #{} (map (comp set :sentence)) separated-by)])
        (:orthogonal-over-separation report)))

(tu/deftest-kb an-exception-over-a-partitioned-pair-is-reported
  (tu/with-terms [tangible_like intangible_like]
    (let [cover (list 'partition 'thing tangible_like intangible_like)
          orth  (list 'siblingDisjointException tangible_like intangible_like)]
      ;; the bare test KB loads no upper layer, so core.txt's edge is asserted here in its place
      (v/assert kb '(genl siblingDisjointException orthogonal) 'CxUniverse)
      (v/assert kb cover 'CxUniverse)
      (v/assert kb orth 'CxUniverse)
      (is (not (v/disjoint? kb tangible_like intangible_like))
          "the exception exempts the pair, so disjoint? cannot show the conflict")
      (let [before (state-snapshot kb)
            report (v/kb-integrity kb #{} 'CxUniverse)
            [found & more] (:orthogonal-over-separation report)]
        (is (= :gap (:status report)))
        (is (nil? more) "exactly one finding")
        (is (= [[(set orth) #{(set cover)}]] (shown-orthogonals report))
            "the finding names the exception and the partition it undoes")
        (is (= (v/handle-of kb orth 'CxUniverse) (:handle (:orthogonal found)))
            "the exception is named by handle")
        (is (= [(v/handle-of kb cover 'CxUniverse)] (map :handle (:separated-by found)))
            "the separation is named by handle")
        (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing")))))

(tu/deftest-kb an-orthogonal-over-an-unseparated-pair-is-not-reported
  (tu/with-terms [spatial_like temporal_like]
    (declare-types! kb 'thing spatial_like temporal_like)
    (v/assert kb (list 'genl spatial_like 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporal_like 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal spatial_like temporal_like) 'CxUniverse)
    (is (= {:status :audited :candidate-count 0} (sans-meter (v/kb-integrity kb #{} 'CxUniverse))))))

(tu/deftest-kb every-form-of-stated-separation-is-reported
  (tu/with-terms [left_kind right_kind upper_left upper_right parent_kind kind_metatype
                  sib_a sib_b]
    (testing "an explicit disjoint over the pair"
      (v/assert kb (list 'disjoint left_kind right_kind) 'CxUniverse)
      (v/assert kb (list 'orthogonal left_kind right_kind) 'CxUniverse)
      (is (= [[(set (list 'orthogonal left_kind right_kind))
               #{(set (list 'disjoint left_kind right_kind))}]]
             (shown-orthogonals (v/kb-integrity kb #{} 'CxUniverse)))))
    (v/retract! kb (v/handle-of kb (list 'disjoint left_kind right_kind) 'CxUniverse))
    (testing "a separating declaration naming a supertype of each"
      (v/assert kb (list 'genl left_kind upper_left) 'CxUniverse)
      (v/assert kb (list 'genl right_kind upper_right) 'CxUniverse)
      (v/assert kb (list 'separating 'thing upper_left upper_right) 'CxUniverse)
      (is (= [[(set (list 'orthogonal left_kind right_kind))
               #{(set (list 'separating 'thing upper_left upper_right))}]]
             (shown-orthogonals (v/kb-integrity kb #{} 'CxUniverse)))))
    (v/retract! kb (v/handle-of kb (list 'separating 'thing upper_left upper_right)
                                'CxUniverse))
    (testing "a sibling_disjoint parent"
      (v/assert kb (list 'genl sib_a parent_kind) 'CxUniverse)
      (v/assert kb (list 'genl sib_b parent_kind) 'CxUniverse)
      (v/assert kb (list 'sibling_disjoint parent_kind) 'CxUniverse)
      (v/assert kb (list 'orthogonal sib_a sib_b) 'CxUniverse)
      (is (some #(= [(set (list 'orthogonal sib_a sib_b))
                     #{(set (list 'sibling_disjoint parent_kind))}] %)
                (shown-orthogonals (v/kb-integrity kb #{} 'CxUniverse)))))
    (testing "a disjoint_metatype holding both"
      (v/assert kb (list 'disjoint_metatype kind_metatype) 'CxUniverse)
      (v/assert kb (list kind_metatype left_kind) 'CxUniverse)
      (v/assert kb (list kind_metatype right_kind) 'CxUniverse)
      (is (some #(= [(set (list 'orthogonal left_kind right_kind))
                     #{(set (list 'disjoint_metatype kind_metatype))
                       (set (list kind_metatype left_kind))
                       (set (list kind_metatype right_kind))}] %)
                (shown-orthogonals (v/kb-integrity kb #{} 'CxUniverse)))))))

(tu/deftest-kb orthogonal-over-separation-findings-respect-context-visibility
  (tu/with-terms [tangible_like intangible_like CxHidden]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'orthogonal tangible_like intangible_like) 'CxUniverse)
    (v/assert kb (list 'partition 'thing tangible_like intangible_like) CxHidden)
    (is (= :audited (:status (v/kb-integrity kb #{} 'CxUniverse)))
        "a separation asserted below the audit context is not seen from it")
    (is (= 1 (count (:orthogonal-over-separation (v/kb-integrity kb #{} CxHidden)))))))

(tu/deftest-kb orthogonal-over-separation-findings-truncate-under-every-bound
  (tu/with-terms [left_part right_part middle_part]
    (v/assert kb (list 'partition 'thing left_part middle_part right_part) 'CxUniverse)
    (v/assert kb (list 'orthogonal left_part middle_part) 'CxUniverse)
    (v/assert kb (list 'orthogonal middle_part right_part) 'CxUniverse)
    (testing "a result cap below the finding count keeps the completed prefix"
      (let [report (v/kb-integrity kb #{} 'CxUniverse {:max-results 1})]
        (is (= :truncated (:status report)))
        (is (= :max-results (:reason report)))
        (is (= 1 (count (:orthogonal-over-separation report))))))
    (testing "an exact result cap is complete"
      (is (= 2 (count (:orthogonal-over-separation
                       (v/kb-integrity kb #{} 'CxUniverse {:max-results 2}))))))
    (testing "work exhaustion inside the pass is truncated, never audited, and keeps the
              findings completed before it"
      (let [run    #(v/kb-integrity kb #{} 'CxUniverse {:max-work %})
            needed (first (filter #(= :gap (:status (run %))) (range 0 2000)))]
        (is (some? needed) "some finite work budget completes the sweep")
        (let [partials (map run (range 0 (or needed 0)))]
          (is (every? #(and (= :truncated (:status %)) (= :max-work (:reason %))) partials))
          (is (some #(= 1 (count (:orthogonal-over-separation %))) partials)
              "a budget exhausted between the two orthogonals keeps the first finding"))))))

;; ---- twin-genls -------------------------------------------------------------

(tu/deftest-kb sibling-types-with-identical-genls-are-reported-as-twins
  (tu/with-terms [temporal_like aspatial_like acausal_like point_kind interval_kind]
    (doseq [k [point_kind interval_kind], g [temporal_like aspatial_like acausal_like]]
      (v/assert kb (list 'genl k g) 'CxUniverse))
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse {:categories #{:twin-genls}})]
      (is (= :gap (:status report)))
      (is (= [{:types (vec (sort-by nm/print-key [point_kind interval_kind]))
               :genls (vec (sort-by nm/print-key [temporal_like aspatial_like acausal_like]))}]
             (:twin-genls report))
          "the group and the genl set it shares, suggesting a missing common parent")
      (is (= before (state-snapshot kb)) "a suggestion asserts nothing"))))

(tu/deftest-kb a-default-sweep-skips-the-review-only-categories
  ;; The four review-only passes run when `:categories` names them, so a smell alone never
  ;; turns a sweep without `:categories` into `:gap`.
  (tu/with-terms [temporal_like aspatial_like acausal_like point_kind interval_kind]
    (declare-types! kb temporal_like aspatial_like acausal_like point_kind interval_kind)
    (doseq [k [point_kind interval_kind], g [temporal_like aspatial_like acausal_like]]
      (v/assert kb (list 'genl k g) 'CxUniverse))
    (is (= {:status :audited :candidate-count 0} (sans-meter (v/kb-integrity kb #{} 'CxUniverse)))
        "the twin pair is not read by a sweep without :categories")
    (is (= :gap (:status (v/kb-integrity kb #{} 'CxUniverse {:categories #{:twin-genls}})))
        "and is reported once :categories names :twin-genls")))

(tu/deftest-kb types-sharing-fewer-than-two-genls-besides-thing-or-differing-are-not-twins
  (tu/with-terms [temporal_like aspatial_like acausal_like one_kind two_kind wide_kind
                  narrow_kind]
    (doseq [k [one_kind two_kind]]
      (v/assert kb (list 'genl k 'thing) 'CxUniverse)
      (v/assert kb (list 'genl k temporal_like) 'CxUniverse))
    (doseq [g [temporal_like aspatial_like acausal_like]]
      (v/assert kb (list 'genl wide_kind g) 'CxUniverse))
    (doseq [g [temporal_like aspatial_like]]
      (v/assert kb (list 'genl narrow_kind g) 'CxUniverse))
    (is (nil? (:twin-genls (v/kb-integrity kb #{} 'CxUniverse {:categories #{:twin-genls}})))
        "one genl besides thing is no twin, and overlapping sets that differ are none")))

(tu/deftest-kb twin-genls-findings-respect-context-visibility
  (tu/with-terms [temporal_like aspatial_like point_kind interval_kind CxHidden]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (doseq [g [temporal_like aspatial_like]]
      (v/assert kb (list 'genl point_kind g) 'CxUniverse)
      (v/assert kb (list 'genl interval_kind g) CxHidden))
    (let [run #(:twin-genls (v/kb-integrity kb #{} % {:categories #{:twin-genls}}))]
      (is (nil? (run 'CxUniverse)) "edges asserted below the audit context are not seen")
      (is (= 1 (count (run CxHidden)))))))

(tu/deftest-kb twin-genls-findings-truncate-under-every-bound
  (tu/with-terms [left_like right_like up_like down_like a_kind b_kind c_kind d_kind]
    (doseq [k [a_kind b_kind], g [left_like right_like]]
      (v/assert kb (list 'genl k g) 'CxUniverse))
    (doseq [k [c_kind d_kind], g [up_like down_like]]
      (v/assert kb (list 'genl k g) 'CxUniverse))
    (let [run #(v/kb-integrity kb #{} 'CxUniverse (merge {:categories #{:twin-genls}} %))]
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results 1]
                 [(:status report) (:reason report) (count (:twin-genls report))]))))
      (testing "an exact result cap is complete"
        (is (= 2 (count (:twin-genls (run {:max-results 2}))))))
      (testing "work exhaustion is truncated, never audited"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %}))) (range 0 5000)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] [(:status %) (:reason %)])
                      (map #(run {:max-work %}) (range 0 (or needed 0))))))))))

;; ---- derivable-stated-edge --------------------------------------------------

(defn- shown-derivable
  "Each `:derivable-stated-edge` finding as its stated sentence, the path that derives it
  without the statement, and the set of the other sentences that state or separate it."
  [report]
  (mapv (fn [{:keys [stated path also-stated-by separated-by]}]
          [(apply list (:sentence stated)) path
           (into #{} (map (comp set :sentence)) (concat also-stated-by separated-by))])
        (:derivable-stated-edge report)))

(tu/deftest-kb a-genl-another-chain-derives-is-reported
  (tu/with-terms [low_kind mid_kind top_kind]
    (v/assert kb (list 'genl low_kind mid_kind) 'CxUniverse)
    (v/assert kb (list 'genl mid_kind top_kind) 'CxUniverse)
    (v/assert kb (list 'genl low_kind top_kind) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse {:categories #{:derivable-stated-edge}})]
      (is (= [[(list 'genl low_kind top_kind) [low_kind mid_kind top_kind] #{}]]
             (shown-derivable report))
          "only the shortcut edge is redundant, with the chain that derives it")
      (is (= before (state-snapshot kb)) "the audit retracts nothing"))))

(tu/deftest-kb a-genl-a-cover-also-installs-is-reported
  (tu/with-terms [whole_kind left_part right_part]
    (v/assert kb (list 'partition whole_kind left_part right_part) 'CxUniverse)
    (v/assert kb (list 'genl left_part whole_kind) 'CxUniverse)
    (is (= [[(list 'genl left_part whole_kind) nil
             #{(set (list 'partition whole_kind left_part right_part))}]]
           (shown-derivable (v/kb-integrity kb #{} 'CxUniverse
                                            {:categories #{:derivable-stated-edge}}))))))

(tu/deftest-kb a-disjoint-a-supertype-separation-derives-is-reported
  (tu/with-terms [upper_left upper_right left_kind right_kind]
    (v/assert kb (list 'genl left_kind upper_left) 'CxUniverse)
    (v/assert kb (list 'genl right_kind upper_right) 'CxUniverse)
    (v/assert kb (list 'disjoint upper_left upper_right) 'CxUniverse)
    (v/assert kb (list 'disjoint left_kind right_kind) 'CxUniverse)
    (is (= [[(list 'disjoint left_kind right_kind) nil
             #{(set (list 'disjoint upper_left upper_right))}]]
           (shown-derivable (v/kb-integrity kb #{} 'CxUniverse
                                            {:categories #{:derivable-stated-edge}})))
        "the inherited separation makes the narrower one redundant, not the reverse")))

(tu/deftest-kb a-disjoint-a-partition-states-is-reported
  (tu/with-terms [whole_kind left_part right_part]
    (v/assert kb (list 'partition whole_kind left_part right_part) 'CxUniverse)
    (v/assert kb (list 'disjoint left_part right_part) 'CxUniverse)
    (let [found (shown-derivable (v/kb-integrity kb #{} 'CxUniverse
                                                 {:categories #{:derivable-stated-edge}}))]
      (is (= 1 (count found)))
      (is (= #{(set (list 'partition whole_kind left_part right_part))}
             (nth (first found) 2))))))

(tu/deftest-kb a-stated-edge-nothing-else-derives-is-not-reported
  (tu/with-terms [low_kind top_kind left_kind right_kind]
    (v/assert kb (list 'genl low_kind top_kind) 'CxUniverse)
    (v/assert kb (list 'genl left_kind top_kind) 'CxUniverse)
    (v/assert kb (list 'genl right_kind top_kind) 'CxUniverse)
    (v/assert kb (list 'disjoint left_kind right_kind) 'CxUniverse)
    (is (nil? (:derivable-stated-edge
               (v/kb-integrity kb #{} 'CxUniverse {:categories #{:derivable-stated-edge}}))))))

(tu/deftest-kb derivable-stated-edge-findings-respect-context-visibility
  (tu/with-terms [low_kind mid_kind top_kind CxHidden]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl low_kind top_kind) 'CxUniverse)
    (v/assert kb (list 'genl low_kind mid_kind) CxHidden)
    (v/assert kb (list 'genl mid_kind top_kind) CxHidden)
    (let [run #(:derivable-stated-edge
                (v/kb-integrity kb #{} % {:categories #{:derivable-stated-edge}}))]
      (is (nil? (run 'CxUniverse)) "a chain asserted below the audit context is not seen")
      (is (= 1 (count (run CxHidden)))))))

(tu/deftest-kb derivable-stated-edge-findings-truncate-under-every-bound
  (tu/with-terms [a_kind b_kind c_kind d_kind]
    (v/assert kb (list 'genl a_kind b_kind) 'CxUniverse)
    (v/assert kb (list 'genl b_kind c_kind) 'CxUniverse)
    (v/assert kb (list 'genl c_kind d_kind) 'CxUniverse)
    (v/assert kb (list 'genl a_kind c_kind) 'CxUniverse)
    (v/assert kb (list 'genl b_kind d_kind) 'CxUniverse)
    (let [run #(v/kb-integrity kb #{} 'CxUniverse
                               (merge {:categories #{:derivable-stated-edge}} %))]
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results 1]
                 [(:status report) (:reason report)
                  (count (:derivable-stated-edge report))]))))
      (testing "an exact result cap is complete"
        (is (= 2 (count (:derivable-stated-edge (run {:max-results 2}))))))
      (testing "work exhaustion is truncated, never audited"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %}))) (range 0 5000)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] [(:status %) (:reason %)])
                      (map #(run {:max-work %}) (range 0 (or needed 0))))))))))

;; ---- disjoint-could-be-partition --------------------------------------------

(defn- shown-partitions
  "Each `:disjoint-could-be-partition` finding as its disjoint sentence, the suggested
  partition and its basis."
  [report]
  (mapv (fn [{:keys [disjoint suggest basis]}]
          [(set (:sentence disjoint)) suggest basis])
        (:disjoint-could-be-partition report)))

(tu/deftest-kb a-disjoint-over-a-covering-is-suggested-as-a-partition
  (tu/with-terms [whole_kind left_part right_part]
    (v/assert kb (list 'covering whole_kind left_part right_part) 'CxUniverse)
    (v/assert kb (list 'disjoint left_part right_part) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse
                                 {:categories #{:disjoint-could-be-partition}})]
      (is (= [[(set (list 'disjoint left_part right_part))
               (apply list 'partition whole_kind (sort-by nm/print-key [left_part right_part]))
               :covering]]
             (shown-partitions report)))
      (is (= [(set (list 'covering whole_kind left_part right_part))]
             (map set (:cover (first (:disjoint-could-be-partition report)))))
          "the finding names the covering it rests on")
      (is (= before (state-snapshot kb)) "a suggestion asserts nothing"))))

(tu/deftest-kb a-disjoint-over-the-only-two-specs-is-suggested-as-a-partition
  (tu/with-terms [parent_kind left_kind right_kind]
    (v/assert kb (list 'genl left_kind parent_kind) 'CxUniverse)
    (v/assert kb (list 'genl right_kind parent_kind) 'CxUniverse)
    (v/assert kb (list 'disjoint left_kind right_kind) 'CxUniverse)
    (is (= [[(set (list 'disjoint left_kind right_kind))
             (apply list 'partition parent_kind (sort-by nm/print-key [left_kind right_kind]))
             :sole-specs]]
           (shown-partitions (v/kb-integrity kb #{} 'CxUniverse
                                             {:categories #{:disjoint-could-be-partition}}))))))

(tu/deftest-kb a-disjoint-with-no-known-cover-or-already-partitioned-is-not-suggested
  (tu/with-terms [parent_kind left_kind right_kind third_kind whole_kind a_part b_part
                  c_part]
    (testing "a parent with a third spec and no covering"
      (doseq [k [left_kind right_kind third_kind]]
        (v/assert kb (list 'genl k parent_kind) 'CxUniverse))
      (v/assert kb (list 'disjoint left_kind right_kind) 'CxUniverse))
    (testing "a three-part covering whose third part is not separated from the pair"
      (v/assert kb (list 'covering whole_kind a_part b_part c_part) 'CxUniverse)
      (v/assert kb (list 'disjoint a_part b_part) 'CxUniverse))
    (is (nil? (:disjoint-could-be-partition
               (v/kb-integrity kb #{} 'CxUniverse
                               {:categories #{:disjoint-could-be-partition}}))))
    (testing "a pair already partitioned"
      (v/assert kb (list 'partition parent_kind left_kind right_kind) 'CxUniverse)
      (is (not-any? #(= parent_kind (second (second %)))
                    (shown-partitions (v/kb-integrity
                                       kb #{} 'CxUniverse
                                       {:categories #{:disjoint-could-be-partition}})))))))

(tu/deftest-kb a-disjoint-over-a-pairwise-separated-covering-names-every-part
  (tu/with-terms [whole_kind a_part b_part c_part]
    (v/assert kb (list 'covering whole_kind a_part b_part c_part) 'CxUniverse)
    (v/assert kb (list 'disjoint a_part b_part) 'CxUniverse)
    (v/assert kb (list 'disjoint a_part c_part) 'CxUniverse)
    (v/assert kb (list 'disjoint b_part c_part) 'CxUniverse)
    (let [found (shown-partitions (v/kb-integrity kb #{} 'CxUniverse
                                                  {:categories #{:disjoint-could-be-partition}}))]
      (is (= 3 (count found)) "one finding per stated disjoint")
      (is (= #{(apply list 'partition whole_kind
                      (sort-by nm/print-key [a_part b_part c_part]))}
             (set (map second found))))
      (is (= #{:covering} (set (map last found)))))))

(tu/deftest-kb disjoint-could-be-partition-findings-truncate-under-every-bound
  (tu/with-terms [one_parent two_parent a_kind b_kind c_kind d_kind]
    (doseq [[p ks] [[one_parent [a_kind b_kind]] [two_parent [c_kind d_kind]]]]
      (doseq [k ks] (v/assert kb (list 'genl k p) 'CxUniverse))
      (v/assert kb (apply list 'disjoint ks) 'CxUniverse))
    (let [run #(v/kb-integrity kb #{} 'CxUniverse
                               (merge {:categories #{:disjoint-could-be-partition}} %))]
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results 1]
                 [(:status report) (:reason report)
                  (count (:disjoint-could-be-partition report))]))))
      (testing "an exact result cap is complete"
        (is (= 2 (count (:disjoint-could-be-partition (run {:max-results 2}))))))
      (testing "work exhaustion is truncated, never audited"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %}))) (range 0 5000)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] [(:status %) (:reason %)])
                      (map #(run {:max-work %}) (range 0 (or needed 0))))))))))

;; ---- missing-arg ------------------------------------------------------------

(defn- shown-missing
  "Each `:missing-arg` finding as `[predicate missing]`."
  [report]
  (mapv (juxt :predicate :missing) (:missing-arg report)))

(tu/deftest-kb a-declared-position-with-no-argument-type-is-reported
  (tu/with-terms [bareRel herdRel loose_kind]
    (v/assert kb (list 'binary_predicate bareRel) 'CxUniverse)
    (v/assert kb (list 'arg bareRel 1 'thing) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate herdRel) 'CxUniverse)
    (v/assert kb (list 'arityMin herdRel 2) 'CxUniverse)
    (v/assert kb (list 'arg herdRel 1 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate loose_kind) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse {:categories #{:missing-arg}})]
      (is (= :gap (:status report)))
      (is (= #{[bareRel [2]] [herdRel [2 :rest]] [loose_kind [1]]}
             (set (shown-missing report)))
          "each untyped position, and a variable-arity tail no rest form covers")
      (is (= before (state-snapshot kb)) "the audit declares nothing"))))

(tu/deftest-kb a-position-typed-by-any-declaration-form-is-not-reported
  (tu/with-terms [typedRel subRel herdRel placed_kind]
    (v/assert kb (list 'binary_predicate typedRel) 'CxUniverse)
    (v/assert kb (list 'arg typedRel 1 'thing) 'CxUniverse)
    (v/assert kb (list 'genlArg typedRel 2 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate subRel) 'CxUniverse)
    (v/assert kb (list 'genl subRel typedRel) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate herdRel) 'CxUniverse)
    (v/assert kb (list 'arityMin herdRel 2) 'CxUniverse)
    (v/assert kb (list 'arg herdRel 1 'thing) 'CxUniverse)
    (v/assert kb (list 'argAndRest herdRel 2 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate placed_kind) 'CxUniverse)
    (v/assert kb (list 'genl placed_kind 'thing) 'CxUniverse)
    (is (nil? (:missing-arg (v/kb-integrity kb #{} 'CxUniverse {:categories #{:missing-arg}})))
        "arg, genlArg, an inherited declaration, argAndRest and a type's own genl edge
         each type their positions")))

(tu/deftest-kb a-position-typed-where-the-relation-is-declared-is-not-reported
  ;; An arity mark can sit in CxUniverse while the declarations typing the positions sit
  ;; in a context below it, as an engine-placed arity class does.  The audit reads those
  ;; declarations from the context that states them, and still reports a position that
  ;; context leaves untyped, or one a context that cannot see them reads.
  (tu/with-terms [CxLow CxSide lowRel halfRel low_kind]
    (v/assert kb (list 'genlCx CxLow 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate lowRel) 'CxUniverse)
    (v/assert kb (list 'arg lowRel 1 'thing) CxLow)
    (v/assert kb (list 'arg lowRel 2 'thing) CxLow)
    (v/assert kb (list 'binary_predicate halfRel) 'CxUniverse)
    (v/assert kb (list 'arg halfRel 1 'thing) CxLow)
    (v/assert kb (list 'unary_predicate low_kind) 'CxUniverse)
    (v/assert kb (list 'genl low_kind 'thing) CxLow)
    (let [found (fn [context]
                  (set (filter (comp #{lowRel halfRel low_kind} first)
                               (shown-missing (v/kb-integrity kb #{} context
                                                              {:categories #{:missing-arg}})))))]
      (is (= #{[halfRel [2]]} (found 'CxUniverse))
          "the declarations below are read, and the position they leave open is reported")
      (is (= #{[halfRel [2]]} (found CxLow)) "as from the context stating them")
      (is (= #{[lowRel [1 2]] [halfRel [1 2]] [low_kind [1]]} (found CxSide))
          "a context that does not see the declarations reads none of them"))))

(tu/deftest-kb a-part-of-a-partition-is-declared-where-the-partition-is-stated
  ;; A `partition`, `covering` or `separating` declaration installs a `genl` edge out of
  ;; each part it names (`tax/installed-edges`), which types the part's one position as a
  ;; stated edge would.  A part whose only edge is that declaration's, stated in a context
  ;; below the audit context, is declared there.
  (doseq [functor '[partition covering separating]]
    (tu/with-terms [CxLow CxSide whole_kind left_kind right_kind]
      (v/assert kb (list 'genlCx CxLow 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'unary_predicate left_kind) 'CxUniverse)
      (v/assert kb (list 'unary_predicate right_kind) 'CxUniverse)
      (v/assert kb (list functor whole_kind left_kind right_kind) CxLow)
      (let [found (fn [context]
                    (set (filter (comp #{left_kind right_kind} first)
                                 (shown-missing (v/kb-integrity kb #{} context
                                                                {:categories #{:missing-arg}})))))]
        (is (= #{} (found 'CxUniverse))
            (str "a " functor " part is read where the " functor " is stated"))
        (is (= #{} (found CxLow)) (str "as from the context stating the " functor))
        (is (= #{[left_kind [1]] [right_kind [1]]} (found CxSide))
            (str "a context that does not see the " functor " reads no edge"))))))

;; ---- rule-macro -----------------------------------------------------------

(defn- macro-of
  "`[sentence macro declaration]` of each `:rule-macro` finding in `report`, sentences as
  lists so a test can compare them with the rule it wrote."
  [report]
  (mapv (fn [f] [(:sentence f) (:macro f) (:declaration f)]) (:rule-macro report)))

(defn- rule-macros
  "The `:rule-macro` findings a sweep run with that category alone reports in `context`."
  ([kb] (rule-macros kb 'CxUniverse))
  ([kb context]
   (macro-of (v/kb-integrity kb #{} context {:categories #{:rule-macro}}))))

(tu/deftest-kb a-preservation-rule-is-reported-as-the-declaration
  (tu/with-terms [empty_kind nonempty_kind]
    (let [down (list 'implies (list 'and (list empty_kind '?c) '(genl ?d ?c))
                     (list empty_kind '?d))
          up   (list 'implies (list 'and (list nonempty_kind '?d) '(genl ?d ?c))
                     (list nonempty_kind '?c))]
      (v/assert kb (list 'set/forwardRule down) 'CxUniverse)
      (v/assert kb (list 'set/forwardRule up) 'CxUniverse)
      (let [before (state-snapshot kb)
            report (v/kb-integrity kb #{} 'CxUniverse {:categories #{:rule-macro}})]
        (is (= :gap (:status report)))
        (is (= #{[(v/handle-of kb down 'CxUniverse) 'CxUniverse 'transitiveInArgInverse
                  (list 'transitiveInArgInverse empty_kind 1 'genl)]
                 [(v/handle-of kb up 'CxUniverse) 'CxUniverse 'transitiveInArg
                  (list 'transitiveInArg nonempty_kind 1 'genl)]}
               (set (map (juxt :rule :context :macro :declaration) (:rule-macro report)))))
        (is (= 2 (count (:rule-macro report))) "one finding per rule")
        (is (every? #(v/sentexes-matching kb (:sentence %) 'CxUniverse) (:rule-macro report))
            "the sentence is the rule as stored")
        (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing")))))

(tu/deftest-kb a-preservation-rule-names-its-position-and-relation
  (tu/with-terms [rankedAt needs_care partOfX]
    (v/assert kb (list 'ternary_predicate rankedAt) 'CxUniverse)
    (v/assert kb (list 'transitive partOfX) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list rankedAt '?a '?w '?b) (list partOfX '?w '?z))
                       (list rankedAt '?a '?z '?b))
              'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list needs_care '?w) (list partOfX '?p '?w))
                       (list needs_care '?p))
              'CxUniverse)
    (is (= #{(list 'transitiveInArg rankedAt 2 partOfX)
             (list 'transitiveInArgInverse needs_care 1 partOfX)}
           (set (map #(nth % 2) (rule-macros kb)))))))

(tu/deftest-kb a-suggested-preservation-declaration-concludes-what-its-rule-concluded
  (doseq [[rule-of fact-of goal-of]
          [[#(list 'implies (list 'and (list % '?c) '(genl ?d ?c)) (list % '?d))
            (fn [p _ super] (list p super)) (fn [p sub _] (list p sub))]
           [#(list 'implies (list 'and (list % '?d) '(genl ?d ?c)) (list % '?c))
            (fn [p sub _] (list p sub)) (fn [p _ super] (list p super))]]]
    (tu/with-terms [marked_kind sub_kind super_kind]
      (let [rule (rule-of marked_kind)]
        (v/assert kb (list 'genl sub_kind super_kind) 'CxUniverse)
        (v/assert kb (fact-of marked_kind sub_kind super_kind) 'CxUniverse)
        (v/assert kb (list 'set/forwardRule rule) 'CxUniverse)
        (let [[decl & more] (map #(nth % 2) (rule-macros kb))
              goal          (goal-of marked_kind sub_kind super_kind)]
          (is (nil? more))
          (is (v/ask? kb goal 'CxUniverse) "the rule concludes the goal")
          (v/retract! kb (v/handle-of kb rule 'CxUniverse))
          (is (not (v/ask? kb goal 'CxUniverse)) "with the rule gone nothing concludes it")
          (v/assert kb decl 'CxUniverse)
          (is (v/ask? kb goal 'CxUniverse) (str decl " concludes it in the rule's place")))))))

(tu/deftest-kb relation-algebra-rules-are-reported-as-their-marks
  (tu/with-terms [likesX partX betweenX childX parentX]
    (doseq [p [likesX partX childX parentX]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'ternary_predicate betweenX) 'CxUniverse)
    (v/assert kb (list 'implies (list likesX '?x '?y) (list likesX '?y '?x)) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list partX '?x '?y) (list partX '?y '?z))
                       (list partX '?x '?z))
              'CxUniverse)
    (v/assert kb (list 'implies (list betweenX '?x '?a '?b) (list betweenX '?x '?b '?a))
              'CxUniverse)
    (v/assert kb (list 'implies (list childX '?x '?y) (list parentX '?y '?x)) 'CxUniverse)
    (v/assert kb (list 'implies (list parentX '?x '?y) (list childX '?y '?x)) 'CxUniverse)
    (is (= #{(list 'symmetric likesX)
             (list 'transitive partX)
             (list 'commutativeInArgs betweenX 2 3)
             (list 'inverse childX parentX)
             (list 'inverse parentX childX)}
           (set (map #(nth % 2) (rule-macros kb)))))))

(tu/deftest-kb a-subsumption-rule-is-reported-as-genl
  (tu/with-terms [bird_kind warm_blooded_kind fatherX parentX]
    (v/assert kb (list 'binary_predicate fatherX) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentX) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule (list 'implies (list bird_kind '?x)
                                              (list warm_blooded_kind '?x)))
              'CxUniverse)
    (v/assert kb (list 'implies (list fatherX '?x '?y) (list parentX '?x '?y)) 'CxUniverse)
    (is (= #{(list 'genl bird_kind warm_blooded_kind) (list 'genl fatherX parentX)}
           (set (map #(nth % 2) (rule-macros kb)))))))

(defn- default-rule
  "The `set/defaultRule` `(implies (antecedent) (consequent))`, forward and backward."
  [ante conseq]
  (list 'set/defaultRule (list 'set/forwardRule (list 'implies ante conseq))))

(defn- shaped-of
  "`[declaration default-shaped?]` of each `:rule-macro` finding in `context`."
  ([kb] (shaped-of kb 'CxUniverse))
  ([kb context]
   (mapv (juxt :declaration (comp boolean :default-shaped))
         (:rule-macro (v/kb-integrity kb #{} context {:categories #{:rule-macro}})))))

(tu/deftest-kb a-default-rule-is-a-generator-or-default-shaped
  (tu/with-terms [pet_kind ownedBy fatherX parentX Somebody]
    (doseq [p [ownedBy fatherX parentX]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (default-rule (list pet_kind '?x) (list ownedBy '?x Somebody)) 'CxUniverse)
    (v/assert kb (default-rule (list fatherX '?x '?y) (list parentX '?x '?y)) 'CxUniverse)
    (is (= #{[(list 'predAllInstance ownedBy pet_kind Somebody) false]
             [(list 'genl fatherX parentX) true]}
           (set (shaped-of kb)))
        "a generator generates a default rule, so its shape is an ordinary finding; genl is
         monotonic, so the default subsumption rule with no known exception is reported
         as default-shaped")))

(tu/deftest-kb a-default-with-a-known-exception-is-not-reported
  (tu/with-terms [fatherX parentX relativeX penguin_kind bird_kind flies_kind CxLower Ann Bob]
    (doseq [p [fatherX parentX relativeX]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'genlCx CxLower 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl parentX relativeX) 'CxUniverse)
    (v/assert kb (default-rule (list fatherX '?x '?y) (list parentX '?x '?y)) 'CxUniverse)
    (v/assert kb (default-rule (list bird_kind '?x) (list flies_kind '?x)) 'CxUniverse)
    (is (= 2 (count (shaped-of kb))))
    (testing "a stored negation of a genl of the consequent, in a context below the rule's"
      (let [h (v/assert kb (list 'not (list relativeX Ann Bob)) CxLower)]
        (is (= [[(list 'genl bird_kind flies_kind) true]] (shaped-of kb)))
        (v/retract! kb h)))
    (testing "a rule concluding the negation of the consequent"
      (v/assert kb (list 'implies (list penguin_kind '?x) (list 'not (list flies_kind '?x)))
                'CxUniverse)
      (is (= [[(list 'genl fatherX parentX) true]] (shaped-of kb))))))

(tu/deftest-kb a-default-with-an-exceptWhen-is-not-reported
  (tu/with-terms [bird_kind flies_kind penguin_kind]
    (v/assert kb (list 'exceptWhen (list penguin_kind '?x)
                       (default-rule (list bird_kind '?x) (list flies_kind '?x)))
              'CxUniverse)
    (is (= [] (shaped-of kb)))))

(defn- acknowledged-macros
  "`[declaration reason]` of each `:rule-macro-review` finding in `context`."
  ([kb] (acknowledged-macros kb 'CxUniverse))
  ([kb context]
   (mapv (juxt :declaration :acknowledged)
         (:rule-macro-review (v/kb-integrity kb #{} context
                                             {:categories #{:rule-macro-review}})))))

(def ^:private sugar-reason
  "The reason core.txt's forward rule writes for a `declined_rule_macro` record."
  "Acknowledged via declined_rule_macro; no reason supplied.")

(defn- own
  "The `[declaration …]` rows of `rows` about `decl`, so a test on the upper ontology reads
  its own rule's suggestion beside whatever core.txt's rules suggest."
  [decl rows]
  (filterv #(= decl (first %)) rows))

(defn- core-kb
  "A KB holding the upper ontology, whose core.txt states the forward rule that makes
  `declined_rule_macro` sugar for `acknowledgedFinding`."
  []
  (doto (tu/fresh) (tu/load-core!)))

(tu/deftest-kb a-declined-suggestion-moves-to-review-until-the-record-goes
  (tu/with-cleared-kb [kb core-kb]
    (tu/with-terms [livesInX locatedInX]
      (doseq [p [livesInX locatedInX]]
        (v/assert kb (list 'binary_predicate p) 'CxUniverse))
      (v/assert kb (default-rule (list livesInX '?a '?p) (list locatedInX '?a '?p)) 'CxUniverse)
      (let [decl (list 'genl livesInX locatedInX)]
        (is (= [[decl true]] (own decl (shaped-of kb))))
        (is (= [] (own decl (acknowledged-macros kb))))
        (let [h (v/assert kb (list 'declined_rule_macro decl) 'CxUniverse)]
          (is (= [] (own decl (shaped-of kb))) "a declined suggestion is not a :rule-macro finding")
          (is (= [[decl sugar-reason]] (own decl (acknowledged-macros kb)))
              "it is a :rule-macro-review finding, with the sugar's reason")
          (is (nil? (:rule-macro-review (v/kb-integrity kb #{} 'CxUniverse)))
              "the review category runs only when named")
          (v/retract! kb h)
          (is (= [[decl true]] (own decl (shaped-of kb)))
              "retracting the record brings the finding back")
          (is (= [] (own decl (acknowledged-macros kb)))))))))

(tu/deftest-kb an-acknowledged-suggestion-carries-its-reason-into-review
  (tu/with-terms [livesInX locatedInX]
    (doseq [p [livesInX locatedInX]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (default-rule (list livesInX '?a '?p) (list locatedInX '?a '?p)) 'CxUniverse)
    (let [decl   (list 'genl livesInX locatedInX)
          reason "living somewhere is usually being there, and the default is meant"
          h      (v/assert kb (list 'acknowledgedFinding :rule-macro decl reason) 'CxUniverse)]
      (is (= [] (shaped-of kb)))
      (is (= [[decl reason]] (acknowledged-macros kb)))
      (testing "an acknowledgment under another category acknowledges nothing here"
        (v/retract! kb h)
        (v/assert kb (list 'acknowledgedFinding :rule-clash decl reason) 'CxUniverse)
        (is (= [[decl true]] (shaped-of kb)))
        (is (= [] (acknowledged-macros kb)))))))

(tu/deftest-kb a-declined-suggestion-is-read-from-the-rule-s-context
  (tu/with-cleared-kb [kb core-kb]
    (tu/with-terms [livesInX locatedInX CxTheory]
      (doseq [p [livesInX locatedInX]]
        (v/assert kb (list 'binary_predicate p) 'CxUniverse))
      (v/assert kb (list 'genlCx CxTheory 'CxUniverse) 'CxUniverse)
      (v/assert kb (default-rule (list livesInX '?a '?p) (list locatedInX '?a '?p)) 'CxUniverse)
      (let [decl (list 'genl livesInX locatedInX)]
        (v/assert kb (list 'declined_rule_macro decl) CxTheory)
        (is (= 1 (count (own decl (shaped-of kb))))
            "a record below the rule's context does not decline it")
        (is (= [] (own decl (acknowledged-macros kb))))))))

(defn- with-temp-dirs
  "`(f dir-a dir-b)` on two new temp directory paths, removed afterwards."
  [f]
  (let [dirs (mapv (fn [i] (.toFile (java.nio.file.Files/createTempDirectory
                                     (str "vaelii-declined-" i "-")
                                     (into-array java.nio.file.attribute.FileAttribute []))))
                   (range 2))
        rm!  (fn [^java.io.File d] (doseq [^java.io.File x (reverse (file-seq d))] (.delete x)))]
    (try (run! rm! dirs)
         (apply f (map #(.getPath ^java.io.File %) dirs))
         (finally (run! rm! dirs)))))

(tu/deftest-kb a-declined-suggestion-survives-a-text-export
  (tu/with-terms [livesInX locatedInX]
    (with-temp-dirs
      (fn [dir _]
        (tu/with-cleared-kb [src core-kb]
          (doseq [p [livesInX locatedInX]]
            (v/assert src (list 'binary_predicate p) 'CxUniverse))
          (v/assert src (default-rule (list livesInX '?a '?p) (list locatedInX '?a '?p))
                    'CxUniverse)
          (v/assert src (list 'declined_rule_macro (list 'genl livesInX locatedInX)) 'CxUniverse)
          (is (zero? (:skipped (v/export-text! src dir)))))
        (tu/with-cleared-kb [reloaded core-kb]
          (v/load-text! reloaded dir)
          (let [record (list 'declined_rule_macro (list 'genl livesInX locatedInX))]
            (is (seq (v/sentexes-matching reloaded record 'CxUniverse)))
            (is (= [] (own (second record) (shaped-of reloaded)))
                "the reloaded record still declines the suggestion")
            (v/retract! reloaded (v/handle-of reloaded record 'CxUniverse))
            (is (= 1 (count (own (second record) (shaped-of reloaded))))
                "the reloaded rule is the one the record named")))))))

(tu/deftest-kb a-monotonic-generator-shape-is-not-reported
  (tu/with-terms [pet_kind ownedBy Somebody]
    (v/assert kb (list 'binary_predicate ownedBy) 'CxUniverse)
    (v/assert kb (list 'implies (list pet_kind '?x) (list ownedBy Somebody '?x)) 'CxUniverse)
    (is (= [] (rule-macros kb))
        "predInstanceAll generates a default rule, so a monotonic one is not its spelling")))

(tu/deftest-kb near-miss-rules-are-not-reported
  (tu/with-terms [empty_kind other_kind needs_care begetsX likesX partX childX parentX
                  ownedBy mark_kind Bob]
    (doseq [p [begetsX likesX partX childX parentX ownedBy]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (doseq [r [;; an extra conjunct
               (list 'implies (list 'and (list empty_kind '?c) '(genl ?d ?c) (list other_kind '?d))
                     (list empty_kind '?d))
               ;; a relation nobody declared transitive
               (list 'implies (list 'and (list needs_care '?w) (list begetsX '?a '?w))
                     (list needs_care '?a))
               ;; a constant where the mark leaves the argument free
               (list 'implies (list likesX '?x Bob) (list likesX Bob '?x))
               ;; a different variable flow: euclidean, not transitive
               (list 'implies (list 'and (list partX '?x '?y) (list partX '?x '?z))
                     (list partX '?y '?z))
               ;; one direction of an inverse
               (list 'implies (list childX '?x '?y) (list parentX '?y '?x))
               ;; a conclusion the engine interprets as a mark
               (list 'implies (list mark_kind '?p) (list 'symmetric '?p))
               ;; a repeated variable
               (list 'implies (list ownedBy '?x '?x) (list likesX '?x '?x))
               ;; an inert rule
               (list 'set/inertRule (list 'implies (list other_kind '?x) (list mark_kind '?x)))]]
      (v/assert kb r 'CxUniverse))
    (is (= [] (rule-macros kb)))))

(tu/deftest-kb a-mark-rule-stated-in-one-theory-is-not-reported
  (tu/with-terms [CxTheory likesX empty_kind]
    (v/assert kb (list 'genlCx CxTheory 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate likesX) 'CxUniverse)
    (v/assert kb (list 'implies (list likesX '?x '?y) (list likesX '?y '?x)) CxTheory)
    (v/assert kb (list 'implies (list 'and (list empty_kind '?c) '(genl ?d ?c))
                       (list empty_kind '?d))
              CxTheory)
    (is (= [] (rule-macros kb)) "a rule CxUniverse cannot see is not visible from it")
    (is (= [(list 'transitiveInArgInverse empty_kind 1 'genl)]
           (map #(nth % 2) (rule-macros kb CxTheory)))
        "a mark is read from every context, so a theory's own symmetry rule stays a rule;
         a preservation declaration is read where it is stated")))

(tu/deftest-kb a-rule-beside-its-declaration-is-marked-stated
  (tu/with-terms [likesX]
    (v/assert kb (list 'binary_predicate likesX) 'CxUniverse)
    (v/assert kb (list 'implies (list likesX '?x '?y) (list likesX '?y '?x)) 'CxUniverse)
    (v/assert kb (list 'symmetric likesX) 'CxUniverse)
    (let [[f & more] (:rule-macro (v/kb-integrity kb #{} 'CxUniverse))]
      (is (nil? more))
      (is (= 'symmetric (:macro f)))
      (is (true? (:stated f)) "the declaration already says it, so the rule is redundant")
      (is (integer? (:rule f)))
      (is (= 'CxUniverse (:context f))))))

(tu/deftest-kb categories-run-the-rule-macro-pass-alone
  (tu/with-terms [likesX orphan_kind_fixture]
    (v/assert kb (list 'binary_predicate likesX) 'CxUniverse)
    (v/assert kb (list 'unary_predicate orphan_kind_fixture) 'CxUniverse)
    (v/assert kb (list 'implies (list likesX '?x '?y) (list likesX '?y '?x)) 'CxUniverse)
    (let [all  (v/kb-integrity kb #{orphan_kind_fixture} 'CxUniverse)
          only (v/kb-integrity kb #{orphan_kind_fixture} 'CxUniverse
                               {:categories #{:rule-macro}})]
      (is (= #{:not-under-thing :rule-macro}
             (set (keys (dissoc all :status :candidate-count :work :elapsed-ms)))))
      (is (= [:rule-macro] (keys (dissoc only :status :candidate-count :work :elapsed-ms))))
      (is (= (:rule-macro all) (:rule-macro only))))))

(tu/deftest-kb rule-macro-findings-truncate-under-every-bound
  (tu/with-terms [likesX metX]
    (doseq [p [likesX metX]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse)
      (v/assert kb (list 'implies (list p '?x '?y) (list p '?y '?x)) 'CxUniverse))
    (let [run      #(v/kb-integrity kb #{} 'CxUniverse (assoc % :categories #{:rule-macro}))
          in-order (mapv :declaration (:rule-macro (run {})))]
      (is (= 2 (count in-order)))
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results] ((juxt :status :reason) report)))
          (is (= (subvec in-order 0 1) (mapv :declaration (:rule-macro report))))))
      (testing "work exhaustion is truncated, never audited"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %}))) (range 0 5000)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] ((juxt :status :reason) (run {:max-work %})))
                      (range 0 (or needed 0)))))))))

;; ---- uncorresponded-function -----------------------------------------------

(tu/deftest-kb a-function-a-held-rule-applies-with-no-correspondence-is-reported
  (tu/with-terms [FruitFn SeedFn PitFn tagged ripe seedOf pitOf stoneOf]
    (doseq [f [FruitFn SeedFn PitFn]]
      (v/assert kb (list 'reifiable_function f) 'CxUniverse))
    (v/assert kb (list 'functionCorrespondingPredicate SeedFn seedOf) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate PitFn pitOf) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate PitFn stoneOf) 'CxUniverse)
    (let [h1 (v/assert kb (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)) 'CxUniverse)
          _  (v/assert kb (list 'implies (list tagged (list PitFn '?t)) (list ripe '?t)) 'CxUniverse)
          _  (v/assert kb (list 'implies (list tagged (list SeedFn '?t)) (list ripe '?t)) 'CxUniverse)
          before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse {:categories #{:uncorresponded-function}})]
      (is (= [{:function FruitFn :rules [h1]}] (:uncorresponded-function report))
          "the rules one and two correspondences respell are not held")
      (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing"))))

;; ---- undeclared-arity -----------------------------------------------------

(defn- undeclared
  "The `:undeclared-arity` terms a sweep run with that category alone reports in
  `context`."
  ([kb] (undeclared kb 'CxUniverse))
  ([kb context]
   (mapv :term (:undeclared-arity (v/kb-integrity kb #{} context
                                                  {:categories #{:undeclared-arity}})))))

(tu/deftest-kb a-genl-node-with-no-arity-is-reported
  (tu/with-terms [stray_kind loose_kind placed_kind below_kind]
    (v/assert kb (list 'unary_predicate placed_kind) 'CxUniverse)
    (v/assert kb (list 'genl below_kind placed_kind) 'CxUniverse)
    (v/assert kb (list 'genl stray_kind loose_kind) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse {:categories #{:undeclared-arity}})]
      (is (= :gap (:status report)))
      (is (= (mapv (fn [t] {:term t}) (sort-by nm/print-key [loose_kind stray_kind]))
             (:undeclared-arity report))
          "a subtype inherits its supertype's length, and both ends of an edge no length binds are findings")
      (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing"))))

(tu/deftest-kb a-genl-node-with-a-declared-arity-is-not-reported
  (tu/with-terms [typed_kind upper_kind linksX relatesX listsX gathersX arityX aritiesX
                  relP relQ Xa Xb Xc]
    (v/assert kb (list 'unary_predicate typed_kind) 'CxUniverse)
    (v/assert kb (list 'unary_predicate upper_kind) 'CxUniverse)
    (v/assert kb (list 'genl typed_kind upper_kind) 'CxUniverse)
    (v/assert kb (list 'binary_predicate linksX) 'CxUniverse)
    (v/assert kb (list 'binary_predicate relatesX) 'CxUniverse)
    (v/assert kb (list 'genl linksX relatesX) 'CxUniverse)
    (v/assert kb (list 'variable_arity listsX) 'CxUniverse)
    (v/assert kb (list 'variable_arity gathersX) 'CxUniverse)
    (v/assert kb (list 'genl listsX gathersX) 'CxUniverse)
    (v/assert kb (list 'arity arityX 3) 'CxUniverse)
    (v/assert kb (list 'arity aritiesX 3) 'CxUniverse)
    (v/assert kb (list 'genl arityX aritiesX) 'CxUniverse)
    (v/assert kb (list 'arity relQ 2) 'CxUniverse)
    (v/assert kb (list 'genl relP relQ) 'CxUniverse)
    (v/assert kb (list relP Xa Xb Xc) 'CxUniverse)
    (is (= [] (undeclared kb))
        "a unary_predicate, a binary_predicate, a variable_arity and an (arity P n)
         declaration each state an arity, and relP inherits relQ's")))

(tu/deftest-kb undeclared-arity-reads-the-edges-a-context-sees-and-an-arity-stated-anywhere
  (tu/with-terms [CxHidden stray_kind placed_kind hidden_kind loose_kind chainOf relatedTo]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl stray_kind placed_kind) 'CxUniverse)
    (v/assert kb (list 'unary_predicate stray_kind) CxHidden)
    (v/assert kb (list 'unary_predicate placed_kind) CxHidden)
    (v/assert kb (list 'genl hidden_kind loose_kind) CxHidden)
    (v/assert kb (list 'genl chainOf relatedTo) 'CxUniverse)
    (v/assert kb (list 'variable_arity chainOf) CxHidden)
    (v/assert kb (list 'variable_arity relatedTo) CxHidden)
    (is (= [] (undeclared kb))
        "an arity or a variable_arity stated below declares the node at CxUniverse, which sees no hidden_kind edge")
    (is (= (sort-by nm/print-key [hidden_kind loose_kind]) (undeclared kb CxHidden)))))

(tu/deftest-kb undeclared-arity-findings-truncate-under-every-bound
  (tu/with-terms [one_kind two_kind loose_kind]
    (doseq [k [one_kind two_kind]]
      (v/assert kb (list 'genl k loose_kind) 'CxUniverse))
    (let [run      #(v/kb-integrity kb #{} 'CxUniverse
                                    (assoc % :categories #{:undeclared-arity}))
          in-order (mapv (fn [t] {:term t}) (sort-by nm/print-key [one_kind two_kind loose_kind]))]
      (is (= in-order (:undeclared-arity (run {}))))
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results] ((juxt :status :reason) report)))
          (is (= (subvec in-order 0 1) (:undeclared-arity report)))))
      (testing "work exhaustion is truncated, never audited"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %}))) (range 0 5000)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] ((juxt :status :reason) (run {:max-work %})))
                      (range 0 (or needed 0)))))))))

;; ---- rule-clash -------------------------------------------------------------

(defn- clash-sweep
  "A sweep of `categories` alone, from `context`."
  ([kb categories] (clash-sweep kb categories 'CxUniverse))
  ([kb categories context] (v/kb-integrity kb #{} context {:categories categories})))

(defn- about
  "The rule-clash findings among `findings` whose sentences name a term of `terms`, so a
  test reads its own rules' pairs beside whatever the starter's rules pair."
  [terms findings]
  (filterv #(some (set terms) (flatten (:sentences %))) findings))

(tu/deftest-kb a-live-rule-clash-is-a-violation-the-default-sweep-reports
  (tu/with-terms [bird_kind penguin_kind flies]
    (let [yes    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse
                                {:direction :forward})
          no     (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x))
                                'CxUniverse {:direction :forward})
          before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse)
          mine   (about [flies] (:rule-clash report))
          e      (first mine)]
      (is (= :gap (:status report)))
      (is (= 1 (count mine)))
      (is (= :negation (:kind e)))
      (is (= #{yes no} (set (:rules e))))
      (is (= 'CxUniverse (:context e)))
      (is (false? (:excepted e)))
      (is (not (contains? e :inert)))
      (is (nil? (:rule-clash-review report)) "the review category runs only when named")
      (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing"))))

(tu/deftest-kb an-inert-rule-clash-is-review-only
  (tu/with-terms [bird_kind penguin_kind flies]
    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
    (let [doc (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x))
                             'CxUniverse {:direction :inert})]
      (is (empty? (about [flies] (:rule-clash (v/kb-integrity kb #{} 'CxUniverse))))
          "a pair with a set/inertRule is no violation")
      (is (empty? (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash})))))
      (let [e (first (about [flies] (:rule-clash-review (clash-sweep kb #{:rule-clash-review}))))]
        (is (= :negation (:kind e)))
        (is (contains? (set (:rules e)) doc))
        (is (true? (:inert e)))))))

(tu/deftest-kb an-excepted-rule-clash-is-review-only
  (tu/with-terms [bird_kind penguin_kind flies]
    (v/assert kb (list 'exceptWhen (list penguin_kind '?x)
                       (list 'set/defaultRule
                             (list 'set/forwardRule
                                   (list 'implies (list bird_kind '?x) (list flies '?x)))))
              'CxUniverse)
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) 'CxUniverse
                   {:direction :forward})
    (is (empty? (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash}))))
        "the exception names the other rule's case, so the clash is handled")
    (let [e (first (about [flies] (:rule-clash-review (clash-sweep kb #{:rule-clash-review}))))]
      (is (= :negation (:kind e)))
      (is (true? (:excepted e)))
      (is (not (contains? e :inert))))))

(tu/deftest-kb an-acknowledged-rule-clash-is-review-only
  ;; The subject names the pair as (RulePairFn (Quote R1) (Quote R2)), each rule quoted on
  ;; its own, in either order and under any variable names: the pair is matched by the
  ;; rules' canonical form.
  (tu/with-terms [bird_kind penguin_kind flies swims]
    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) 'CxUniverse
                   {:direction :forward})
    (let [reason "penguins are birds that do not fly, and the clash is the facts' to settle"
          pair   (list 'RulePairFn
                       (list 'Quote (list 'implies (list penguin_kind '?p) (list 'not (list flies '?p))))
                       (list 'Quote (list 'implies (list bird_kind '?b) (list flies '?b))))]
      (is (= 1 (count (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash}))))))
      (testing "an acknowledgment of another pair acknowledges nothing here"
        (let [other (list 'RulePairFn
                          (list 'Quote (list 'implies (list penguin_kind '?p) (list 'not (list swims '?p))))
                          (list 'Quote (list 'implies (list bird_kind '?b) (list flies '?b))))
              h     (v/assert kb (list 'acknowledgedFinding :rule-clash other reason) 'CxUniverse)]
          (is (= 1 (count (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash}))))))
          (v/retract! kb h)))
      (let [h (v/assert kb (list 'acknowledgedFinding :rule-clash pair reason) 'CxUniverse)]
        (is (empty? (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash}))))
            "an acknowledged pair is no violation")
        (let [e (first (about [flies] (:rule-clash-review (clash-sweep kb #{:rule-clash-review}))))]
          (is (= :negation (:kind e)))
          (is (= reason (:acknowledged e)) "the reason stays visible beside the pair")
          (is (false? (:excepted e)))
          (is (not (contains? e :inert))))
        (v/retract! kb h)
        (is (= 1 (count (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash})))))
            "retracting the acknowledgment brings the violation back")))))

(tu/deftest-kb a-rule-clash-is-read-from-a-context-that-sees-both-rules
  (tu/with-terms [bird_kind penguin_kind flies CxLeft CxRight CxBoth]
    (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxLeft) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxRight) 'CxUniverse)
    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) CxLeft {:direction :forward})
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) CxRight
                   {:direction :forward})
    (is (empty? (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash}))))
        "CxUniverse sees neither rule")
    (is (empty? (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash} CxLeft))))
        "CxLeft sees one")
    (let [e (first (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash} CxBoth))))]
      (is (= :negation (:kind e)))
      (is (= CxBoth (:context e)) "the audit context, where the pair is judged"))))

(tu/deftest-kb a-rule-clash-is-judged-and-acknowledged-at-the-audit-context
  ;; CxP and CxQ each see both rules; CxP sorts first, so a reading keyed on print order
  ;; would judge Q's pair in P.
  (tu/with-terms [bird_kind penguin_kind flies CxLeft CxRight CxP CxQ]
    (doseq [[c p] [[CxLeft 'CxUniverse] [CxRight 'CxUniverse]
                   [CxP CxLeft] [CxP CxRight] [CxQ CxLeft] [CxQ CxRight]]]
      (v/assert kb (list 'genlCx c p) 'CxUniverse))
    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) CxLeft {:direction :forward})
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) CxRight
                   {:direction :forward})
    (let [from-q #(mapv :context (about [flies] (:rule-clash (clash-sweep kb #{:rule-clash} CxQ))))
          census #(set (map :context (about [flies] (:pairs (:clashes (v/kb-quality kb {:limit 1000}))))))]
      (is (= [CxQ] (from-q)))
      (is (= #{CxP CxQ} (census)) "the census reports the pair at each maximal common descendant")
      (let [h (v/assert kb (list 'disjoint bird_kind penguin_kind) CxP)]
        (is (= [CxQ] (from-q)) "a separation Q does not see leaves Q's pair")
        (is (= #{CxQ} (census)) "the pair separated in P still clashes in Q")
        (v/retract! kb h))
      (let [h (v/assert kb (list 'disjoint bird_kind penguin_kind) CxQ)]
        (is (= [] (from-q)) "a separation Q sees drops the pair")
        (v/retract! kb h))
      (let [pair (list 'RulePairFn
                       (list 'Quote (list 'implies (list bird_kind '?x) (list flies '?x)))
                       (list 'Quote (list 'implies (list penguin_kind '?x) (list 'not (list flies '?x)))))
            h    (v/assert kb (list 'acknowledgedFinding :rule-clash pair "kept") CxP)]
        (is (= [CxQ] (from-q)) "an acknowledgment Q does not see acknowledges nothing in Q")
        (v/retract! kb h)))))

(tu/deftest-kb the-census-clashes-are-the-two-rule-clash-categories
  (tu/with-terms [bird_kind penguin_kind flies dog_kind barks]
    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) 'CxUniverse
                   {:direction :forward})
    (v/assert-rule kb [(list dog_kind '?x)] (list barks '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list bird_kind '?x)] (list 'not (list barks '?x)) 'CxUniverse
                   {:direction :inert})
    (let [census (about [flies barks] (:pairs (:clashes (v/kb-quality kb {:limit 1000}))))
          sweep  (clash-sweep kb #{:rule-clash :rule-clash-review})
          found  (about [flies barks] (concat (:rule-clash sweep) (:rule-clash-review sweep)))]
      (is (= 2 (count census)))
      (is (= (set census) (set (map #(dissoc % :inert) found)))
          "kb-quality's :clashes reading is the same pairing, unsplit"))))

(tu/deftest-kb a-partition-alone-separates-two-rule-conclusions
  ;; The `partition` is the KB's only separation, so the presence check that admits unary
  ;; conclusion pairs reads the covers or finds no pair.  The partition is asserted before
  ;; the rules and after them, each on a KB of its own.
  (tu/with-terms [animal_kind feline_kind canine_kind meows barks]
    (let [decls [#(v/assert % (list 'genl animal_kind 'thing) 'CxUniverse)
                 #(v/assert % (list 'partition animal_kind feline_kind canine_kind) 'CxUniverse)]
          rules [#(v/assert-rule % [(list meows '?x)] (list feline_kind '?x) 'CxUniverse
                                 {:direction :forward})
                 #(v/assert-rule % [(list barks '?x)] (list canine_kind '?x) 'CxUniverse
                                 {:direction :forward})]]
      (doseq [[order steps] [[:partition-first (concat decls rules)]
                             [:rules-first (concat rules decls)]]]
        (tu/with-neutral-kb [kb tu/fresh]
          (doseq [f steps] (f kb))
          (is (= [:disjoint] (mapv :kind (:pairs (:clashes (v/kb-quality kb))))) order))))))

(tu/deftest-kb rule-clash-findings-truncate-under-every-bound
  (tu/with-terms [bird_kind penguin_kind flies swims]
    (doseq [f [flies swims]]
      (v/assert-rule kb [(list bird_kind '?x)] (list f '?x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list f '?x)) 'CxUniverse
                     {:direction :forward}))
    (let [run      #(v/kb-integrity kb #{} 'CxUniverse (assoc % :categories #{:rule-clash}))
          in-order (mapv :rules (:rule-clash (run {})))]
      (is (= 2 (count (about [flies swims] (:rule-clash (run {}))))))
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (run {:max-results 1})]
          (is (= [:truncated :max-results] ((juxt :status :reason) report)))
          (is (= (subvec in-order 0 1) (mapv :rules (:rule-clash report))))))
      (testing "work exhaustion is truncated, never audited"
        (let [needed (first (filter #(= :gap (:status (run {:max-work %})))
                                    (range 0 1000000 50)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] ((juxt :status :reason) (run {:max-work %})))
                      (range 0 (or needed 0) 50))))))))

;; ---- taxonomy-island ----------------------------------------------------------

(defn- islands
  "The `:taxonomy-island` findings over `terms` a sweep of that category alone reports in
  `context`."
  ([kb terms] (islands kb terms 'CxUniverse))
  ([kb terms context]
   (filterv #(contains? (set terms) (:term %))
            (:taxonomy-island (v/kb-integrity kb #{} context
                                              {:categories #{:taxonomy-island}})))))

(tu/deftest-kb an-edged-type-that-misses-the-root-is-a-taxonomy-island
  ;; The root is the type the most nodes reach, so the placed chain makes it `thing`.
  (tu/with-terms [stray_kind loose_kind placed_kind below_kind]
    (let [census #(:islands (:taxonomy (v/kb-quality kb)))
          start  (census)]
      (v/assert kb (list 'genl placed_kind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl below_kind placed_kind) 'CxUniverse)
      (v/assert kb (list 'genl stray_kind loose_kind) 'CxUniverse)
      (let [before (state-snapshot kb)]
        (is (= (mapv (fn [t] {:term t :root 'thing}) (sort-by nm/print-key [loose_kind stray_kind]))
               (islands kb [stray_kind loose_kind placed_kind below_kind]))
            "both ends of the edge that reaches no root, and not the placed types")
        (is (= (+ start 2) (census)) "kb-quality's :islands counts the same nodes")
        (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing")))))

(tu/deftest-kb taxonomy-island-is-review-only-and-reads-the-edges-a-context-sees
  (tu/with-terms [CxHidden hidden_kind loose_kind placed_kind below_kind]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl placed_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl below_kind placed_kind) 'CxUniverse)
    (v/assert kb (list 'genl hidden_kind loose_kind) CxHidden)
    (is (nil? (:taxonomy-island (v/kb-integrity kb #{} CxHidden)))
        "a sweep without :categories skips the review-only pass")
    (is (= [] (islands kb [hidden_kind loose_kind])) "CxUniverse sees no edge of either")
    (is (= (sort-by nm/print-key [hidden_kind loose_kind])
           (mapv :term (islands kb [hidden_kind loose_kind] CxHidden))))))

(tu/deftest-kb a-relation-declaration-the-audit-context-does-not-see-keeps-its-island
  ;; The placed chain makes `thing` the root, as in the test above.
  (tu/with-terms [stray loose_kind placed_kind below_kind CxA CxB]
    (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'genl placed_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl below_kind placed_kind) 'CxUniverse)
    (v/assert kb (list 'genl stray loose_kind) CxA)
    (let [both (sort-by nm/print-key [stray loose_kind])]
      (is (= both (mapv :term (islands kb [stray loose_kind] CxA))))
      (v/assert kb (list 'binary_predicate stray) CxB)
      (is (= both (mapv :term (islands kb [stray loose_kind] CxA)))
          "CxA does not see the arity CxB states"))))

;; ---- stranded-declaration -----------------------------------------------------

(defn- stranded
  "The `:stranded-declaration` findings naming one of `preds` a sweep of that category
  alone reports in `context`."
  ([kb preds] (stranded kb preds 'CxUniverse))
  ([kb preds context]
   (filterv #(contains? (set preds) (:predicate %))
            (:stranded-declaration (v/kb-integrity kb #{} context
                                                   {:categories #{:stranded-declaration}})))))

(tu/deftest-kb a-declaration-past-its-predicate-s-arity-is-a-violation
  (tu/with-terms [parentOf a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 3 a_type) 'CxUniverse)
    (is (= [] (stranded kb [parentOf]))
        "nothing binds parentOf yet, so the position is a lower bound and not a mistake")
    (v/assert kb (list 'arg parentOf 1 a_type) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (let [before (state-snapshot kb)
          report (v/kb-integrity kb #{} 'CxUniverse)
          e      (first (filter #(= parentOf (:predicate %)) (:stranded-declaration report)))]
      (is (= :gap (:status report)) "the default sweep runs the pass")
      (is (= [(list 'arg parentOf 3 a_type)] (mapv :sentence (stranded kb [parentOf]))))
      (is (= {:predicate parentOf :position 3 :arity 2 :via parentOf :context 'CxUniverse}
             (select-keys e [:predicate :position :arity :via :context])))
      (is (string? (:message e)) "the entry point's own wording")
      (is (= (filterv #(= parentOf (:predicate %))
                      (:stranded (:declarations (v/kb-quality kb {:limit 1000}))))
             (stranded kb [parentOf]))
          "kb-quality's :declarations lists the same entries")
      (is (= before (state-snapshot kb)) "the audit stores, believes and files nothing"))))

(tu/deftest-kb stranded-declaration-reads-the-declarations-a-context-sees
  (tu/with-terms [CxHidden parentOf a_type]
    (v/assert kb (list 'genlCx CxHidden 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 3 a_type) CxHidden)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (is (= [] (stranded kb [parentOf])) "CxUniverse does not see the declaration")
    (is (= [CxHidden] (mapv :context (stranded kb [parentOf] CxHidden))))))
