;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.solve-context-test
  "`vaelii.impl.asp.solve-context`, `do/label` and `do/classify`: an `assumptionRule`
  never chains, an inert fact is stored and never believed, `do/label` writes one inert
  labeling context per optimal answer set and replaces its previous run, and `do/classify`
  aggregates them.  The solving tests are guarded on `asp?`; the representation tests run
  without a backend."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solve-context :as sc]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

;; ---- 1. assumptionRule: a choice rule, inference-inert ------------------

(deftest an-assumption-rule-is-distinct-from-its-bare-twin
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate color]
      (let [bare (v/assert kb (list 'implies (list candidate '?c) (list color '?c 'red)) 'CxUniverse {:direction :forward})
            asm  (v/assert kb (list 'set/assumptionRule
                                    (list 'implies (list candidate '?c) (list color '?c 'red)))
                           'CxUniverse)]
        (testing "the wrapper is part of identity, so they are two sentexes"
          (is (not= bare asm)))
        (testing "assumption? reads the record, true only for the wrapped one"
          (is (rules/assumption? (sentex-of kb asm)))
          (is (not (rules/assumption? (sentex-of kb bare)))))
        (testing "the choice is the record's effect, and a solve is its one engine"
          (is (= [:choose #{:solve}] ((juxt :effect :engines) (sentex-of kb asm))))
          (is (= [:derive #{:forward :backward}] ((juxt :effect :engines) (sentex-of kb bare)))))
        (testing "and re-asserting the same assumptionRule is idempotent"
          (is (= asm (v/assert kb (list 'set/assumptionRule
                                        (list 'implies (list candidate '?c) (list color '?c 'red)))
                               'CxUniverse))))))))

(deftest an-assumption-rule-does-not-forward-chain
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate color Item]
      (v/assert kb (list 'implies (list candidate '?c) (list color '?c 'red)) 'CxUniverse {:direction :forward})
      (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
                'CxUniverse)
      (v/assert kb (list candidate Item) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list color Item 'red) 'CxUniverse)) "bare rule fired")
      (is (empty? (v/sentexes-matching kb (list color Item 'blue) 'CxUniverse)) "assumptionRule did not"))))

;; ---- 2. inert facts: stored, inspectable, never believed ----------------

(deftest an-inert-fact-is-stored-but-never-believed
  ;; an inert fact is no premise, so the neutral teardown cannot retract it; this clears
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p Tom CxBox]
      (let [h (v/assert-inert kb (list p Tom) CxBox)]
        (testing "stored and inspectable"
          (is (some? (sentex-of kb h)))
          (is (some #(= (:id %) h) (v/sentexes-in-context kb CxBox))))
        (testing "but not a premise, so not believed"
          (is (not (v/believed? kb h)))
          (is (empty? (v/sentexes-matching kb (list p Tom) CxBox))))
        (testing "and retract! tears it down directly, though it was never a TMS datum"
          (is (= {:removed-sentexes 1 :removed-justifications 0} (v/retract! kb h)))
          (is (nil? (sentex-of kb h)))
          (is (empty? (v/sentexes-in-context kb CxBox)))
          (is (empty? (v/find-sentexes kb Tom))))))))

(deftest an-inert-fact-a-derivation-reached-is-inert-again-once-the-derivation-goes
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p q Tom CxBox]
      (let [h  (v/assert-inert kb (list p Tom) CxBox)
            _  (v/assert kb (list 'set/forwardRule (list 'implies (list q '?x) (list p '?x))) CxBox)
            hq (v/assert kb (list q Tom) CxBox)]
        (testing "a firing concluding the inert record's sentence makes the record believed"
          (is (v/believed? kb h)))
        (v/retract! kb hq)
        (testing "and the retraction of the firing's premise keeps the record, inert and OUT"
          (is (= (list p Tom) (:sentence (sentex-of kb h))))
          (is (not (v/believed? kb h)))
          (is (not (jtms/known-datum? (reasoning/tms kb) h))))))))

(deftest an-inert-negation-forms-no-nogood
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p Tom CxBox]
      (v/assert kb (list p Tom) 'CxUniverse)                              ; believed
      (v/assert kb (list 'genlCx CxBox 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert-inert kb (list 'not (list p Tom)) CxBox)                 ; inert opposite
      (testing "no contradiction, and the believed side stands"
        (is (zero? (count (v/contradictions kb))))
        (is (seq (v/sentexes-matching kb (list p Tom) 'CxUniverse)))))))

;; ---- 3. do/label: one inert labeling per optimal answer set -------------

(defn- color-choices
  "docs/solving.md's example: at most one color for an individual."
  [kb]
  (let [candidate (tu/tmp-pred) color (tu/tmp-pred) item (tu/tmp-ind)]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
              'CxUniverse)
    (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
              'CxUniverse)
    (v/assert kb (list 'functional color) 'CxUniverse)
    (v/assert kb (list candidate item) 'CxUniverse)
    {:color color :item item}))

(deftest label-materializes-one-inert-context-per-answer-set
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
        (testing "two optima: red-world and blue-world"
          (is (= 2 (:count r)))
          (let [worlds (set (map (fn [l] (set (map #(nth % 2) (:true l)))) (:labelings r)))]
            (is (= #{#{'red} #{'blue}} worlds))))
        (testing "each labeling is a total, consistent assignment"
          (doseq [l (:labelings r)]
            (is (= 1 (count (:true l))))
            (is (= 1 (count (:false l))))))
        (testing "base belief is untouched — neither color is believed, no contradiction"
          (is (empty? (v/sentexes-matching kb (list color item 'red) 'CxUniverse)))
          (is (empty? (v/sentexes-matching kb (list color item 'blue) 'CxUniverse)))
          (is (zero? (count (v/contradictions kb)))))
        (testing "and the truth values persist as inert sentexes in each context"
          ;; two truth values plus the labelingOf ownership marker
          (doseq [l (:labelings r)]
            (is (= 3 (count (v/sentexes-in-context kb (:context l)))))))))))

(deftest answer-sets-read-the-program-with-no-keep-belief-objective-and-write-nothing
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            fact   #(list color item %)
            before (count (v/sentexes-in-context kb 'CxUniverse))
            all    (v/answer-sets kb 'CxUniverse)
            read   #(:consequences (v/answer-sets kb 'CxUniverse {:reading %}))]
        (testing "the empty choice is an optimum beside each color, since only the soft
                  functional clash costs"
          (is (= #{#{} #{(fact 'red)} #{(fact 'blue)}} (set (:answer-sets all))))
          (is (= [:optimum [0]] ((juxt :status :costs) all))))
        (testing "no color is cautious, and both are brave"
          (is (= #{} (read :cautious)))
          (is (= #{(fact 'red) (fact 'blue)} (read :brave))))
        (is (= 1 (count (:answer-sets (v/answer-sets kb 'CxUniverse {:reading :one})))))
        (is (= before (count (v/sentexes-in-context kb 'CxUniverse))))))))

(deftest answer-sets-refuses-an-option-its-reading-does-not-read-and-a-query-context
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [[opts mismatch] [[[:limit 3] :not-a-map]
                             [{:reading :brave :limit 3} :unknown-key]
                             [{:reading :every} :bad-value]
                             [{:among [1.5]} :bad-value]
                             [{:opt-strategy :oll} :bad-value]
                             [{:project 'tourEdge} :bad-value]]]
      (is (= [:unknown-option mismatch]
             (try (v/answer-sets kb 'CxUniverse opts)
                  (catch clojure.lang.ExceptionInfo e ((juxt :type :mismatch) (ex-data e)))))
          (pr-str opts)))
    (is (= :unsupported-context
           (try (v/answer-sets kb 'CxEverything)
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(deftest label-with-no-constraint-keeps-every-choice
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate wants Item]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list wants '?c 'tea)))
                  'CxUniverse)
        (v/assert kb (list candidate Item) 'CxUniverse)
        (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
          (is (= 1 (:count r)))
          (is (= 1 (count (:true (first (:labelings r)))))))))))

(deftest label-with-no-choices-does-nothing
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p Tom]
      (v/assert kb (list p Tom) 'CxUniverse)
      (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
        (is (zero? (:count r)))
        (is (= :no-choices (:reason r)))))))

(deftest a-negated-choice-head-is-refused
  ;; Grounding refuses the head, so the test needs no solver backend.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate paints Cand]
      (v/assert kb (list candidate Cand) 'CxUniverse)
      (v/assert kb (list 'set/assumptionRule
                         (list 'implies (list candidate '?c) (list 'not (list paints '?c))))
                'CxUniverse)
      (let [e (try (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)
                   (catch clojure.lang.ExceptionInfo ex ex))]
        (is (instance? clojure.lang.ExceptionInfo e) "the negated-head label is refused")
        (is (= :choice-head-not-positive (:type (ex-data e))))
        (is (= [(list 'not (list paints Cand))] (:negated (ex-data e)))
            "and the offending ground head is named")))))

(deftest grounding-honors-the-assumption-rules-exception
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [candidate banned wants Item Other]
      (v/assert kb (list 'exceptWhen (list banned '?c)
                         (list 'set/assumptionRule
                               (list 'implies (list candidate '?c) (list wants '?c 'tea))))
                'CxUniverse)
      (v/assert kb (list candidate Item) 'CxUniverse)
      (v/assert kb (list banned Item) 'CxUniverse)
      (testing "the only candidate is excepted, so there is nothing to solve"
        (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
          (is (zero? (:count r)))
          (is (= :no-choices (:reason r)))))
      (when asp?
        (testing "an unbanned candidate is still offered"
          (v/assert kb (list candidate Other) 'CxUniverse)
          (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
            (is (= 1 (:count r)))
            (is (= [(list wants Other 'tea)] (:true (first (:labelings r)))))))))))

(deftest a-forward-rule-derives-the-fact-a-choice-grounds-on
  ;; the same do/label call grounds nothing before the forward rule concludes the
  ;; precondition and a labeling after
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [registered candidate color Item]
      (let [plan (tu/tmp-ctx "Plan")]
        ;; a forward rule concluding the precondition, and a two-way colour choice over it
        (v/assert kb (list 'set/forwardRule
                           (list 'implies (list registered '?c) (list candidate '?c)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse)
        (v/assert kb (list 'functional color) 'CxUniverse)
        (testing "before the precondition: nothing is a candidate, so a do/label grounds nothing"
          (let [r (v/assert kb (list 'do/label 'CxUniverse plan) 'CxUniverse)]
            (is (zero? (:count r)))
            (is (= :no-choices (:reason r)))))
        (testing "the precondition arrives and the forward rule concludes the candidate"
          (v/assert kb (list registered Item) 'CxUniverse)
          (is (seq (v/sentexes-matching kb (list candidate Item) 'CxUniverse))
              "the forward rule materialized the derived fact"))
        (when asp?
          (testing "now the choice grounds on the derived fact: two optima, red and blue"
            (let [r (v/assert kb (list 'do/label 'CxUniverse plan) 'CxUniverse)]
              (is (= 2 (:count r)))
              (is (= #{(list color Item 'red) (list color Item 'blue)} (set (:choices r))))
              (let [worlds (set (map (fn [l] (set (map #(nth % 2) (:true l)))) (:labelings r)))]
                (is (= #{#{'red} #{'blue}} worlds))))))))))

(deftest grounding-proves-an-antecedent-through-a-registered-prover
  ;; `(reach ?c)` has no stored fact and no rule; only the registered prover answers it
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [reach color Item]
      (v/add-prover kb (reify prover-types/Prover
                         (applicable?  [_ _ goal _] (and (sequential? goal) (= reach (first goal))))
                         (est-bindings [_ _ _ _] 1)
                         (cost         [_ _ _ _] :lookup)
                         (completeness [_ _ _ _] 100)
                         (solve [_ _ goal _]
                           (let [[_ x] goal]
                             (cond
                               (and (symbol? x) (.startsWith (name x) "?")) [{x Item}]
                               (= x Item)                                    [{}]
                               :else                                         [])))))
      (v/assert kb (list 'set/assumptionRule (list 'implies (list reach '?c) (list color '?c 'red)))
                'CxUniverse)
      (v/assert kb (list 'set/assumptionRule (list 'implies (list reach '?c) (list color '?c 'blue)))
                'CxUniverse)
      (v/assert kb (list 'functional color) 'CxUniverse)
      (testing "the antecedent has no stored fact and no rule concludes it — only the prover answers"
        (is (empty? (v/sentexes-matching kb (list reach Item) 'CxUniverse))))
      (when asp?
        (testing "the choice grounds on the prover-supplied binding: two optima, red and blue"
          (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
            (is (= 2 (:count r)))
            (is (= #{(list color Item 'red) (list color Item 'blue)} (set (:choices r))))
            (let [worlds (set (map (fn [l] (set (map #(nth % 2) (:true l)))) (:labelings r)))]
              (is (= #{#{'red} #{'blue}} worlds)))))))))

(deftest grounding-reads-a-transitive-closure-from-a-bound-end-and-reports-an-open-one
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [ancestorOf heir lineage A B C]
      (doseq [s [(list 'transitive ancestorOf) (list ancestorOf A B) (list ancestorOf B C)]]
        (v/assert kb s 'CxUniverse))
      (testing "one bound end: the closure answers, so A two edges up is a choice"
        (let [rule (v/assert kb (list 'set/assumptionRule
                                      (list 'implies (list ancestorOf '?x C) (list heir '?x)))
                             'CxUniverse)
              r    (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan") :one) 'CxUniverse)]
          (is (= #{(list heir A) (list heir B)} (set (:choices r))))
          (is (= [] (:unenumerated r)))
          (v/retract! kb rule)))
      (testing "both ends open: the stored edges answer, and the result names the predicate"
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list ancestorOf '?x '?y) (list lineage '?y '?x)))
                  'CxUniverse)
        (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan") :one) 'CxUniverse)]
          (is (= #{(list lineage B A) (list lineage C B)} (set (:choices r))))
          (is (= [ancestorOf] (:unenumerated r))))))))

(deftest a-constraint-body-reaches-a-prover
  ;; `(forbidden ?x)` has no stored fact and no rule; only the registered prover answers it
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [cand pick forbidden Ay Bee]
        (v/add-prover kb (reify prover-types/Prover
                           (applicable?  [_ _ goal _] (and (sequential? goal) (= forbidden (first goal))))
                           (est-bindings [_ _ _ _] 1)
                           (cost         [_ _ _ _] :lookup)
                           (completeness [_ _ _ _] 100)
                           (solve [_ _ goal _]
                             (let [[_ x] goal]
                               (cond
                                 (and (symbol? x) (.startsWith (name x) "?")) [{x Ay}]
                                 (= x Ay) [{}]
                                 :else    [])))))
        (v/assert kb (list 'set/assumptionRule (list 'implies (list cand '?x) (list pick '?x)))
                  'CxUniverse)
        (v/assert kb (list cand Ay) 'CxUniverse)
        (v/assert kb (list cand Bee) 'CxUniverse)
        ;; hard: a pick the prover marks forbidden is a nogood over that choice head
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'and (list pick '?x) (list forbidden '?x))
                                 (list 'probe_forbidden_pick '?x)))
                  'CxUniverse)
        ;; soft: take a pick when one is allowed, so the optimum reaches for Bee
        (v/assert kb (list 'set/softConstraint
                           (list 'implies (list 'and (list 'not (list pick Ay)) (list 'not (list pick Bee)))
                                 (list 'probe_no_pick Ay)))
                  'CxUniverse)
        (let [r      (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan") :one) 'CxUniverse)
              truths (:true (first (:labelings r)))]
          (is (some #(= (list pick Bee) %) truths)
              "the unforbidden choice is taken")
          (is (not-any? #(= (list pick Ay) %) truths)
              "the choice the prover forbids is a nogood, so it is never true"))))))

;; ---- 6. groundings are never stored; a re-run replaces -------------------

(deftest groundings-are-never-stored
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            r (v/assert kb (list 'do/label 'CxUniverse 'CxMenuPlan) 'CxUniverse)]
        (testing "the menu comes back in the result instead"
          (is (= #{(list color item 'red) (list color item 'blue)} (set (:choices r)))))
        (testing "no options context exists, in the hierarchy or as an extent"
          (is (not (contains? (set (v/contexts kb)) 'CxMenuPlanOptions)))
          (is (zero? (v/count-in-context kb 'CxMenuPlanOptions))))
        (testing "the choice predicate is stored only as labeling truth values"
          ;; two labelings × (one positive + one negative) — a stored menu would add
          ;; two more to the predicate extent
          (is (= 4 (v/count-with-functor kb color))))))))

(deftest label-replaces-a-previous-run
  ;; inert writes are find-or-create and numbering restarts at 1, so without the sweep a
  ;; re-run unions two groundings in one context
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate color Item]
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse)
        (let [fh   (v/assert kb (list 'functional color) 'CxUniverse)
              cand (v/assert kb (list candidate Item) 'CxUniverse)
              r1   (v/assert kb '(do/label CxUniverse CxReplacePlan) 'CxUniverse)]
          (is (= 2 (:count r1)) "the clash splits the optima: two worlds")
          (testing "the base moves — the clash is retracted — and a re-run replaces"
            (v/retract! kb fh)
            (let [r2 (v/assert kb '(do/label CxUniverse CxReplacePlan) 'CxUniverse)]
              (is (= 1 (:count r2)) "no clash, one world keeping both choices")
              (testing "the surplus stale context dropped out of the hierarchy"
                (is (contains? (set (v/contexts kb)) 'CxReplacePlan1))
                (is (not (contains? (set (v/contexts kb)) 'CxReplacePlan2))))
              (testing "and the surviving context holds exactly the new truth values"
                ;; run 1 left a `(not …)` here; a union would still show it
                (is (= #{(list color Item 'red) (list color Item 'blue)}
                       (set (remove #(= 'labelingOf (first %))
                                    (map :sentence (v/sentexes-in-context kb 'CxReplacePlan1)))))))))
          (testing "a run that grounds no choices clears everything: its result is 'no labelings'"
            (v/retract! kb cand)
            (let [r3 (v/assert kb '(do/label CxUniverse CxReplacePlan) 'CxUniverse)]
              (is (= :no-choices (:reason r3)))
              (is (not (contains? (set (v/contexts kb)) 'CxReplacePlan1))))))))))

(deftest classify-replaces-its-previous-classification
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate color Item]
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse)
        (let [fh (v/assert kb (list 'functional color) 'CxUniverse)]
          (v/assert kb (list candidate Item) 'CxUniverse)
          (v/assert kb '(do/label CxUniverse CxReclassPlan) 'CxUniverse)
          (let [c1 (v/assert kb '(do/classify CxReclassPlan) 'CxUniverse)]
            (is (= 2 (count (:supportable c1))) "tied worlds: both colors supportable"))
          (v/retract! kb fh)
          (v/assert kb '(do/label CxUniverse CxReclassPlan) 'CxUniverse)
          (let [c2 (v/assert kb '(do/classify CxReclassPlan) 'CxUniverse)]
            (is (= 2 (count (:forced c2))) "one world now: both colors forced")
            (is (empty? (:supportable c2)))
            (testing "the class context holds only the fresh classification and its marker"
              (is (= #{(list 'forced (list color Item 'red))
                       (list 'forced (list color Item 'blue))
                       '(classificationOf CxReclassPlanClass CxReclassPlan)}
                     (set (map :sentence (v/sentexes-in-context kb 'CxReclassPlanClass))))))))))))

(deftest a-backendless-rerun-leaves-the-previous-run-standing
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (let [r1 (v/assert kb '(do/label CxUniverse CxKeepPlan) 'CxUniverse)]
        (is (= 2 (:count r1)))
        (with-redefs [solver/available? (constantly false)]
          (let [r2 (v/assert kb '(do/label CxUniverse CxKeepPlan) 'CxUniverse)]
            (is (= :no-backend (:reason r2)))))
        (testing "nothing was cleared"
          (is (contains? (set (v/contexts kb)) 'CxKeepPlan1))
          (is (contains? (set (v/contexts kb)) 'CxKeepPlan2))
          ;; two truth values plus the labelingOf marker, all still standing
          (is (= 3 (count (v/sentexes-in-context kb 'CxKeepPlan1)))))))))

(deftest a-user-context-matching-the-name-pattern-is-not-swept
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [p Tom]
        (color-choices kb)
        ;; a real user context whose name collides with what label will mint
        (v/assert kb '(genlCx CxSweepPlan1 CxUniverse) 'CxUniverse
                  {:strength :monotonic})
        (v/assert kb (list p Tom) 'CxSweepPlan1 {:strength :monotonic})
        (v/assert kb '(do/label CxUniverse CxSweepPlan) 'CxUniverse)
        (v/assert kb '(do/label CxUniverse CxSweepPlan) 'CxUniverse)
        (testing "the user's believed fact survived two runs of the sweep"
          (is (seq (v/sentexes-matching kb (list p Tom) 'CxSweepPlan1))))
        (testing "and classify aggregates only the marked labelings"
          (let [c (v/assert kb '(do/classify CxSweepPlan) 'CxUniverse)]
            (is (= 2 (:count c)))
            (is (not-any? #(= (list p Tom) %)
                          (concat (:forced c) (:supportable c) (:excluded c))))))))))

(deftest a-users-sentex-about-a-solve-context-survives-the-sweep
  ;; a classification context has no solve edge, and an empty one passes the
  ;; believed-extent check
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [about Tom]
        (color-choices kb)
        (v/assert kb '(do/label CxUniverse CxOwnPlan) 'CxUniverse)
        ;; the user's edge, hanging the (still empty) class context under their own
        ;; context, and a claim about a labeling context made from elsewhere
        (let [edge  (v/assert kb '(genlCx CxOwnPlanClass CxUniverse) 'CxUniverse
                              {:strength :monotonic})
              claim (v/assert kb (list about Tom 'CxOwnPlan1) 'CxUniverse)]
          (v/assert kb '(do/classify CxOwnPlan) 'CxUniverse)
          (v/assert kb '(do/classify CxOwnPlan) 'CxUniverse)
          (testing "two classifications later the user's edge stands"
            (is (v/believed? kb edge))
            (is (seq (v/sentexes-matching kb '(genlCx CxOwnPlanClass CxUniverse) 'CxUniverse))))
          (testing "and the classification and its marker were written beside it"
            (is (= 3 (count (v/sentexes-in-context kb 'CxOwnPlanClass)))))
          (v/assert kb '(do/label CxUniverse CxOwnPlan) 'CxUniverse)
          (testing "a re-run replaces the labeling but leaves the claim about it"
            (is (v/believed? kb claim))
            (is (= 3 (count (v/sentexes-in-context kb 'CxOwnPlan1)))
                "two truth values plus the marker, freshly written")))))))

(deftest a-users-genlcx-edge-off-a-labeling-context-survives-the-sweep
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (v/assert kb '(do/label CxUniverse CxHangPlan) 'CxUniverse)
      (let [users (mapv #(v/assert kb (list 'genlCx 'CxHangPlan1 %) 'CxUniverse
                                   {:strength :monotonic})
                        '[CxHangA CxHangB CxHangC])]
        (is (every? #(v/believed? kb %) users) "the user's three edges are believed")
        (let [r (v/assert kb '(do/label CxUniverse CxHangPlan) 'CxUniverse)]
          (testing "a re-run replaces the labeling and leaves the user's edges standing"
            (is (every? #(v/believed? kb %) users))
            (is (= 3 (count (v/sentexes-matching kb '(genlCx CxHangPlan1 ?up)
                                                 'CxUniverse)))))
          (testing "while its own placement edge and truth values went with the run"
            (is (empty? (v/sentexes-matching kb '(genlCx CxHangPlan1 CxUniverse)
                                             'CxUniverse)))
            (is (empty? (v/sentexes-in-context kb 'CxHangPlan1))))
          (testing "and the fresh labelings were written into slots of their own"
            (is (= 2 (:count r)))
            (is (not-any? #(= 'CxHangPlan1 (:context %)) (:labelings r)))))))))

(deftest a-labeling-with-believed-content-blocks-the-rerun-rather-than-being-skipped
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [note Hello]
        (color-choices kb)
        (is (= 2 (:count (v/assert kb '(do/label CxUniverse CxBlockPlan) 'CxUniverse))))
        (v/assert kb (list note Hello) 'CxBlockPlan1)
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/assert kb '(do/label CxUniverse CxBlockPlan) 'CxUniverse)))]
          (is (= :labeling-run-blocked (:type (ex-data e))))
          (is (= '[CxBlockPlan1] (:believed (ex-data e)))))
        (testing "and it refused rather than writing a third slot"
          (is (not (contains? (set (v/contexts kb)) 'CxBlockPlan3)))
          (is (= 2 (:count (v/assert kb '(do/classify CxBlockPlan) 'CxUniverse)))
              "one grounding's worth of labelings, as before"))
        (testing "the user's fact is untouched, which is why the sweep declined"
          (is (seq (v/sentexes-matching kb (list note Hello) 'CxBlockPlan1))))
        (testing ":one and :sat are unaffected — they have nothing to replace"
          (is (= 1 (:count (v/assert kb '(do/label CxUniverse CxBlockPlan :one) 'CxUniverse)))))
        (testing "retracting the user's fact unblocks the run"
          (run! #(v/retract! kb (:id %))
                (v/sentexes-matching kb (list note Hello) 'CxBlockPlan1))
          (is (= 2 (:count (v/assert kb '(do/label CxUniverse CxBlockPlan) 'CxUniverse)))))))))

(deftest a-labeling-that-lost-its-marker-blocks-the-rerun
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (v/assert kb '(do/label CxUniverse CxLostPlan) 'CxUniverse)
      (let [marker (first (filter #(= 'labelingOf (first (:sentence %)))
                                  (v/sentexes-in-context kb 'CxLostPlan1)))]
        (v/retract! kb (:id marker))
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/assert kb '(do/label CxUniverse CxLostPlan) 'CxUniverse)))]
          (is (= :labeling-run-blocked (:type (ex-data e))))
          (is (= '[CxLostPlan1] (:orphaned (ex-data e)))))
        (testing "no fresh slot was minted around it"
          (is (not (contains? (set (v/contexts kb)) 'CxLostPlan3))))
        (testing "retracting the orphan's extent and its placement edge unblocks the run"
          (run! #(v/retract! kb (:id %)) (v/sentexes-in-context kb 'CxLostPlan1))
          (run! #(v/retract! kb (:id %))
                (v/sentexes-matching kb '(genlCx CxLostPlan1 CxUniverse) 'CxUniverse))
          (is (= 2 (:count (v/assert kb '(do/label CxUniverse CxLostPlan) 'CxUniverse)))))))))

(deftest a-classification-with-believed-content-blocks-its-own-rerun
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [note Hello]
        (color-choices kb)
        (v/assert kb '(do/label CxUniverse CxClsPlan) 'CxUniverse)
        (v/assert kb '(do/classify CxClsPlan) 'CxUniverse)
        (let [before (count (v/sentexes-in-context kb 'CxClsPlanClass))]
          (v/assert kb (list note Hello) 'CxClsPlanClass)
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/assert kb '(do/classify CxClsPlan) 'CxUniverse)))]
            (is (= :labeling-run-blocked (:type (ex-data e))))
            (is (= '[CxClsPlanClass] (:believed (ex-data e)))))
          (testing "a re-label refuses too, the class context being its to replace as well"
            (is (thrown? clojure.lang.ExceptionInfo
                         (v/assert kb '(do/label CxUniverse CxClsPlan) 'CxUniverse))))
          (testing "and nothing was written beside the standing classification"
            (is (= (inc before) (count (v/sentexes-in-context kb 'CxClsPlanClass)))
                "the user's own sentex, and nothing else")))))))

(deftest an-unmarked-context-named-like-the-classification-refuses-the-run
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [p Tom]
        (color-choices kb)
        (let [h (v/assert-inert kb (list p Tom) 'CxFooClass)]
          (doseq [op ['(do/label CxUniverse CxFoo) '(do/classify CxFoo)]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/assert kb op 'CxUniverse)))]
              (is (= [:labeling-run-blocked '[CxFooClass]]
                     ((juxt :type :unmarked) (ex-data e)))
                  (str op))))
          (testing "the user's sentex survives both refusals"
            (is (some? (sentex-of kb h))))
          (testing "retracting it unblocks the run, and the classification carries its marker"
            (v/retract! kb h)
            (is (= 2 (:count (v/assert kb '(do/label CxUniverse CxFoo) 'CxUniverse))))
            (v/assert kb '(do/classify CxFoo) 'CxUniverse)
            (is (some #(= '(classificationOf CxFooClass CxFoo) (:sentence %))
                      (v/sentexes-in-context kb 'CxFooClass)))
            (is (= 2 (:count (v/assert kb '(do/label CxUniverse CxFoo) 'CxUniverse)))
                "a marked classification is swept by the re-run")
            (is (empty? (v/sentexes-in-context kb 'CxFooClass)))))))))

(deftest a-do-label-run-makes-exactly-one-solve-in-every-mode
  ;; docs/asp.md, "The time limit": `do/label`'s row, one solve in every mode
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (doseq [[mode expected] [[:all :all-optima] [:one :label] [:sat :label]]]
        (let [seen  (atom [])
              solve solver/solve]
          (with-redefs [solver/solve (fn [a m] (swap! seen conj m) (solve a m))]
            (v/assert kb (list 'do/label 'CxUniverse 'CxOneSolvePlan mode) 'CxUniverse))
          (is (= [expected] @seen) (str mode)))))))

;; ---- 3b. finding the rules a solve reads ---------------------------------

(defn- walked-rules
  "The rules a solve reads, found by walking each visible context's whole extent: the
  reference `program-rules` answers without the walk."
  [kb base]
  (set (for [ctx (distinct (cons base (tax/context-up (reasoning/taxonomy kb) base)))
             h   (reads/as-stored-in-context (:index kb) ctx)
             :let [s (p/get-sentex (:records kb) h)]
             :when (and s (rules/solve-sentex? s) (res/rule-believed? kb h)
                        (res/believed-at? kb h base))]
         h)))

(deftest the-solve-rule-set-answers-what-the-extent-walk-answers
  ;; Rules of every solve kind in three contexts, one a sibling the base cannot see, plus a
  ;; derived assumption rule and a chaining rule the set must leave out.  Across
  ;; arrival orders, and after a retraction, a defeat and a withdrawn genlCx edge, the
  ;; set read equals the walk, and its content order does not move with the order.
  (tu/with-terms [candidate color flag hasTone clashOf Tom CxMid CxLow CxSide]
    (let [orders (atom #{})]
      (doseq [seed [1 2 3 4]]
        (tu/with-cleared-kb [kb tu/fresh]
          (let [red   (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
                items [[(list 'genlCx CxMid 'CxUniverse) 'CxUniverse]
                       [(list 'genlCx CxLow CxMid) 'CxUniverse]
                       [(list 'genlCx CxSide 'CxUniverse) 'CxUniverse]
                       [red CxMid]
                       [(list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue))) CxSide]
                       [(list 'set/hardConstraint
                              (list 'implies (list 'and (list color '?c 'red) (list color '?c 'blue))
                                    (list clashOf '?c '?c)))
                        CxLow]
                       [(list 'asp/atMost 1 '?k (list color Tom '?k)) 'CxUniverse]
                       [(list 'set/solveRule (list 'implies (list color '?c 'red) (list hasTone '?c 'warm))) CxLow]
                       [(list 'set/forwardRule (list 'implies (list candidate '?c) (list flag '?c))) CxLow]
                       [(list 'set/forwardRule
                              (list 'implies (list flag '?t)
                                    (list 'set/assumptionRule
                                          (list 'implies (list candidate '?t) (list color '?t 'green)))))
                        CxLow]
                       [(list candidate Tom) 'CxUniverse]]
                rnd   (java.util.Random. seed)
                order (let [l (java.util.ArrayList. ^java.util.Collection items)]
                        (java.util.Collections/shuffle l rnd)
                        (vec l))
                read  #(let [rs (#'sc/program-rules kb CxLow)]
                         (is (= (walked-rules kb CxLow) (set (map :id rs))) (str "seed " seed " " %))
                         (mapv :sentence rs))]
            (doseq [[s ctx] order]
              ;; the edges monotonic, the rest default, so the denial below defeats `flag`
              (if (= 'genlCx (first s))
                (v/assert kb s ctx {:strength :monotonic})
                (v/assert kb s ctx)))
            (let [all (read "all arrived")]
              (is (= 5 (count all)) "red, the derived green, the constraint, the bound, the solve rule")
              (swap! orders conj all))
            (v/retract! kb (v/handle-of kb red CxMid))
            (read "after a retraction")
            (v/assert kb (list 'not (list flag Tom)) CxLow {:strength :monotonic})
            (is (= 3 (count (read "after the derived rule's support is defeated"))))
            (run! #(v/retract! kb (:id %))
                  (v/sentexes-matching kb (list 'genlCx CxLow CxMid) 'CxUniverse))
            (read "after the genlCx edge is withdrawn"))))
      (is (= 1 (count @orders)) "one content order in every arrival order"))))

(deftest finding-a-solves-rules-reads-its-rules-not-the-corpus
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [candidate color noise]
      (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
                'CxUniverse)
      (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
                'CxUniverse)
      (let [fetches (fn []
                      (let [n    (atom 0)
                            recs (:records kb)
                            counting #_{:clj-kondo/ignore [:missing-protocol-method]}
                            (reify p/RecordStore
                              (get-sentex [_ id] (swap! n inc) (p/get-sentex recs id)))]
                        (dorun (#'sc/assumption-rules (assoc kb :records counting) 'CxUniverse))
                        @n))
            before  (fetches)]
        (dotimes [_ 200] (v/assert kb (list noise (tu/tmp-ind)) 'CxUniverse))
        (is (= before (fetches)) "200 more facts in the base, no more fetches")
        (is (= before (count (reads/as-stored-rules-in-global (:index kb) :solve))))))))

;; ---- 4. do/classify: gather brave/cautious over the labelings -----------

(deftest classify-gathers-brave-cautious-over-labelings
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            into (tu/tmp-ctx "Plan")]
        (v/assert kb (list 'do/label 'CxUniverse into) 'CxUniverse)
        (let [c (v/assert kb (list 'do/classify into) 'CxUniverse)]
          (testing "both colors are supportable — each true in one world, false in the other"
            (is (= #{(list color item 'red) (list color item 'blue)} (set (:supportable c))))
            (is (empty? (:forced c)))
            (is (empty? (:excluded c))))
          (testing "and the classification persists as inert sentexes"
            (is (= #{(list 'supportable (list color item 'red))
                     (list 'supportable (list color item 'blue))
                     (list 'classificationOf (:class-context c) into)}
                   (set (map :sentence (v/sentexes-in-context kb (:class-context c))))))))))))

(deftest classify-marks-an-unconstrained-choice-forced
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate wants Item]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list wants '?c 'tea)))
                  'CxUniverse)
        (v/assert kb (list candidate Item) 'CxUniverse)
        (let [into (tu/tmp-ctx "Plan")]
          (v/assert kb (list 'do/label 'CxUniverse into) 'CxUniverse)
          (let [c (v/assert kb (list 'do/classify into) 'CxUniverse)]
            (is (= [(list wants Item 'tea)] (:forced c)))
            (is (empty? (:supportable c)))))))))

;; ---- 5. imperative argument checks --------------------------------------

(deftest the-imperatives-check-their-arguments
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [form [(list 'do/label 'CxUniverse)                 ; one arg
                  (list 'do/label 'CxUniverse 'A 'B)           ; three
                  (list 'do/classify)                               ; none
                  (list 'do/classify 'A 'B)]]                       ; two
      (is (= :not-assertible
             (try (v/assert kb form 'CxUniverse) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (str "refused: " (pr-str form))))
    (testing "and a do/ imperative is refused inside a rule"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'implies (list 'p '?x) (list 'do/label 'A 'B)) 'CxUniverse {:direction :forward}))))))

;; ---- progressive solve contexts: a 4x4 sudoku ---------------------------
;; Each round `do/label` enumerates the worlds over the candidates the excepted
;; assumptionRule offers, `do/classify` names the forced values, and `promote` writes
;; them as `filled` clues into a `genlCx` child of the round, which rules more
;; candidates out.  The loop ends when nothing is left to choose.

;; the unique solution, and the five cells the puzzle leaves open
(def ^:private solution
  {[1 1] 1 [1 2] 2 [1 3] 3 [1 4] 4
   [2 1] 3 [2 2] 4 [2 3] 1 [2 4] 2
   [3 1] 2 [3 2] 1 [3 3] 4 [3 4] 3
   [4 1] 4 [4 2] 3 [4 3] 2 [4 4] 1})

(def ^:private open-cells #{[1 1] [1 2] [1 3] [2 1] [3 1]})

(def ^:private all-cells (sort (keys solution)))

(defn- cell-sym [[r c]] (symbol (str "C" r c)))
(defn- val-sym  [n]     (symbol (str "V" n)))

(defn- box-of [[r c]] [(quot (dec r) 2) (quot (dec c) 2)])

(defn- peers?
  "Same row, same column, or same 2×2 box."
  [a b]
  (and (not= a b)
       (or (= (a 0) (b 0)) (= (a 1) (b 1)) (= (box-of a) (box-of b)))))

(defn- load-sudoku
  "The timeless structure and rules into CxSudoku; the given clues into
  CxRound1, which sees it."
  [kb]
  (let [S 'CxSudoku]
    ;; metadata first — it governs the facts and choices below
    (v/assert kb '(symmetric peerOf) S {:strength :monotonic})
    (v/assert kb '(functional cellValue) S {:strength :monotonic})
    ;; the board: cells and values as typed individuals
    (doseq [rc all-cells]
      (v/assert kb (list 'sudoku_cell (cell-sym rc)) S {:strength :monotonic}))
    (doseq [n (range 1 5)]
      (v/assert kb (list 'sudoku_value (val-sym n)) S {:strength :monotonic}))
    ;; peer geometry, one direction per unordered pair — peerOf is symmetric
    (doseq [[i a] (map-indexed vector all-cells)
            b     (drop (inc i) all-cells)
            :when (peers? a b)]
      (v/assert kb (list 'peerOf (cell-sym a) (cell-sym b)) S {:strength :monotonic}))
    ;; a filled peer rules its value out; a filled cell rules every value out
    (v/assert kb '(implies (and (peerOf ?c ?c2) (filled ?c2 ?v)) (ruledOut ?c ?v))
              S {:direction :forward :strength :monotonic})
    (v/assert kb '(implies (and (filled ?c ?v2) (sudoku_value ?v)) (ruledOut ?c ?v))
              S {:direction :forward :strength :monotonic})
    ;; the choice: any cell may take any value — except one already ruled out
    (v/assert kb '(exceptWhen (ruledOut ?c ?v)
                              (set/assumptionRule
                               (implies (and (sudoku_cell ?c) (sudoku_value ?v))
                                        (cellValue ?c ?v))))
              S {:strength :monotonic})
    ;; round 1 sees the structure and adds the clues
    (v/assert kb '(genlCx CxRound1 CxSudoku) S {:strength :monotonic})
    (doseq [rc all-cells :when (not (open-cells rc))]
      (v/assert kb (list 'filled (cell-sym rc) (val-sym (solution rc)))
                'CxRound1 {:strength :monotonic}))))

(defn- promote
  "Record newly forced cell values as real clues in `ctx`, the next round's context —
  a genlCx child of `prev`, so the next grounding sees everything so far."
  [kb forced ctx prev]
  (v/assert kb (list 'genlCx ctx prev) prev {:strength :monotonic})
  (doseq [s forced
          :let [[_ c vv] (vec s)]]
    (v/assert kb (list 'filled c vv) ctx {:strength :monotonic})))

(deftest sudoku-solved-by-progressive-solve-contexts
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (load-sudoku kb)

      (let [r1 (v/assert kb '(do/label CxRound1 CxRoundOnePlan) 'CxRound1)
            c1 (v/assert kb '(do/classify CxRoundOnePlan) 'CxRound1)]
        (testing "round 1: C11 is open three ways, the other four open cells are naked singles"
          (is (= 3 (:count r1)))
          (is (= #{'(cellValue C12 V2) '(cellValue C13 V3)
                   '(cellValue C21 V3) '(cellValue C31 V2)}
                 (set (:forced c1))))
          (is (= #{'(cellValue C11 V1) '(cellValue C11 V2) '(cellValue C11 V3)}
                 (set (:supportable c1))))
          (is (empty? (:excluded c1))))
        (testing "each world keeps the four singles plus one of C11's candidates"
          (doseq [l (:labelings r1)]
            (is (= 5 (count (:true l))))
            (is (= 2 (count (:false l)))))
          (is (= #{'V1 'V2 'V3}
                 (set (map (fn [l]
                             (some (fn [s] (let [[_ c vv] (vec s)]
                                             (when (= c 'C11) vv)))
                                   (:true l)))
                           (:labelings r1))))))
        (testing "the labeling contexts hang under the round that produced them"
          (is (every? #(v/sees? kb % 'CxRound1)
                      (map :context (:labelings r1)))))

        (promote kb (:forced c1) 'CxRound2 'CxRound1)
        (let [r2 (v/assert kb '(do/label CxRound2 CxRoundTwoPlan) 'CxRound2)
              c2 (v/assert kb '(do/classify CxRoundTwoPlan) 'CxRound2)]
          (testing "round 2: the promoted clues squeeze C11 to a single — one world, one forced value"
            (is (= 1 (:count r2)))
            (is (= ['(cellValue C11 V1)] (:forced c2)))
            (is (empty? (:supportable c2))))

          (promote kb (:forced c2) 'CxRound3 'CxRound2)
          (testing "round 3: every cell is decided, so grounding offers nothing"
            (let [r3 (v/assert kb '(do/label CxRound3 CxRoundThreePlan) 'CxRound3)]
              (is (zero? (:count r3)))
              (is (= :no-choices (:reason r3)))))

          (testing "the chain of round contexts proves the unique solution"
            (doseq [rc all-cells]
              (let [vs (distinct (map #(get % '?v)
                                      (v/prove kb (list 'filled (cell-sym rc) '?v)
                                               'CxRound3)))]
                (is (= [(val-sym (solution rc))] vs)
                    (str "cell " rc)))))

          (testing "no choice ever leaked into belief, and nothing contradicts"
            (is (empty? (v/prove kb '(cellValue ?c ?v) 'CxRound3)))
            (is (zero? (count (v/contradictions kb)))))

          (testing "re-running a round replaces its labelings instead of accreting"
            ;; CxRound1's up-closure is unchanged by the later rounds (they sit
            ;; below it), so the same three worlds come back — into freshly rewritten
            ;; contexts, each holding exactly one grounding's truth values
            (let [r1b (v/assert kb '(do/label CxRound1 CxRoundOnePlan) 'CxRound1)]
              (is (= 3 (:count r1b)))
              ;; five kept + two rejected truth values + the labelingOf marker
              (doseq [l (:labelings r1b)]
                (is (= 8 (count (v/sentexes-in-context kb (:context l)))))))))))))
