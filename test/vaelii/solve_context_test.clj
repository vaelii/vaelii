;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.solve-context-test
  "assumptionRules and persistent, inert solve/labeling contexts
  (`vaelii.impl.asp.solve-context`, the `do/label` and `do/classify` imperatives).

  The feature's whole claim is that a solve becomes a **persisted, inert artifact** that
  leaves the always-true base KB untouched, so the tests pin exactly that:

    * an `assumptionRule` never forward-chains — its head is a choice, not a truth;
    * an inert fact is stored and inspectable but never IN, so it forms no nogood and
      moves no belief — which is what lets many labelings coexist;
    * `do/label` materializes one labeling context per optimal answer set, base belief
      unchanged; `do/classify` gathers brave/cautious over them.

  Enumeration needs an ASP backend, so the `do/label`/`do/classify` end-to-end tests are
  guarded on `asp?`; the assumptionRule and inert-fact unit tests are not — those are the
  representation, independent of any solver."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.types.prover :as prover-types]
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
                           'CxUniverse {:direction :forward})]
        (testing "the wrapper is part of identity, so they are two sentexes"
          (is (not= bare asm)))
        (testing "assumption? reads the record, true only for the wrapped one"
          (is (rules/assumption? (sentex-of kb asm)))
          (is (not (rules/assumption? (sentex-of kb bare)))))
        (testing "and re-asserting the same assumptionRule is idempotent"
          (is (= asm (v/assert kb (list 'set/assumptionRule
                                        (list 'implies (list candidate '?c) (list color '?c 'red)))
                               'CxUniverse {:direction :forward}))))))))

(deftest an-assumption-rule-does-not-forward-chain
  ;; The defining behaviour: a choice head is not a derived truth. The bare rule fires
  ;; on the same fact; the assumptionRule stays dormant until a solve grounds it.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate color Item]
      (v/assert kb (list 'implies (list candidate '?c) (list color '?c 'red)) 'CxUniverse {:direction :forward})
      (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
                'CxUniverse {:direction :forward})
      (v/assert kb (list candidate Item) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list color Item 'red) 'CxUniverse)) "bare rule fired")
      (is (empty? (v/sentexes-matching kb (list color Item 'blue) 'CxUniverse)) "assumptionRule did not"))))

;; ---- 2. inert facts: stored, inspectable, never believed ----------------

(deftest an-inert-fact-is-stored-but-never-believed
  ;; inert facts are not premises, so the retract-based neutral teardown cannot clean
  ;; them — a store-mutating test clears instead (like the persistence tests)
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p Tom CxBox]
      (let [h (v/assert-inert kb (list p Tom) 'CxBox)]
        (testing "stored and inspectable"
          (is (some? (sentex-of kb h)))
          (is (some #(= (:id %) h) (v/sentexes-in-context kb 'CxBox))))
        (testing "but not a premise, so not believed"
          (is (not (v/in? kb h)))
          (is (empty? (v/sentexes-matching kb (list p Tom) 'CxBox))))
        (testing "and retract! tears it down directly, though it was never a TMS datum"
          (is (= {:removed-sentexes 1 :removed-justifications 0} (v/retract! kb h)))
          (is (nil? (sentex-of kb h)))
          (is (empty? (v/sentexes-in-context kb 'CxBox)))
          (is (empty? (v/find-sentexes kb Tom))))))))

(deftest an-inert-negation-forms-no-nogood
  ;; The property that makes labelings coexist: an inert `(not X)` in a context that
  ;; sees a believed `X` is invisible to the belief-filtered nogood scan.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p Tom CxBox]
      (v/assert kb (list p Tom) 'CxUniverse)                              ; believed
      (v/assert kb (list 'genlCx 'CxBox 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert-inert kb (list 'not (list p Tom)) 'CxBox)                 ; inert opposite
      (testing "no contradiction, and the believed side stands"
        (is (zero? (count (v/contradictions kb))))
        (is (seq (v/sentexes-matching kb (list p Tom) 'CxUniverse)))))))

;; ---- 3. do/label: one inert labeling per optimal answer set -------------

(defn- color-choices
  "The user's worked example: pick at most one color for an individual."
  [kb]
  (let [candidate (tu/tmp-pred) color (tu/tmp-pred) item (tu/tmp-ind)]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
              'CxUniverse {:direction :forward})
    (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
              'CxUniverse {:direction :forward})
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

(deftest label-with-no-constraint-keeps-every-choice
  ;; Nothing forbids the choices, so the single optimum keeps them all.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate wants Item]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list wants '?c 'tea)))
                  'CxUniverse {:direction :forward})
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
  ;; A choice head must be a POSITIVE literal.  A labeling persists `(head)`/`(not head)`
  ;; and `classify`'s polarity-table reads it back by unwrapping one `not`, so a negated
  ;; head `(not X)` would round-trip as its positive core `X` with the polarity flipped —
  ;; classify emitting a statement about a non-head.  It is refused at grounding, before
  ;; any world is written, and no backend is needed to reach the refusal.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate paints Cand]
      (v/assert kb (list candidate Cand) 'CxUniverse)
      (v/assert kb (list 'set/assumptionRule
                         (list 'implies (list candidate '?c) (list 'not (list paints '?c))))
                'CxUniverse {:direction :forward})
      (let [e (try (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)
                   (catch clojure.lang.ExceptionInfo ex ex))]
        (is (instance? clojure.lang.ExceptionInfo e) "the negated-head label is refused")
        (is (= :choice-head-not-positive (:type (ex-data e))))
        (is (= [(list 'not (list paints Cand))] (:negated (ex-data e)))
            "and the offending ground head is named")))))

(deftest grounding-honors-the-assumption-rules-exception
  ;; ground-heads is a fourth consumer of a rule's firing beside the three chainers:
  ;; a binding the exceptWhen holds of is not offered as a choice, the same decision
  ;; the chainers make by refusing to fire (docs/exceptions.md).
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
  ;; Grounding proves an assumptionRule's antecedent over the facts *believed* in Base.
  ;; A forward rule's conclusion is a believed fact like any other.  So a choice whose
  ;; body names a derived predicate stays dormant until a forward rule concludes that
  ;; predicate: the precondition is asserted, the forward rule materializes the fact,
  ;; and the same do/label call that grounded nothing before now grounds a labeling.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [registered candidate color Item]
      (let [plan (tu/tmp-ctx "Plan")]
        ;; a forward rule concluding the precondition, and a two-way colour choice over it
        (v/assert kb (list 'set/forwardRule
                           (list 'implies (list registered '?c) (list candidate '?c)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse {:direction :forward})
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse {:direction :forward})
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
  ;; ground-heads proves an assumptionRule's antecedents over a REGISTRY leaf
  ;; (`registry-bounds` → `provers/solve-goal`), the division `vaelii.core/query` runs — so
  ;; a candidate that rests on a registered prover is a legal antecedent, not something the
  ;; caller must pre-project into a stored candidate fact.  Here the antecedent `(reach ?c)`
  ;; has no stored fact and no rule concludes it; only the registered prover answers it, and
  ;; the choice still grounds.  (The stored-fact leaf `prove` alone left it dormant.)
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
                'CxUniverse {:direction :forward})
      (v/assert kb (list 'set/assumptionRule (list 'implies (list reach '?c) (list color '?c 'blue)))
                'CxUniverse {:direction :forward})
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

(deftest a-constraint-body-reaches-a-prover
  ;; ground-constraint-body proves a constraint's BACKGROUND literals over the registry
  ;; leaf too, so a hardConstraint can forbid a choice on a condition only a registered
  ;; prover answers — here `(forbidden ?x)`, which has no stored fact and no rule.
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
                  'CxUniverse {:direction :forward})
        (v/assert kb (list cand Ay) 'CxUniverse)
        (v/assert kb (list cand Bee) 'CxUniverse)
        ;; hard: a pick the prover marks forbidden is a nogood over that choice head
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'and (list pick '?x) (list forbidden '?x))
                                 (list 'probe_forbidden_pick '?x)))
                  'CxUniverse {:direction :forward})
        ;; soft: take a pick when one is allowed, so the optimum reaches for Bee
        (v/assert kb (list 'set/softConstraint
                           (list 'implies (list 'and (list 'not (list pick Ay)) (list 'not (list pick Bee)))
                                 (list 'probe_no_pick Ay)))
                  'CxUniverse {:direction :forward})
        (let [r      (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan") :one) 'CxUniverse)
              truths (:true (first (:labelings r)))]
          (is (some #(= (list pick Bee) %) truths)
              "the unforbidden choice is taken")
          (is (not-any? #(= (list pick Ay) %) truths)
              "the choice the prover forbids is a nogood, so it is never true"))))))

;; ---- 6. groundings are never stored; a re-run replaces -------------------

(deftest groundings-are-never-stored
  ;; The menu is solver working state: it comes back in the result, and nothing
  ;; lands in the records beyond the labeling truth values themselves.
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
          ;; two more under the functor root
          (is (= 4 (v/count-with-functor kb color))))))))

(deftest label-replaces-a-previous-run
  ;; assert-inert is find-or-create and numbering restarts at 1, so without the
  ;; replace sweep a re-run after the base moved would union two groundings' truth
  ;; values into one context and leave surplus stale contexts for classify to sweep
  ;; back in.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate color Item]
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse {:direction :forward})
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse {:direction :forward})
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
  ;; A stale classification describes labelings that no longer exist; after the base
  ;; moves and the run is re-labeled, only the fresh classification may remain.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate color Item]
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse {:direction :forward})
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse {:direction :forward})
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
            (testing "the class context holds only the fresh classification"
              (is (= #{(list 'forced (list color Item 'red))
                       (list 'forced (list color Item 'blue))}
                     (set (map :sentence (v/sentexes-in-context kb 'CxReclassPlanClass))))))))))))

(deftest a-backendless-rerun-leaves-the-previous-run-standing
  ;; :no-backend computed nothing, so it must not destroy the artifact it failed to
  ;; replace — unlike :no-choices, which is a real (empty) result.
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
  ;; Ownership is recorded (the labelingOf marker), never inferred from a name: a
  ;; user context that happens to be named like a labeling is neither read by
  ;; classify nor cleared by a re-run — with a destructive sweep, a name pattern
  ;; would be data loss.
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
  ;; The sweep takes a context's own extent (and a marked labeling's placement edge),
  ;; never everything that *mentions* it.  A classification context has no edge of
  ;; the solve's at all, so an edge hanging `<Into>Class` somewhere is always a
  ;; user's; and an empty `<Into>Class` passes the believed-extent guard, which reads
  ;; the extent and cannot see the edge.
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
            (is (v/in? kb edge))
            (is (seq (v/sentexes-matching kb '(genlCx CxOwnPlanClass CxUniverse) 'CxUniverse))))
          (testing "and the classification was written beside it"
            (is (= 2 (count (v/sentexes-in-context kb 'CxOwnPlanClass)))))
          (v/assert kb '(do/label CxUniverse CxOwnPlan) 'CxUniverse)
          (testing "a re-run replaces the labeling but leaves the claim about it"
            (is (v/in? kb claim))
            (is (= 3 (count (v/sentexes-in-context kb 'CxOwnPlan1)))
                "two truth values plus the marker, freshly written")))))))

(deftest a-users-genlcx-edge-off-a-labeling-context-survives-the-sweep
  ;; The narrower half of the claim above, and the one where getting it wrong is data
  ;; loss: the sweep takes the *one* edge that placed the labeling under this run's
  ;; base, not every `(genlCx <labeling> _)` in the KB.  Hanging a solve's world under
  ;; contexts of one's own is the ordinary way to read it beside other knowledge, and
  ;; those edges are monotonic — asserted, believed, and nobody else's to retract.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (v/assert kb '(do/label CxUniverse CxHangPlan) 'CxUniverse)
      (let [users (mapv #(v/assert kb (list 'genlCx 'CxHangPlan1 %) 'CxUniverse
                                   {:strength :monotonic})
                        '[CxHangA CxHangB CxHangC])]
        (is (every? #(v/in? kb %) users) "the user's three edges are believed")
        (let [r (v/assert kb '(do/label CxUniverse CxHangPlan) 'CxUniverse)]
          (testing "a re-run replaces the labeling and leaves the user's edges standing"
            (is (every? #(v/in? kb %) users))
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
  ;; The sweep declines to touch a context holding a believed sentex, which is right —
  ;; it must never destroy knowledge.  Carrying on afterwards is not: the untouched
  ;; context keeps the marker naming it labeling 1 of this `Into`, the new run mints
  ;; another labeling 1 beside it, and `classify` then aggregates two groundings into
  ;; one classification — the accretion replace-on-rerun exists to prevent.  Refusing
  ;; is what makes "replaced, never accreted" true rather than usually true.
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
  ;; The marker is an ordinary retractable sentex and rediscovery is the only path to a
  ;; labeling context, so a retracted marker hides that context from the sweep forever
  ;; — while its `genlCx` edge goes on holding it under the base.  Since the placement
  ;; edge is taken off the marked context, a lost marker leaks a believed monotonic
  ;; edge, and one more slot on every re-run.  Blocked, the leak cannot start.
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
  ;; Same rule, the other artifact: a `<Into>Class` the sweep cannot clear would take a
  ;; second classification beside the first, and two of those in one context describe
  ;; no set of labelings.
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

(deftest a-do-label-run-makes-exactly-one-solve-in-every-mode
  ;; `VAELII_ASP_TIME_LIMIT` is a per-solve budget and a solve runs on the single
  ;; writer, so what an operation holds the writer for is the budget times the solves
  ;; it makes (docs/asp.md tabulates the multipliers).  `do/label` is the one at 1× in
  ;; all three modes — `:all` enumerates once, `:one` and `:sat` solve once — and this
  ;; is what keeps that row of the table honest.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (doseq [[mode expected] [[:all :all-optima] [:one :label] [:sat :label]]]
        (let [seen  (atom [])
              solve solver/solve]
          (with-redefs [solver/solve (fn [a m] (swap! seen conj m) (solve a m))]
            (v/assert kb (list 'do/label 'CxUniverse 'CxOneSolvePlan mode) 'CxUniverse))
          (is (= [expected] @seen) (str mode)))))))

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
                     (list 'supportable (list color item 'blue))}
                   (set (map :sentence (v/sentexes-in-context kb (:class-context c))))))))))))

(deftest classify-marks-an-unconstrained-choice-forced
  ;; A choice no constraint touches is kept in every labeling — a cautious consequence.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate wants Item]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list wants '?c 'tea)))
                  'CxUniverse {:direction :forward})
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
