;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.prover-composition-test
  "Completeness is a claim about a **goal**, not about a predicate.

  `solve-goal-with` runs the cheapest complete prover *alone*, which is most of what
  makes `ask` cheap on a closure goal — and it is only sound if `completeness 100`
  means *my answers are a superset of everyone else's for this goal*.  A computed
  prover normally earns that: the closures are built from the very facts `FactProver`
  would return, and a calculus reads both the facts and the derived conclusions into
  its network before entailing anything.

  What none of them can read is a claim nobody stored.  `(transitiveInArg P n R)`
  licenses a statement about a tuple that appears in no fact, no rule conclusion and no
  network — so a prover that claimed 100 unconditionally would discard it silently,
  and `query-plan` would list a prover that never runs.

  Three channels reach a goal that way, each found by differencing — run the complete
  prover alone, run everyone else applicable, and see what only the second answers.
  Two of them were live `ask` / `prove` disagreements: a `set/backwardRule` concluding
  `genl`, `disjoint` or an RCC-8 predicate never fires forward, so its conclusion is in
  no closure and no network; and a declared `(inverse P Q)` stores the claim under a
  name neither the closures nor a calculus vocabulary reads.

  These tests are the two halves of that: the claim survives, and the diagnostic says
  which provers actually ran."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private ctx 'CxUniverse)

(defn- runs [plan] (into #{} (comp (filter :runs?) (map :prover)) plan))
(defn- shadowed [plan] (into #{} (comp (remove :runs?) (map :prover)) plan))
(defn- prover-entry [plan nm] (first (filter #(= nm (:prover %)) plan)))
(defn- guarded [plan] (into #{} (comp (filter :guarded-by) (map :prover)) plan))
(defn- channels-of [plan] (some :guarded-by plan))

;; ---- the measured case ---------------------------------------------------

(tu/deftest-kb a-preserved-claim-survives-a-complete-calculus-prover
  (tu/with-terms [zone_t library_t]
    (v/add-prover kb (space/spatial-prover))
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl library_t zone_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse 'partOfRegion 1 'genl) ctx))
    ;; the claim is stated of the *general* term and inherits down to the specific one
    (v/assert kb (list 'partOfRegion zone_t zone_t) ctx)
    (testing "the inherited claim is answered rather than discarded by the calculus"
      (is (v/ask? kb (list 'partOfRegion library_t zone_t) ctx)))
    (testing "and the plan says both provers run"
      (let [plan (v/query-plan kb (list 'partOfRegion library_t zone_t) ctx)]
        (is (contains? (runs plan) "TransitiveInArgProver"))
        (is (contains? (runs plan) "CalculusProver"))
        (is (empty? (shadowed plan))
            "no prover is listed as applicable and then never consulted")
        (is (= 100 (:completeness (prover-entry plan "CalculusProver")))
            "the calculus still claims the sources it reads — that claim is true")
        (is (= #{:preserving} (channels-of plan))
            "and the plan names the source none of them reads, which is why all run")
        (is (contains? (guarded plan) "CalculusProver"))))))

(tu/deftest-kb a-calculus-goal-nothing-else-bears-on-still-runs-alone
  (tu/with-terms [RoomA RoomB]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb (list 'nonTangentialProperPart RoomA RoomB) ctx)
    (let [goal (list 'partOfRegion RoomA RoomB)
          plan (v/query-plan kb goal ctx)]
      (testing "the entailment still comes back"
        (is (v/ask? kb goal ctx)))
      (testing "and it is still the one prover consulted — the fast path is intact"
        (is (= #{"CalculusProver"} (runs plan)))
        (is (= 100 (:completeness (prover-entry plan "CalculusProver"))))
        (is (contains? (shadowed plan) "FactProver"))
        (is (= "CalculusProver" (:shadowed-by (prover-entry plan "FactProver")))
            "the plan names what displaced it")))))

;; ---- the same question of the closure provers ---------------------------

(tu/deftest-kb a-preserved-claim-survives-the-transitivity-prover
  (tu/with-terms [thing_a_t thing_b_t sub_a_t]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl sub_a_t thing_a_t) ctx)
      ;; a declaration on `genl` itself: argument 2 of a genl claim inherits upwards
      (v/assert kb (list 'transitiveInArgInverse 'genl 2 'genl) ctx))
    (v/assert kb (list 'genl thing_a_t thing_b_t) ctx)
    (let [goal (list 'genl sub_a_t thing_b_t)
          plan (v/query-plan kb goal ctx)]
      (testing "the closure answers it anyway, so nothing is lost either way"
        (is (v/ask? kb goal ctx)))
      (testing "and the plan names why the closure does not run alone"
        (is (= #{:preserving} (channels-of plan)))
        (is (contains? (guarded plan) "TransitivityProver"))
        (is (contains? (runs plan) "TransitiveInArgProver"))))))

(tu/deftest-kb an-ordinary-genl-goal-is-answered-by-the-closure-alone
  (tu/with-terms [dog_t animal_t]
    (v/assert kb (list 'genl dog_t animal_t) ctx)
    (let [plan (v/query-plan kb (list 'genl dog_t animal_t) ctx)]
      (is (= 100 (:completeness (prover-entry plan "TransitivityProver")))
          "a KB declaring no preservation pays nothing and keeps the fast path")
      (is (= #{"TransitivityProver"} (runs plan))))))

;; ---- the provers that are complete unconditionally ----------------------

(tu/deftest-kb the-guard-is-safe-in-one-direction-and-it-is-the-safe-one
  (tu/with-terms [Ann Bob]
    (testing "with nothing declared, the sole prover runs alone"
      (let [plan (v/query-plan kb (list 'different Ann Bob) ctx)]
        (is (= #{"DifferentProver"} (runs plan)))
        (is (v/ask? kb (list 'different Ann Bob) ctx))))
    ;; A declaration naming a predicate nothing can state: `different` is refused by
    ;; `wff`, so no claim about it can exist and `TransitiveInArgProver` will find none.
    ;; The guard fires anyway — it reads the declaration, not the claims — and that is
    ;; the point being pinned.
    (v/assert kb (list 'transitiveInArgInverse 'different 1 'genl) ctx)
    (let [plan (v/query-plan kb (list 'different Ann Bob) ctx)]
      (is (= 100 (:completeness (prover-entry plan "DifferentProver")))
          "the prover's own claim is unchanged — it is about the sources it reads")
      (testing "the guard fires, so the union runs instead of the one prover"
        (is (= #{:preserving} (channels-of plan)))
        (is (contains? (guarded plan) "DifferentProver"))
        (is (contains? (runs plan) "TransitiveInArgProver")))
      (testing "and the answer is unchanged, which is the property that matters:
                a guard that fires needlessly costs a lazy prover nobody forces,
                where one that fails to fire loses an answer"
        (is (v/ask? kb (list 'different Ann Bob) ctx))
        (is (not (v/ask? kb (list 'different Ann Ann) ctx)))))))

;; ---- the channel set itself ---------------------------------------------

(tu/deftest-kb the-shadowing-channel-is-named-and-empty-by-default
  (tu/with-terms [dog_t animal_t typeLargerThan]
    (is (empty? (provers/shadowing-channels kb (list typeLargerThan dog_t animal_t) ctx))
        "nothing shadows a computed answer in a KB that declares no preservation")
    (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
    (is (= #{:preserving}
           (provers/shadowing-channels kb (list typeLargerThan dog_t animal_t) ctx)))
    (testing "and it is scoped like every other declaration read"
      (tu/with-terms [CxOther]
        ;; CxOther sits above CxUniverse, so it does not see the declaration
        (v/assert kb (list 'genlCx 'CxUniverse CxOther) 'CxUniverse)
        (is (empty? (provers/shadowing-channels
                     kb (list typeLargerThan dog_t animal_t) CxOther))
            "a context that cannot see the declaration is not shadowed by it")))))

;; ---- what the planner reads ---------------------------------------------

(tu/deftest-kb the-goal-estimate-follows-the-conditional-completeness
  (tu/with-terms [zone_t library_t]
    (v/add-prover kb (space/spatial-prover))
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl library_t zone_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse 'partOfRegion 1 'genl) ctx))
    (is (nil? (provers/est-goal kb (list 'partOfRegion library_t zone_t) ctx))
        "no complete prover, so no authoritative estimate — the planner uses its own
         count-aware model rather than a shadowed prover's number")))

;; ---- :rules — a backward rule's conclusion is in no closure and no network -----

(defn- backward-rule-reaches
  "Assert a backward-only rule concluding `goal`'s predicate from `via`, and report
  what `ask?` and the plan say.  Backward-only, so it never fires forward and its
  conclusion is never stored."
  [kb via goal]
  (v/assert kb (list 'set/backwardRule (list 'implies (list (first via) '?x '?y)
                                             (list (first goal) '?x '?y)))
            ctx)
  (v/assert kb via ctx)
  {:ask   (v/ask? kb goal ctx)
   :deep  (v/query? kb goal ctx {:max-depth 2})
   :plan  (v/query-plan kb goal ctx)})

(tu/deftest-kb a-backward-rule-concluding-genl-is-not-shadowed-by-the-closure
  (tu/with-terms [sub_t sup_t pcLinked]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl sub_t 'thing) ctx)
      (v/assert kb (list 'genl sup_t 'thing) ctx))
    (let [goal (list 'genl sub_t sup_t)
          {:keys [ask deep plan]} (backward-rule-reaches kb (list pcLinked sub_t sup_t) goal)]
      (testing "a backchainer answers the goal; `ask`, which expands no rule, does not"
        (is deep)
        (is (v/provable? kb goal ctx))
        (is (not ask)))
      (testing "and the plan names the channel that stops the closure running alone"
        (is (= #{:rules} (channels-of plan)))
        (is (contains? (guarded plan) "TransitivityProver"))))))

(tu/deftest-kb a-backward-rule-concluding-disjoint-is-not-shadowed-by-the-cache
  (tu/with-terms [a_t b_t pcSep]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl a_t 'thing) ctx)
      (v/assert kb (list 'genl b_t 'thing) ctx))
    (let [goal (list 'disjoint a_t b_t)
          {:keys [ask deep plan]} (backward-rule-reaches kb (list pcSep a_t b_t) goal)]
      (is deep)
      (is (not ask))
      (is (= #{:rules} (channels-of plan)))
      (is (contains? (guarded plan) "DisjointnessProver")))))

(tu/deftest-kb a-backward-rule-concluding-a-region-relation-is-not-shadowed
  (tu/with-terms [RegionA RegionB pcInside]
    (v/add-prover kb (space/spatial-prover))
    (let [goal (list 'partOfRegion RegionA RegionB)
          {:keys [ask deep plan]} (backward-rule-reaches kb (list pcInside RegionA RegionB) goal)]
      (is deep)
      (is (not ask))
      (is (= #{:rules} (channels-of plan)))
      (is (contains? (guarded plan) "CalculusProver")))))

;; ---- :inverse — the partner is stored under a name the computed prover cannot read

(tu/deftest-kb a-declared-inverse-of-genl-is-not-shadowed-by-the-closure
  (tu/with-terms [sub_t sup_t pcSpecOf]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl sub_t 'thing) ctx)
      (v/assert kb (list 'genl sup_t 'thing) ctx)
      (v/assert kb (list 'inverse 'genl pcSpecOf) ctx))
    (v/assert kb (list pcSpecOf sup_t sub_t) ctx)      ; => (genl sub_t sup_t)
    (let [goal (list 'genl sub_t sup_t)
          plan (v/query-plan kb goal ctx)]
      (is (v/ask? kb goal ctx))
      (is (contains? (runs plan) "InverseProver"))
      (is (= #{:inverse} (channels-of plan)))
      (is (contains? (guarded plan) "TransitivityProver")))))

(tu/deftest-kb a-declared-inverse-outside-a-calculus-vocabulary-is-not-shadowed
  (tu/with-terms [Big Small pcContains]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb (list 'inverse 'partOfRegion pcContains) ctx)
    (v/assert kb (list pcContains Big Small) ctx)      ; => (partOfRegion Small Big)
    (let [goal (list 'partOfRegion Small Big)
          plan (v/query-plan kb goal ctx)]
      (is (v/ask? kb goal ctx))
      (is (contains? (runs plan) "InverseProver"))
      (is (= #{:inverse} (channels-of plan)))
      (is (contains? (guarded plan) "CalculusProver")))))

;; ---- what stays absorbed ------------------------------------------------

(tu/deftest-kb the-absorbed-channels-do-not-shadow
  (tu/with-terms [RoomA RoomB RoomAlias]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb (list 'nonTangentialProperPart RoomA RoomB) ctx)
    (testing "an equality is rewritten into the goal before any prover sees it"
      (v/assert kb (list 'equals RoomA RoomAlias) ctx)
      (is (empty? (provers/shadowing-channels kb (list 'partOfRegion RoomAlias RoomB) ctx))
          "a merge is absorbed, so it must not push the goal onto the union path")
      (is (v/ask? kb (list 'partOfRegion RoomAlias RoomB) ctx)))
    (testing "and a stored fact of the calculus is what the network is built from"
      (is (empty? (provers/shadowing-channels kb (list 'partOfRegion RoomA RoomB) ctx))))))
