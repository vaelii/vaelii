;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argtype-ground-test
  "A ground `(Type Individual)` `ask` must not pay a full inferred-type scan when a
  cheaper witness answers.  Two composing guards (perf-review #5):

    * FactProver precedes ArgTypeProver in `default-provers`, so a *stored* membership
      answers the union before ArgTypeProver.solve's scan is ever forced.
    * `inferred-types` is lazy, so an inferred-only ground test short-circuits on the
      first witness instead of computing the individual's whole type set.

  The spy counts the `argIsa` probes `inferred-types` issues — exactly the work the
  scan does, isolated the way `reach_memo_test` isolates the closure walk.  A
  `FactProver` lookup of the goal predicate uses the goal's own functor, so it is
  never an `argIsa` probe and never counted."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- counting-argisa-probes
  "Wrap `matches-visible`, counting only the `(argIsa …)` probes `inferred-types`
  issues.  Every other match (a FactProver lookup, a symmetric mirror) carries a
  different functor, so this isolates the inferred-type scan."
  [calls]
  (let [orig res/matches-visible]
    (fn [kb s c]
      (when (and (sequential? s) (= 'argIsa (first s)))
        (swap! calls inc))
      (orig kb s c))))

(defn- typed-individual-in-m-relations!
  "Assert `x` as a `dog` (⊑ `animal`), then M binary relations `(relK x IndK)` each
  argIsa-constrained at argument 1 to `animal` — so x fills M argIsa-constrained
  positions and `inferred-types` has M sentexes to scan.  Returns the `dog` type so a
  ground `(dog x)` membership can be asked."
  [kb x m ctx]
  (let [dog (tu/tmp-type "dog") animal (tu/tmp-type "animal")]
    (v/assert kb (list 'genl dog animal) ctx)
    (v/assert kb (list dog x) ctx)                      ; the stored membership FactProver answers
    (dotimes [_ m]
      (let [rel (tu/tmp-pred "rel") other (tu/tmp-ind "Other")]
        (v/assert kb (list 'argIsa rel 1 animal) ctx)
        (v/assert kb (list rel x other) ctx)))          ; x @ arg1, animal-constrained
    dog))

;; ---- the contract: a stored fact short-circuits the scan ----------------

(tu/deftest-kb stored-fact-ground-ask-does-not-scan-the-individuals-relations
  ;; THE gate.  With `(dog Muffet)` stored and Muffet also filling 30 argIsa-constrained
  ;; positions, `ask? (dog Muffet)` must be answered by the stored fact — FactProver
  ;; precedes ArgTypeProver and the union is lazy, so ArgTypeProver.solve is never
  ;; forced and `inferred-types` never runs.  Pre-change (ArgTypeProver first, eager
  ;; scan) this issued ~M argIsa probes before FactProver got a turn.
  (tu/with-terms [Muffet]
    (let [ctx 'UniverseContext, m 30
          dog (typed-individual-in-m-relations! kb Muffet m ctx)
          calls (atom 0)]
      (with-redefs [res/matches-visible (counting-argisa-probes calls)]
        (testing "the stored membership is provable"
          (is (v/ask? kb (list dog Muffet) ctx)))
        (testing "and it was answered without any inferred-type scan"
          (is (zero? @calls)
              (str "argIsa probes " @calls
                   " — a stored-fact ground ask must not scan the individual's relations")))))))

;; ---- change 2, directly: inferred-types is lazy -------------------------

(tu/deftest-kb inferred-types-streams-rather-than-computing-the-whole-type-set
  ;; Even with no stored fact to short-circuit on, `inferred-types` must be lazy: taking
  ;; a single element realizes only the head of the believed-sentex scan, not all M.
  ;; Eager (`into #{}`) would issue one argIsa probe per relation regardless.
  (tu/with-terms [Blob]
    (let [ctx 'UniverseContext, m 50
          _   (typed-individual-in-m-relations! kb Blob m ctx)
          calls (atom 0)]
      (with-redefs [res/matches-visible (counting-argisa-probes calls)]
        (let [one (first (#'provers/inferred-types kb Blob ctx))]
          (testing "it still yields a type"
            (is (some? one)))
          (testing "taking one element scanned far fewer than all M relations"
            (is (< @calls m)
                (str "argIsa probes " @calls " of " m
                     " — inferred-types must not realize the whole scan for one element"))))))))

;; ---- inferred-only membership still holds -------------------------------

(tu/deftest-kb inferred-only-membership-still-holds
  ;; (food Bone1) is provable only through (argIsa eats 2 food) + (eats Muffet Bone1):
  ;; no stored (food Bone1) fact, so ArgTypeProver must still run when FactProver
  ;; yields nothing — the reorder and the lazy `some` must not lose this answer.
  (tu/with-terms [eats food Muffet Bone1]
    (let [ctx 'UniverseContext]
      (v/assert kb (list 'argIsa eats 2 food) ctx)
      (v/assert kb (list eats Muffet Bone1) ctx)          ; Bone1 @ arg2, food-constrained
      (testing "the inferred membership is provable"
        (is (v/ask? kb (list food Bone1) ctx)))
      (testing "with no stored fact backing it"
        (is (empty? (v/sentexes-matching kb (list food Bone1) ctx))
            "membership is inferred, not stored")))))

;; ---- open enumeration unchanged -----------------------------------------

(tu/deftest-kb open-type-query-still-enumerates-every-inferred-type
  ;; `(?t Bone1)` is the pvar branch — it must still enumerate the individual's whole
  ;; inferred type set (the lazy `for` consumed to the end), including genl supertypes.
  ;; And `types-of`, which bypasses the prover engine, is untouched.
  (tu/with-terms [eats food edible fruit Muffet Bone1]
    (let [ctx 'UniverseContext]
      (v/assert kb (list 'genl food edible) ctx)
      (v/assert kb (list 'argIsa eats 2 food) ctx)
      (v/assert kb (list eats Muffet Bone1) ctx)          ; Bone1 inferred food, hence edible
      (v/assert kb (list fruit Bone1) ctx)              ; a stored membership as well
      (testing "the open query enumerates the inferred type and its supertypes"
        (let [ts (set (map #(get % '?t) (v/ask kb (list '?t Bone1) ctx)))]
          (is (contains? ts food)   "the directly-inferred type")
          (is (contains? ts edible) "and its genl supertype")
          (is (contains? ts fruit)  "and the stored membership, unioned in by FactProver")))
      (testing "types-of reports the stored memberships (it bypasses the provers)"
        (is (contains? (set (v/types-of kb Bone1 ctx)) fruit))))))

;; ---- ground miss --------------------------------------------------------

(tu/deftest-kb ground-miss-with-no-witness-returns-false
  ;; (cat Muffet) with no stored fact and no argIsa path: ArgTypeProver's `some` exhausts
  ;; the witness stream and finds nothing, so the goal fails cleanly.
  (tu/with-terms [Muffet cat]
    (let [ctx 'UniverseContext, m 5]
      (typed-individual-in-m-relations! kb Muffet m ctx)  ; Muffet is inferrably animal, never cat
      (testing "a type it neither stores nor can infer is not provable"
        (is (not (v/ask? kb (list cat Muffet) ctx)))))))

;; ---- the reorder, structurally ------------------------------------------

(tu/deftest-kb factprover-precedes-argtypeprover-in-the-plan
  ;; The union path breaks an equal-cost tie on registry order, so FactProver must sit
  ;; ahead of ArgTypeProver in the plan for a ground `(Type Individual)` goal.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [provs (mapv :prover (v/query-plan kb (list dog Muffet) 'UniverseContext))
          pos   (into {} (map-indexed (fn [i p] [p i]) provs))
          fact  (pos "FactProver")
          arg   (pos "ArgTypeProver")]
      (is (some? fact) "FactProver applies to a ground membership")
      (is (some? arg)  "ArgTypeProver applies to a ground membership")
      (is (< fact arg) "FactProver must precede ArgTypeProver"))))
