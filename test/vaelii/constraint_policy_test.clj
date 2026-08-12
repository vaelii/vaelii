;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-policy-test
  "What **`check`** says about a definitional clash, under both constraint policies.

  `check` promises to predict `assert`, and for `:disjoint` and `:functional` what
  `assert` does is the KB's `:constraints` policy's answer — so the only way `check`
  can keep that promise is to read the policy too.  Whether it does is asked here in
  both directions.

  The other two cases are the ones the policy does **not** reach.  `:arbitrate` admits a
  clash against a *defeasible* claim; against **known-true** content it still refuses,
  because admitting it would store what the KB can never believe.  So `check` reports a
  problem there under either policy, and a reader who took \"`:arbitrate` means `check`
  returns empty\" as unconditional would be wrong exactly where it matters.  And
  `:asymmetric`, the third arbitrable kind, reads the opposing class whatever the policy
  says — the control on the two that move.

  `constraint_nogood_test` owns the policy as a *setting* — per-KB against the process
  default, and a declaration arriving after the facts.  This namespace owns what `check`
  says about it."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- arbitrating-kb [] (v/open-kb (assoc tu/scratch-space :constraints :arbitrate)))
(defn- refusing-kb    [] (v/open-kb (assoc tu/scratch-space :constraints :refuse)))

(deftest disjoint-clash-under-refuse
  (tu/with-neutral-kb [kb refusing-kb]
    (tu/with-terms [dog_t cat_t Muffet Whiskers]
      (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
      (v/assert kb (list dog_t Muffet) 'UniverseContext)
      (testing "a compatible individual is unaffected"
        (is (v/assert kb (list cat_t Whiskers) 'UniverseContext)))
      (testing "check reports the clash, and assert throws it"
        (is (seq (v/check kb (list cat_t Muffet) 'UniverseContext)))
        (is (= [:disjoint]
               (mapv :type (v/check kb (list cat_t Muffet) 'UniverseContext))))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list cat_t Muffet) 'UniverseContext))))
      (testing "and nothing was stored"
        (is (nil? (v/handle-of kb (list cat_t Muffet) 'UniverseContext)))
        (is (v/ask? kb (list dog_t Muffet) 'UniverseContext))
        (is (not (v/ask? kb (list cat_t Muffet) 'UniverseContext)))))))

(deftest disjoint-clash-under-arbitrate
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [dog_t cat_t Muffet Whiskers]
      (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
      (v/assert kb (list dog_t Muffet) 'UniverseContext)
      (testing "a compatible individual is unaffected"
        (is (v/assert kb (list cat_t Whiskers) 'UniverseContext)))
      (testing "check reports nothing, because assert would admit it"
        (is (empty? (v/check kb (list cat_t Muffet) 'UniverseContext)))
        (is (v/assert kb (list cat_t Muffet) 'UniverseContext)))
      (testing "the pair is a represented dilemma, not a survivor and a casualty"
        (is (= 1 (count (v/contradictions kb))))
        (is (v/ask? kb (list dog_t Muffet) 'UniverseContext))
        (is (v/ask? kb (list cat_t Muffet) 'UniverseContext))))))

(deftest check-still-reports-a-clash-against-known-true-under-either-policy
  ;; The line `:arbitrate` does not cross, and the one a reader of the policy is most
  ;; likely to assume away.  `refuses-assert?` reads the *opposing* side's class: a
  ;; known-true opponent refuses whatever the policy says, so `check` predicts a throw.
  (doseq [[policy build] [[:refuse refusing-kb] [:arbitrate arbitrating-kb]]]
    (testing (str "under " policy)
      (tu/with-neutral-kb [kb build]
        (tu/with-terms [dog_t cat_t Muffet]
          (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
          (v/assert kb (list dog_t Muffet) 'UniverseContext {:strength :monotonic})
          (is (= [:disjoint]
                 (mapv :type (v/check kb (list cat_t Muffet) 'UniverseContext)))
              "a known-true opponent is not arbitrable, so check predicts the refusal")
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'UniverseContext)))
          (is (empty? (v/contradictions kb))))))))

(deftest asymmetric-is-not-policy-dependent-at-all
  ;; The third arbitrable kind reads the opposing class under either policy, so it is
  ;; the control on the two above: what moves there must not move here.  It is also the
  ;; `:type` the docstring's enumeration has to name, since `check` can return it.
  (doseq [[policy build] [[:refuse refusing-kb] [:arbitrate arbitrating-kb]]]
    (testing (str "under " policy)
      (tu/with-neutral-kb [kb build]
        (tu/with-terms [biggerThan Alice Bob Carla Dana]
          (v/assert kb (list 'asymmetric biggerThan) 'UniverseContext)
          (testing "a defeasible converse is admitted, and settled"
            (v/assert kb (list biggerThan Alice Bob) 'UniverseContext)
            (is (empty? (v/check kb (list biggerThan Bob Alice) 'UniverseContext)))
            (is (v/assert kb (list biggerThan Bob Alice) 'UniverseContext)))
          (testing "a known-true converse is refused, and check says so"
            (v/assert kb (list biggerThan Carla Dana) 'UniverseContext
                      {:strength :monotonic})
            (is (= [:asymmetric]
                   (mapv :type (v/check kb (list biggerThan Dana Carla)
                                        'UniverseContext))))
            (is (thrown? clojure.lang.ExceptionInfo
                         (v/assert kb (list biggerThan Dana Carla)
                                   'UniverseContext)))))))))
