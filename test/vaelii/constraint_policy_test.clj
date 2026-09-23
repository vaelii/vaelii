;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-policy-test
  "What **`check`** says about a definitional clash, under both constraint policies.

  `check` promises to predict `assert`, and for `:disjoint` and `:functional` what
  `assert` does is the KB's `:constraints` policy's answer — so the only way `check`
  can keep that promise is to read the policy too.  Whether it does is asked here in
  both directions.

  The other two cases are the ones the policy does **not** reach.  `:arbitrate` admits a
  clash against a *defeasible* claim; against **known-true** content separated by a
  **known-true** declaration it still refuses, because admitting it would store what the
  KB can never believe.  Both halves are read: a known-true membership separated by a
  `:default` declaration is a pair a denial of that declaration retires, so it is
  arbitrated rather than refused.  So `check` reports a problem there under either
  policy, and a reader who took \"`:arbitrate` means `check` returns empty\" as
  unconditional would be wrong exactly where it matters.  And
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
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (testing "a compatible individual is unaffected"
        (is (v/assert kb (list cat_t Whiskers) 'CxUniverse)))
      (testing "check reports the clash, and assert throws it"
        (is (seq (v/check kb (list cat_t Muffet) 'CxUniverse)))
        (is (= [:disjoint]
               (mapv :type (v/check kb (list cat_t Muffet) 'CxUniverse))))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list cat_t Muffet) 'CxUniverse))))
      (testing "and nothing was stored"
        (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse)))
        (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
        (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse)))))))

(deftest disjoint-clash-under-arbitrate
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [dog_t cat_t Muffet Whiskers]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (testing "a compatible individual is unaffected"
        (is (v/assert kb (list cat_t Whiskers) 'CxUniverse)))
      (testing "check reports nothing, because assert would admit it"
        (is (empty? (v/check kb (list cat_t Muffet) 'CxUniverse)))
        (is (v/assert kb (list cat_t Muffet) 'CxUniverse)))
      (testing "the pair is a represented dilemma, not a survivor and a casualty"
        (is (= 1 (count (v/contradictions kb))))
        (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
        (is (v/ask? kb (list cat_t Muffet) 'CxUniverse))))))

(deftest check-still-reports-a-clash-against-known-true-under-either-policy
  ;; The line `:arbitrate` does not cross, and the one a reader of the policy is most
  ;; likely to assume away.  `refuses-assert?` reads the *opposing* side's class: a
  ;; known-true opponent refuses whatever the policy says, so `check` predicts a throw.
  ;;
  ;; The separation is known-true too, and that is not decoration.  Under `:arbitrate`
  ;; the refusal reads both halves — what the sentence opposes *and* the derivation that
  ;; makes the two a pair — so a `:default` declaration here would be arbitrated instead
  ;; (the case below).  Known-true is what the shipped upper ontology declares its own
  ;; separations at.
  (doseq [[policy build] [[:refuse refusing-kb] [:arbitrate arbitrating-kb]]]
    (testing (str "under " policy)
      (tu/with-neutral-kb [kb build]
        (tu/with-terms [dog_t cat_t Muffet]
          (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (= [:disjoint]
                 (mapv :type (v/check kb (list cat_t Muffet) 'CxUniverse)))
              "a known-true opponent is not arbitrable, so check predicts the refusal")
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'CxUniverse)))
          (is (empty? (v/contradictions kb))))))))

(deftest check-follows-arbitrate-across-a-defeasible-separation
  ;; The same known-true opponent, and the opposite answer, because the separation is a
  ;; `:default` claim: a pair that rests on one is a pair a later `(not (disjoint …))`
  ;; retires, so refusing the sentence would throw away content the KB goes on to
  ;; believe.  `check` has to predict that, or it stops predicting `assert`.
  ;;
  ;; Under `:refuse` nothing about this moves — the policy is about whether a *writer* is
  ;; told no (`checks/arbitrating?`), and a writer is told no on any clash the KB reads.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [dog_t cat_t Muffet]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/check kb (list cat_t Muffet) 'CxUniverse))
          "check predicts the admission")
      (is (v/assert kb (list cat_t Muffet) 'CxUniverse))))
  (tu/with-neutral-kb [kb refusing-kb]
    (tu/with-terms [dog_t cat_t Muffet]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
      (is (= [:disjoint] (mapv :type (v/check kb (list cat_t Muffet) 'CxUniverse)))
          "and :refuse still refuses it")
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat_t Muffet) 'CxUniverse))))))

(deftest asymmetric-is-not-policy-dependent-at-all
  ;; The third arbitrable kind reads the opposing class under either policy, so it is
  ;; the control on the two above: what moves there must not move here.  It is also the
  ;; `:type` the docstring's enumeration has to name, since `check` can return it.
  (doseq [[policy build] [[:refuse refusing-kb] [:arbitrate arbitrating-kb]]]
    (testing (str "under " policy)
      (tu/with-neutral-kb [kb build]
        (tu/with-terms [biggerThan Alice Bob Carla Dana]
          (v/assert kb (list 'asymmetric biggerThan) 'CxUniverse)
          (testing "a defeasible converse is admitted, and settled"
            (v/assert kb (list biggerThan Alice Bob) 'CxUniverse)
            (is (empty? (v/check kb (list biggerThan Bob Alice) 'CxUniverse)))
            (is (v/assert kb (list biggerThan Bob Alice) 'CxUniverse)))
          (testing "a known-true converse is refused, and check says so"
            (v/assert kb (list biggerThan Carla Dana) 'CxUniverse
                      {:strength :monotonic})
            (is (= [:asymmetric]
                   (mapv :type (v/check kb (list biggerThan Dana Carla)
                                        'CxUniverse))))
            (is (thrown? clojure.lang.ExceptionInfo
                         (v/assert kb (list biggerThan Dana Carla)
                                   'CxUniverse)))))))))
