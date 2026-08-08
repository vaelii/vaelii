;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-levels-edge-test
  "Cost-model branches and level behaviours the existing suites do not reach.

  `plan_test` covers the greedy ordering, sideways information passing, the pinned
  evaluable and recursive literals, and planned-vs-unplanned equivalence.  What it
  never does is hand the planner a **negative** literal, or check the two secondary
  estimates that exist precisely because the trie cannot answer — the argument-root
  bound and the caller's `:est-override`.  Each of those is a branch whose failure
  mode is a *silently worse plan*, never an error: the wrong literal goes first and
  the query is merely slow.

  `levels_test` covers what each level yields and `escalate` from floors 0 and 2.
  The floor *above* where the answer lives, and level 1 with nothing to drive it,
  are the remaining branches."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the negative-literal cost path ------------------------------------

(tu/deftest-kb a-negative-literal-is-costed-by-the-functor-root
  ;; A negative literal keys under `[:false <body>]`, so no prefix built from its own
  ;; tokens reaches it and `count-at` answers 0 — a *lower* bound, which would rank
  ;; the most expensive literal in the conjunction as the cheapest.  The functor root
  ;; is the one count spanning both polarities.
  (tu/with-terms [banned allowed Aa Bb Cc Dd]
    ;; many negative `banned` facts, one positive `allowed` fact
    (doseq [i [Aa Bb Cc Dd]]
      (v/assert kb (list 'not (list banned i)) 'NaturalWorldContext {:chain? false}))
    (v/assert kb (list allowed Aa) 'NaturalWorldContext {:chain? false})
    (let [neg-cost (plan/est-matches kb (list 'not (list banned '?x)) #{})
          pos-cost (plan/est-matches kb (list allowed '?y) #{})]
      (testing "the negative literal's cost reflects its real extent, not zero"
        (is (pos? neg-cost) "a zero estimate would rank it as the cheapest literal")
        (is (>= neg-cost 4) "there are four stored negative facts"))
      (testing "and it is correctly costed as the more expensive of the two"
        (is (> neg-cost pos-cost))))))

(tu/deftest-kb the-planner-puts-the-selective-literal-first-even-when-it-is-negative
  ;; The ordering consequence of the estimate above: with one `allowed` fact and many
  ;; negative `banned` ones, the positive literal must lead.
  (tu/with-terms [banned allowed Aa Bb Cc Dd]
    (doseq [i [Aa Bb Cc Dd]]
      (v/assert kb (list 'not (list banned i)) 'NaturalWorldContext {:chain? false}))
    (v/assert kb (list allowed Aa) 'NaturalWorldContext {:chain? false})
    (let [ordered (plan/order kb [(list 'not (list banned '?x)) (list allowed '?x)]
                              'NaturalWorldContext)]
      (is (= (list allowed '?x) (first ordered))
          "the single-fact literal binds ?x before the four-fact one is tested"))))

;; ---- the argument-root estimate ----------------------------------------

(tu/deftest-kb a-ground-argument-after-a-variable-is-costed-by-the-argument-root
  ;; The trie narrows left to right, so `(parentOf ?x Cid)` can only be counted up to
  ;; `?x` — every `parentOf` fact.  The argument roots (`[:argument-root parentOf 2 Cid]`)
  ;; index the ground argument directly, and are the whole reason the secondary roots
  ;; exist.
  (tu/with-terms [parentOf Ann Bob Cid Dee Eve]
    (doseq [[p c] [[Ann Bob] [Ann Cid] [Dee Eve] [Bob Eve] [Cid Eve]]]
      (v/assert kb (list parentOf p c) 'NaturalWorldContext {:chain? false}))
    (let [open      (plan/est-matches kb (list parentOf '?x '?y) #{})
          after-var (plan/est-matches kb (list parentOf '?x Cid) #{})]
      (testing "fixing the second argument is tighter than leaving both open"
        (is (< after-var open)
            "without the argument root this would be the same count as the open literal"))
      (is (<= after-var 1) "exactly one fact has Cid in argument 2"))))

;; ---- :est-override ------------------------------------------------------

(tu/deftest-kb est-override-replaces-the-index-model-when-a-caller-supplies-one
  ;; The seam a chainer whose leaf is the registry uses, so a `genl` conjunct is costed by
  ;; the transitive closure rather than by stored edges (`provers/registry-est-override`,
  ;; and `provers_test` for it end to end).  Here it is driven straight at `plan/order`,
  ;; because what needs pinning is the two branches of the seam itself: that an override
  ;; is consulted and that ordering follows it, and that one declining falls back.
  (tu/with-terms [alpha beta Xx]
    (v/assert kb (list alpha Xx) 'NaturalWorldContext {:chain? false})
    (v/assert kb (list beta Xx)  'NaturalWorldContext {:chain? false})
    (let [goals    [(list alpha '?x) (list beta '?x)]
          ;; declare beta absurdly cheap and alpha expensive, inverting the tie
          override (fn [g _bound] (if (= (first g) beta) 1 9999))
          ordered  (plan/order kb goals 'NaturalWorldContext {:est-override override})]
      (is (= (list beta '?x) (first ordered))
          "the override decided the order, so it was consulted"))
    (testing "an override that declines (nil) falls back to the index model"
      (let [goals   [(list alpha '?x) (list beta '?x)]
            ordered (plan/order kb goals 'NaturalWorldContext
                                {:est-override (fn [_ _] nil)})]
        (is (= (count goals) (count ordered))
            "every literal survives the fallback path")
        (is (= (set goals) (set ordered)))))))

;; ---- escalate's floor ---------------------------------------------------

(tu/deftest-kb escalate-starting-above-where-the-answer-lives
  ;; The default floor is 2; `levels_test` also covers floor 0.  A floor *above* the
  ;; level that would answer exercises `:tried` being `(range floor (inc n))` rather
  ;; than starting at 0 — and must still find an answer at a higher level rather than
  ;; reporting none.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'NaturalWorldContext)
    (let [low  (v/escalate kb (list dog Muffet) 'NaturalWorldContext)
          high (v/escalate kb (list dog Muffet) 'NaturalWorldContext 5)]
      (testing "from the default floor the cheapest answering level is found"
        (is (some? (:level low)))
        (is (>= (:level low) 2)))
      (testing "from a floor of 5 the search starts there and still answers"
        (is (some? (:level high)))
        (is (>= (:level high) 5) "it never reports a level below the floor")
        (is (every? #(>= % 5) (:tried high))
            ":tried records only the levels actually attempted")))))

;; ---- level 1 with nothing to drive it ----------------------------------

(tu/deftest-kb level-one-with-no-root-to-narrow-on-yields-nothing
  ;; Level 1 narrows a context extent by functor.  With a variable context *and* a
  ;; non-symbol functor there is no root to drive it, and the guard must yield an
  ;; empty result rather than throwing or enumerating the KB.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'NaturalWorldContext)
    (is (empty? (v/lookup kb 1 '(?p ?x) '?ctx))
        "nothing names a root, so level 1 has nothing to offer")))
