;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reach-memo-test
  "The two caches over a transitive predicate's closure, which hold different things at
  different scopes.

  **`observe/*reach-memo*`** holds one node's neighbours for the length of a search step.
  A rule with two transitive antecedents solves the second once per binding of the join
  variable; without the memo each solve re-walks the closure over the nodes many seeds
  share.  Opened once per backward search (`observe/with-search-scope`), it collapses
  those repeated lookups to one store hit per node, and — being fresh per query, over a
  KB a query never mutates — can never go stale.

  **`:closure-answers`** holds a whole reach, on the KB, across asks.  That one *can* go
  stale, so everything able to move an answer has to retire it, and the tests below are
  mostly about the ways an answer moves: belief, retraction, a later edge, a later
  sub-predicate, and the vantage a reader stands at."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb succs-is-memoized-only-under-a-bound-cache
  (tu/with-terms [before A B CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (v/assert kb (list before A B) CxFarm)
    (testing "no memo bound -> each succs call hits the store"
      (is (= 2 (tu/neighbours-built #(binding [observe/*reach-memo* nil]
                                       (#'provers/succs kb before A CxFarm)
                                       (#'provers/succs kb before A CxFarm))))))
    (testing "a bound memo -> repeated succs of the same node hits the store once"
      (is (= 1 (tu/neighbours-built #(binding [observe/*reach-memo* (atom {})]
                                       (#'provers/succs kb before A CxFarm)
                                       (#'provers/succs kb before A CxFarm))))))
    (testing "preds-of shares the cache without colliding with succs (different dir)"
      (is (= 2 (tu/neighbours-built #(binding [observe/*reach-memo* (atom {})]
                                       (#'provers/succs kb before A CxFarm)
                                       (#'provers/preds-of kb before A CxFarm))))   ; a different direction of A
          "succ and pred of the same node are distinct keys"))))

(tu/deftest-kb two-transitive-antecedents-stay-correct-and-linear
  (tu/with-terms [before twoHop CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (let [nodes (vec (repeatedly 11 tu/tmp-ind))]           ; N0 -> N1 -> … -> N10, a chain
      (doseq [i (range 10)] (v/assert kb (list before (nodes i) (nodes (inc i))) CxFarm))
      ;; twoHop(?a,?c) :- before(?a,?b) ∧ before(?b,?c), backward-only so nothing is
      ;; forward-materialized and the join genuinely walks the `before` closure twice
      (v/assert-rule kb [(list before '?a '?b) (list before '?b '?c)]
                     (list twoHop '?a '?c) CxFarm {:direction :backward})
      (let [ans   (atom nil)
            built (tu/neighbours-built
                   #(reset! ans (set (map (fn [b] (get b '?c))
                                          (v/query kb (list twoHop (nodes 0) '?c) CxFarm
                                                   {:max-depth 2})))))]
        (testing "correct: N0 two-hops to every node from N2 onward"
          (is (= (set (subvec nodes 2)) @ans)))
        (testing "the closure is walked once, not once per join binding"
          ;; ~11 distinct nodes each built once; un-memoized is ~66 (11+10+…+1)
          (is (< built 25)
              (str "neighbour sets built " built " should be ~linear, not quadratic")))))))

;; ---- the closure ANSWER cache (`:closure-answers`) -----------------------
;;
;; The memo above holds one node's neighbours for the length of a search step.  This one
;; holds a whole reach, on the KB, across asks — so everything that can move an answer
;; has to move it, and every one of those is a clock move rather than an invalidation
;; this cache knows how to perform.  The belief case is the one that is silent when it is
;; wrong: a stale closure answers plausibly.

(defn- ancestors-of
  [kb pred x context]
  (set (map #(get % '?y) (v/ask kb (list pred x '?y) context))))

(tu/deftest-kb a-defeated-edge-moves-the-cached-closure
  ;; Write this one first: a closure held across a relabel is the failure that reports a
  ;; plausible answer rather than an error.  A relabel moves the change clock, which is
  ;; what retires the entry — nothing here looks for the entry the edge was in.
  (tu/with-terms [before A B C CxFarm]
    (v/assert kb (list 'genlCx CxFarm 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'transitive before) CxFarm)
    (v/assert kb (list before A B) CxFarm)
    (v/assert kb (list before B C) CxFarm)
    (is (= #{B C} (ancestors-of kb before A CxFarm)) "the closure, computed and held")
    ;; the middle edge is defeated rather than removed: the sentex stays stored and goes
    ;; OUT, which is the move a cache keyed on the store alone would not see
    (v/assert kb (list 'not (list before B C)) CxFarm {:strength :monotonic})
    (is (= #{B} (ancestors-of kb before A CxFarm))
        "the closure shrinks with belief, and does not answer out of the held set")))

(tu/deftest-kb a-retracted-edge-moves-the-cached-closure
  (tu/with-terms [before A B C CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (v/assert kb (list before A B) CxFarm)
    (let [h (v/assert kb (list before B C) CxFarm)]
      (is (= #{B C} (ancestors-of kb before A CxFarm)))
      (v/retract! kb h)
      (is (= #{B} (ancestors-of kb before A CxFarm))))))

(tu/deftest-kb a-new-edge-extends-a-closure-already-answered
  (tu/with-terms [before A B C CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (v/assert kb (list before A B) CxFarm)
    (is (= #{B} (ancestors-of kb before A CxFarm)))
    (v/assert kb (list before B C) CxFarm)
    (is (= #{B C} (ancestors-of kb before A CxFarm)) "the held answer did not survive the assert")))

(tu/deftest-kb a-sub-predicate-edge-arriving-later-extends-the-closure
  ;; The walk fans its functor over the genl spec closure, so an edge stored under a
  ;; sub-predicate is a hop.  A genl edge is an assert like any other, so the clock moves
  ;; and the held answer goes with it.
  (tu/with-terms [before strictlyBefore A B C CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (v/assert kb (list before A B) CxFarm)
    (v/assert kb (list strictlyBefore B C) CxFarm)
    (is (= #{B} (ancestors-of kb before A CxFarm)))
    (v/assert kb (list 'genl strictlyBefore before) CxFarm)
    (is (= #{B C} (ancestors-of kb before A CxFarm))
        "the sub-predicate's edge is now a hop, and the held closure did not hide it")))

(tu/deftest-kb two-contexts-that-see-different-edges-get-different-closures
  ;; The vantage is in the key.  Without it the first context asked would answer for the
  ;; second, which is the quietest possible wrong answer.
  (tu/with-terms [before A B C CxBase CxSide]
    (v/assert kb (list 'genlCx CxSide CxBase) 'CxUniverse)
    (v/assert kb (list 'transitive before) CxBase)
    (v/assert kb (list before A B) CxBase)
    (v/assert kb (list before B C) CxSide)             ; only the narrower view sees it
    (is (= #{B} (ancestors-of kb before A CxBase)) "the base sees one hop")
    (is (= #{B C} (ancestors-of kb before A CxSide)) "and the side context sees two")
    (is (= #{B} (ancestors-of kb before A CxBase)) "and asking again does not swap them")))

(tu/deftest-kb a-repeated-closure-ask-walks-nothing
  (tu/with-terms [before CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (let [nodes (vec (repeatedly 8 tu/tmp-ind))]
      (doseq [i (range 7)] (v/assert kb (list before (nodes i) (nodes (inc i))) CxFarm))
      (let [first-answer (atom nil)
            walked        (tu/neighbours-built #(reset! first-answer
                                                        (ancestors-of kb before (nodes 0) CxFarm)))
            again         (atom nil)
            walked-again  (tu/neighbours-built #(reset! again
                                                        (ancestors-of kb before (nodes 0) CxFarm)))]
        (is (= @first-answer @again) "the same answer")
        (is (pos? walked) "the first ask walked")
        (is (zero? walked-again) "and the second walked nothing at all")))))

(tu/deftest-kb a-closed-goal-reads-the-cache-without-filling-it
  ;; The asymmetry: an entry answers a pair by membership, and a closed goal that misses
  ;; keeps its early exit rather than building the whole extent to store one.
  (tu/with-terms [before CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (let [nodes (vec (repeatedly 8 tu/tmp-ind))]
      (doseq [i (range 7)] (v/assert kb (list before (nodes i) (nodes (inc i))) CxFarm))
      (testing "a closed goal alone leaves the cache empty"
        (v/clear-caches kb)
        (is (v/ask? kb (list before (nodes 0) (nodes 7)) CxFarm))
        (is (zero? (count (:entries @(reasoning/closures kb))))))
      (testing "and once an open ask has filled it, a pair from that node is answered from the set"
        (ancestors-of kb before (nodes 0) CxFarm)
        (let [stranger (tu/tmp-ind)                         ; in no edge, so in no reach
              hit      (atom nil)
              miss     (atom nil)
              walked   (tu/neighbours-built (fn []
                                              (reset! hit  (v/ask? kb (list before (nodes 0) (nodes 7)) CxFarm))
                                              (reset! miss (v/ask? kb (list before (nodes 0) stranger) CxFarm))))]
          (is @hit)
          (is (not @miss))
          (is (zero? walked) "neither answer walked — both came out of the held set")))
      (testing "a pair from a node no ask has filled still walks, and still stops early"
        (let [answered (atom nil)
              walked   (tu/neighbours-built #(reset! answered
                                                     (v/ask? kb (list before (nodes 7) (nodes 0)) CxFarm)))]
          (is (not @answered))
          (is (pos? walked) "the miss falls through to the walk rather than inventing one"))))))

(tu/deftest-kb a-closure-past-the-bound-is-not-held
  ;; The bound counts members, because an entry is a whole reach: bounding entries would
  ;; bound nothing.  A reach bigger than the bound is never stored at all — it is the
  ;; case the bound exists for.
  (tu/with-terms [before CxFarm]
    (v/assert kb (list 'transitive before) CxFarm)
    (let [nodes (vec (repeatedly 8 tu/tmp-ind))]
      (doseq [i (range 7)] (v/assert kb (list before (nodes i) (nodes (inc i))) CxFarm))
      (binding [provers/*closure-answer-limit* 3]
        (v/clear-caches kb)
        (is (= 7 (count (ancestors-of kb before (nodes 0) CxFarm)))
            "the answer is the whole reach whether or not it is held")
        (is (zero? (count (:entries @(reasoning/closures kb))))
            "and a reach of 7 members is not held under a bound of 3"))
      (testing "a total that reaches the bound drops the map rather than evicting"
        (binding [provers/*closure-answer-limit* 5]
          (v/clear-caches kb)
          (ancestors-of kb before (nodes 5) CxFarm)     ; 2 members
          (ancestors-of kb before (nodes 4) CxFarm)     ; 3 more, total 5
          (is (pos? (count (:entries @(reasoning/closures kb)))))
          (ancestors-of kb before (nodes 3) CxFarm)     ; 4 more, over the bound
          (is (zero? (count (:entries @(reasoning/closures kb))))))))))
