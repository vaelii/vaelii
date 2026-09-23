;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-negation-test
  "Refutation and negative constraints over a qualitative constraint network.

  These algebras are jointly exhaustive and pairwise disjoint, so exactly one base
  relation holds of any pair — which is what lets a network prove a relation **false**
  where the engine's open-world default rightly refuses to.  Two halves, tested together
  because each is the other's mirror:

  * a goal `(not (P a b))` is answered by **refutation**, `possible ∩ denotation(P) = ∅`,
    where the positive goal needs the stronger `possible ⊆ denotation(P)`;
  * a believed `(not (P a b))` is read into the network as a **constraint**, intersecting
    the pair with the complement of that denotation.

  So a negative fact and a negative goal meet in the same place, and the calculus prover
  stays the sole complete method for its predicates under either polarity."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxSpace "upper"] [CxTime "upper"]])
                        (v/add-prover (space/spatial-prover))
                        (v/add-prover (iv/allen-prover)))))

(def ^:private C 'CxUniverse)

;; ---- (a) negative goals: refutation --------------------------------------

(tu/deftest-kb a-chain-of-containments-refutes-disconnection
  ;; A ⊏ B ⊏ D pins A?D to NTPP, and NTPP is not DC — so the network *disproves*
  ;; disconnection, which nothing asserted and no fact records.
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (is (= #{:ntpp} (space/possible-relations kb C A D)))
    (testing "the composed pair is refuted for every predicate its possible set misses"
      (is (v/ask? kb (list 'not (list 'spatiallyDisconnected A D)) C))
      (is (v/ask? kb (list 'not (list 'regionDiscreteFrom A D)) C))
      (is (v/ask? kb (list 'not (list 'hasRegionPart A D)) C)))
    (testing "and the positive goals it does entail still answer — refutation is an
              addition, not a replacement"
      (is (v/ask? kb (list 'nonTangentialProperPart A D) C))
      (is (v/ask? kb (list 'partOfRegion A D) C)))
    (testing "a relation the network entails is not refuted"
      (is (not (v/ask? kb (list 'not (list 'partOfRegion A D)) C))))))

(tu/deftest-kb an-open-pair-refutes-nothing
  ;; The boundary.  Two regions the network says nothing about have all eight relations
  ;; possible, so no denotation is disjoint from that set and no goal is refuted — "not
  ;; provable", exactly as a non-entailment is.
  (tu/with-terms [A B D E]
    ;; two components with no path between them, so no composition reaches across
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart D E) C)
    (is (= space/all-relations (space/possible-relations kb C B E))
        "B and E are unconstrained: nothing relates the two components")
    (testing "so neither polarity is answered about them"
      (is (not (v/ask? kb (list 'partOfRegion B E) C)))
      (is (not (v/ask? kb (list 'not (list 'partOfRegion B E)) C)))
      (is (not (v/ask? kb (list 'spatiallyDisconnected B E) C)))
      (is (not (v/ask? kb (list 'not (list 'spatiallyDisconnected B E)) C))))))

(tu/deftest-kb refutation-answers-all-four-goal-shapes
  ;; the same four shapes the positive reading has, and they must agree with it: a
  ;; ground check, a variable on either side, two distinct variables, one variable twice
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (let [ys #(set (map (fn [m] (get m '?y)) %))
          xs #(set (map (fn [m] (get m '?x)) %))]
      (testing "ground / ground — a check"
        (is (v/ask? kb (list 'not (list 'spatiallyDisconnected A B)) C))
        (is (not (v/ask? kb (list 'not (list 'nonTangentialProperPart A B)) C))))
      (testing "ground / variable — enumerate the nodes, the diagonal included, since no
                region is disconnected from itself"
        (is (= #{A B} (ys (v/ask kb (list 'not (list 'spatiallyDisconnected A '?y)) C)))))
      (testing "variable / ground — the mirror"
        (is (= #{A B} (xs (v/ask kb (list 'not (list 'spatiallyDisconnected '?x B)) C)))))
      (testing "two distinct variables — the pairs off the diagonal"
        (is (= #{[A B] [B A]}
               (set (map (juxt #(get % '?x) #(get % '?y))
                         (v/ask kb (list 'not (list 'spatiallyDisconnected '?x '?y)) C))))))
      (testing "one variable twice — the diagonal itself"
        (is (= #{A B} (xs (v/ask kb (list 'not (list 'spatiallyDisconnected '?x '?x)) C))))
        (is (empty? (v/ask kb (list 'not (list 'spatiallyEqual '?x '?x)) C))
            "and a region *is* equal to itself, so that one is not refuted")))))

(tu/deftest-kb an-inconsistent-network-refutes-nothing-either
  ;; an impossible theory is not mined for conclusions, whichever way the goal points
  (tu/with-terms [A B]
    (v/assert kb (list 'spatiallyDisconnected A B) C)
    (v/assert kb (list 'spatiallyEqual A B) C)
    (is (not (v/ask? kb (list 'partOfRegion A B) C)))
    (is (not (v/ask? kb (list 'not (list 'partOfRegion A B)) C)))))

(tu/deftest-kb refutation-works-for-the-interval-algebra-too
  ;; the reading lives in the shared glue, so every calculus gets it — Allen included,
  ;; where `before` composed twice cannot be `after`
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (is (= #{:before} (iv/possible-allen-relations kb C A D)))
    (is (v/ask? kb (list 'not (list 'after A D)) C))
    (is (v/ask? kb (list 'not (list 'intervalEqual A D)) C))
    (is (not (v/ask? kb (list 'not (list 'precedes A D)) C)))))

;; ---- (b) negative facts as constraints -----------------------------------

(tu/deftest-kb a-negative-fact-narrows-an-otherwise-unknown-pair
  ;; `(not (regionConnectedTo A B))` rules out all seven relations C denotes, leaving
  ;; DC alone — so a *negative* fact entails a *positive* goal nobody stated.
  (tu/with-terms [A B]
    (v/assert kb (list 'not (list 'regionConnectedTo A B)) C)
    (is (= #{:dc} (space/possible-relations kb C A B))
        "the complement of C's denotation is the singleton DC")
    (is (= :dc (space/definite-relation kb C A B)))
    (testing "and the positive goal it pins down is answered"
      (is (v/ask? kb (list 'spatiallyDisconnected A B) C))
      (is (v/ask? kb (list 'regionDiscreteFrom A B) C))
      (is (not (v/ask? kb (list 'partOfRegion A B) C))))
    (testing "the constraint is written in both directions, so the mirror answers too"
      (is (v/ask? kb (list 'spatiallyDisconnected B A) C)))
    (testing "and it follows belief: retract it and the pair is unknown again"
      (v/retract! kb (v/handle-of kb (list 'not (list 'regionConnectedTo A B)) C))
      (is (= space/all-relations (space/possible-relations kb C A B)))
      (is (not (v/ask? kb (list 'spatiallyDisconnected A B) C))))))

(tu/deftest-kb a-negative-fact-composes-with-a-positive-one
  ;; the two halves of the read meet in one network: the negative narrows a pair, the
  ;; composition carries the narrowing to a pair neither fact mentions together
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'not (list 'regionConnectedTo B D)) C)   ; B is DC from D
    (testing "A is strictly inside B and B is disconnected from D, so A is disconnected
              from D — a composition with a negative fact for one of its inputs"
      (is (= #{:dc} (space/possible-relations kb C A D)))
      (is (v/ask? kb (list 'spatiallyDisconnected A D) C))
      (is (v/ask? kb (list 'not (list 'partOfRegion A D)) C)))))

(tu/deftest-kb the-negative-read-is-order-independent
  ;; intersection is commutative and associative and a complement is a fixed function of
  ;; the denotation, so a mixed batch reads the same network whatever order it arrives in
  (tu/with-terms [A B]
    (let [facts [(list 'regionOverlaps A B)
                 (list 'not (list 'spatiallyEqual A B))
                 (list 'not (list 'hasRegionPart A B))]
          nets  (for [order [[0 1 2] [2 1 0] [1 0 2] [1 2 0]]]
                  (let [hs (mapv #(v/assert kb (nth facts %) C) order)
                        net (space/region-network kb C)]
                    (doseq [h hs] (v/retract! kb h))
                    net))]
      (is (= 1 (count (set nets))) "all four orders read one network")
      (is (= #{:po :tpp :ntpp} (get (first nets) [A B]))
          "O minus EQ minus Pi — the three ways A can overlap B without containing it"))))

(tu/deftest-kb a-negative-fact-in-an-invisible-context-does-not-narrow
  ;; the negative read applies the same belief and visibility filters the positive one
  ;; does, so a fact stated where the query cannot see it is not a constraint there
  (tu/with-terms [A B CxSide]
    (v/assert kb (list 'genlCx CxSide C) 'CxUniverse)
    (v/assert kb (list 'not (list 'regionConnectedTo A B)) CxSide)
    (testing "invisible from the more general context"
      (is (= space/all-relations (space/possible-relations kb C A B))))
    (testing "and in force in the context that states it"
      (is (= #{:dc} (space/possible-relations kb CxSide A B))))))

;; ---- a negative fact that contradicts a positive one ---------------------

(tu/deftest-kb a-negative-fact-can-empty-a-constraint-and-is-reported
  ;; `(not (partOfRegion A B))` and `(nonTangentialProperPart A B)` are different
  ;; predicates, so nothing outside the calculus sees a clash — no nogood, no defeat, both
  ;; believed.  Only the network knows they cannot both hold, and it says so through the
  ;; ledger the engine already keeps.
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'not (list 'partOfRegion A B)) C)
    (v/clear-violations! kb)
    (is (seq (v/sentexes-matching kb (list 'nonTangentialProperPart A B) C))
        "both facts are stored and believed — the TMS has no quarrel with them")
    (is (seq (v/sentexes-matching kb (list 'not (list 'partOfRegion A B)) C)))
    (testing "the calculus answers nothing at all"
      (is (not (v/ask? kb (list 'nonTangentialProperPart A B) C)))
      (is (not (v/ask? kb (list 'not (list 'partOfRegion A B)) C))))
    (testing "and reports the pair the two facts emptied"
      (let [es (filter #(= :qualitative-inconsistency (:violation %)) (v/violations kb))]
        (is (= 1 (count es)))
        (is (= :rcc8 (:calculus (first es))))
        (is (contains? (set (:pairs (:detail (first es)))) [A B]))))
    (testing "dropping either one restores a satisfiable network"
      (v/retract! kb (v/handle-of kb (list 'not (list 'partOfRegion A B)) C))
      (is (= #{:ntpp} (space/possible-relations kb C A B)))
      (is (v/ask? kb (list 'partOfRegion A B) C)))))

(tu/deftest-kb two-negatives-that-exhaust-the-universe-are-inconsistent
  ;; nothing composed here: the reader alone intersects two complements to nothing, which
  ;; is the shape `unsatisfiable-as-given?` exists to catch
  (tu/with-terms [A B]
    (v/assert kb (list 'not (list 'regionConnectedTo A B)) C)      ; leaves DC
    (v/assert kb (list 'not (list 'regionDiscreteFrom A B)) C)     ; rules DC out
    (v/clear-violations! kb)
    (is (not (v/ask? kb (list 'spatiallyDisconnected A B) C)))
    (let [es (filter #(= :qualitative-inconsistency (:violation %)) (v/violations kb))]
      (is (= 1 (count es)))
      (is (contains? (set (:pairs (:detail (first es)))) [A B])))))

(tu/deftest-kb a-self-assertion-a-negation-forbids-is-inconsistent
  ;; the diagonal case: `(not (spatiallyEqual A A))` records a constraint on [A A] that
  ;; excludes the identity, which no triple would ever visit and `constraint` would answer
  ;; the identity for regardless — so only the up-front check reports it
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'not (list 'spatiallyEqual A A)) C)
    (v/clear-violations! kb)
    (is (not (v/ask? kb (list 'nonTangentialProperPart A B) C)))
    (is (seq (filter #(= :qualitative-inconsistency (:violation %)) (v/violations kb))))))
