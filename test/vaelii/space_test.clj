;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.space-test
  "RCC-8 qualitative spatial reasoning (`vaelii.impl.space`): the eight base region
  relations and the six derived ones, answered by entailment over the path-consistent
  constraint network of everything asserted in a context.

  What each test is really checking is that a *conclusion nobody stored* comes out —
  the composition table derives the relation between two regions from the chain of
  relations between them, and a derived predicate is entailed whenever every still
  possible relation lies inside its denotation."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxSpace vocabulary that
;; states region relations in it, and the spatial prover registered.  The vocabulary is
;; an upper context (it is *about* space, so it is nobody else's business); the prover
;; is opt-in, so registering it is what turns stored spatial facts into a network.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxSpace "upper"]])
                        (v/add-prover (space/spatial-prover)))))

(def ^:private C 'CxUniverse)

;; ---- base entailment through the composition table ----------------------

(tu/deftest-kb composition-derives-an-unasserted-base-relation
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "NTPP∘NTPP = NTPP, so A is strictly inside D though nobody said so"
      (is (v/ask? kb (list 'nonTangentialProperPart A D) C)))
    (testing "and the table pins it to exactly that — no other base relation survives"
      (is (= #{:ntpp} (space/possible-relations kb C A D)))
      (is (= :ntpp (space/definite-relation kb C A D))))
    (testing "so a base relation the network excludes is not answered"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A D) C)))
      (is (not (v/ask? kb (list 'externallyConnected A D) C)))
      (is (not (v/ask? kb (list 'tangentialProperPart A D) C))))
    (testing "the converse direction is derived with it"
      (is (v/ask? kb (list 'nonTangentialProperPartInverse D A) C)))))

(tu/deftest-kb an-asserted-relation-answers-itself
  (tu/with-terms [A B]
    (v/assert kb (list 'externallyConnected A B) C)
    (is (v/ask? kb (list 'externallyConnected A B) C))
    (testing "and its converse, since EC is symmetric"
      (is (v/ask? kb (list 'externallyConnected B A) C)))
    (testing "while the seven relations it rules out are not entailed"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A B) C)))
      (is (not (v/ask? kb (list 'partiallyOverlapping A B) C)))
      (is (not (v/ask? kb (list 'spatiallyEqual A B) C))))))

(tu/deftest-kb a-disjunctive-chain-leaves-the-pair-open
  (tu/with-terms [A B D]
    ;; DC∘DC is unconstrained: two regions each disconnected from B may stand in any
    ;; relation at all, so nothing about A and D is entailed
    (v/assert kb (list 'spatiallyDisconnected A B) C)
    (v/assert kb (list 'spatiallyDisconnected B D) C)
    (is (= space/all-relations (space/possible-relations kb C A D)))
    (is (= :unknown (space/definite-relation kb C A D)))
    (testing "an open pair entails no spatial predicate, not even a wide derived one"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A D) C)))
      (is (not (v/ask? kb (list 'regionConnectedTo A D) C)))
      (is (not (v/ask? kb (list 'regionOverlaps A D) C))))))

;; ---- derived predicates, by denotation subset ---------------------------

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "#{:ntpp} sits inside every denotation that contains NTPP"
      (is (v/ask? kb (list 'partOfRegion A D) C)         "P  ⊇ #{:tpp :ntpp :eq}")
      (is (v/ask? kb (list 'properPartOfRegion A D) C)   "PP ⊇ #{:tpp :ntpp}")
      (is (v/ask? kb (list 'regionOverlaps A D) C)       "O — a proper part shares a part")
      (is (v/ask? kb (list 'regionConnectedTo A D) C)    "C — anything but disconnected"))
    (testing "and outside the denotations that do not"
      (is (not (v/ask? kb (list 'regionDiscreteFrom A D) C)))
      (is (not (v/ask? kb (list 'hasRegionPart A D) C))))
    (testing "the converse derived predicate holds the other way round"
      (is (v/ask? kb (list 'hasRegionPart D A) C))
      (is (not (v/ask? kb (list 'partOfRegion D A) C))))))

(tu/deftest-kb a-derived-assertion-constrains-without-pinning
  (tu/with-terms [A B]
    ;; asserting the disjunction narrows the pair to its denotation and no further
    (v/assert kb (list 'properPartOfRegion A B) C)
    (is (= #{:tpp :ntpp} (space/possible-relations kb C A B)))
    (testing "so the wider predicates it implies are entailed"
      (is (v/ask? kb (list 'partOfRegion A B) C))
      (is (v/ask? kb (list 'regionOverlaps A B) C)))
    (testing "but neither of the two base relations it leaves open is"
      (is (not (v/ask? kb (list 'tangentialProperPart A B) C)))
      (is (not (v/ask? kb (list 'nonTangentialProperPart A B) C))))))

(tu/deftest-kb two-facts-about-one-pair-intersect
  (tu/with-terms [A B]
    (v/assert kb (list 'partOfRegion A B) C)              ; #{:tpp :ntpp :eq}
    (v/assert kb (list 'properPartOfRegion A B) C)        ; #{:tpp :ntpp}
    (is (= #{:tpp :ntpp} (space/possible-relations kb C A B))
        "the constraint is the intersection, whichever order they were read in")
    (is (not (v/ask? kb (list 'spatiallyEqual A B) C)))))

;; ---- inconsistency -------------------------------------------------------

(tu/deftest-kb a-contradictory-network-answers-nothing
  (tu/with-terms [A B D]
    (v/assert kb (list 'spatiallyDisconnected A B) C)
    (v/assert kb (list 'spatiallyEqual A B) C)
    (testing "DC and EQ are disjoint base relations, so their pair empties"
      (is (= #{} (space/possible-relations kb C A B)))
      (is (= :inconsistent (space/definite-relation kb C A B))))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A B) C)))
      (is (not (v/ask? kb (list 'spatiallyEqual A B) C)))
      (is (not (v/ask? kb (list 'regionConnectedTo A B) C)))
      (is (empty? (v/ask kb (list 'partOfRegion A '?y) C)))
      (is (not (v/ask? kb (list 'partOfRegion D D) C))
          "not even the diagonal, which holds of any region in a coherent network"))
    (testing "retracting one of the two gives the other its answers back"
      (v/retract! kb (v/handle-of kb (list 'spatiallyEqual A B) C))
      (is (v/ask? kb (list 'spatiallyDisconnected A B) C))
      (is (not (v/ask? kb (list 'spatiallyEqual A B) C))))))

(tu/deftest-kb a-region-cannot-stand-apart-from-itself
  (tu/with-terms [A B]
    ;; DC, EC and PO are their own converses, so asserting one of a region and itself
    ;; leaves a non-empty diagonal constraint rather than an empty one.  The diagonal is
    ;; the algebra's identity — no triple visits it and no composition can narrow it — so
    ;; the claim is unsatisfiable in a way only the up-front check reports.
    (v/assert kb (list 'spatiallyDisconnected A A) C)
    (is (= :inconsistent (space/definite-relation kb C A B)))
    (is (not (v/ask? kb (list 'spatiallyDisconnected A A) C))
        "a region is not disconnected from itself, so nothing follows from saying it is")
    (testing "retracting it makes the network coherent again"
      (v/retract! kb (v/handle-of kb (list 'spatiallyDisconnected A A) C))
      (is (v/ask? kb (list 'partOfRegion A A) C)))))

(tu/deftest-kb a-reflexive-self-assertion-is-fine
  (tu/with-terms [A]
    ;; the denotations containing EQ are the ones a region may stand in to itself
    (v/assert kb (list 'regionOverlaps A A) C)
    (is (= #{:eq} (space/possible-relations kb C A A)))
    (is (v/ask? kb (list 'partOfRegion A A) C))
    (is (v/ask? kb (list 'spatiallyEqual A A) C))
    (is (not (v/ask? kb (list 'properPartOfRegion A A) C)))))

(tu/deftest-kb an-inconsistency-derived-through-a-chain-is-caught
  (tu/with-terms [A B D]
    ;; A strictly inside B, B strictly inside D — so A must be inside D, and it
    ;; cannot also be disconnected from it
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (v/assert kb (list 'spatiallyDisconnected A D) C)
    (is (= :inconsistent (space/definite-relation kb C A D)))
    (is (not (v/ask? kb (list 'nonTangentialProperPart A B) C))
        "the whole network is unsatisfiable, so no pair of it is answered")))

;; ---- open enumeration ----------------------------------------------------

(tu/deftest-kb an-open-argument-enumerates-the-entailed-regions
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "(partOfRegion A ?y) — every region A is entailed to be part of"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'partOfRegion A '?y) C)))]
        (is (= #{A B D} ys)
            "B and D by assertion and composition, A itself because P is reflexive")))
    (testing "(partOfRegion ?x D) — every region entailed to be part of D"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'partOfRegion '?x D) C)))]
        (is (= #{A B D} xs))))
    (testing "a base relation enumerates only the pairs it is pinned to"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'nonTangentialProperPart A '?y) C)))]
        (is (= #{B D} ys) "A is not strictly inside itself")))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'properPartOfRegion '?x '?y) C)))]
        (is (= #{[A B] [A D] [B D]} pairs))))))

(tu/deftest-kb one-variable-twice-is-the-diagonal
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (testing "(partOfRegion ?x ?x) holds of every region — P's denotation contains EQ"
      (is (= #{A B} (set (map #(get % '?x) (v/ask kb (list 'partOfRegion '?x '?x) C))))))
    (testing "(properPartOfRegion ?x ?x) of none — PP's does not"
      (is (empty? (v/ask kb (list 'properPartOfRegion '?x '?x) C))))))

;; ---- context and belief --------------------------------------------------

(tu/deftest-kb the-network-follows-belief-and-visibility
  (tu/with-terms [A B D CxInner CxOuter]
    (v/assert kb (list 'genlCx CxInner CxOuter) C)
    (v/assert kb (list 'nonTangentialProperPart A B) CxOuter)
    (v/assert kb (list 'nonTangentialProperPart B D) CxInner)
    (testing "the inner context sees both facts, so it derives the chain"
      (is (v/ask? kb (list 'nonTangentialProperPart A D) CxInner)))
    (testing "the outer context sees only its own, so it derives nothing"
      (is (not (v/ask? kb (list 'nonTangentialProperPart A D) CxOuter)))
      (is (v/ask? kb (list 'nonTangentialProperPart A B) CxOuter)))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart B D) CxInner))
      (is (not (v/ask? kb (list 'nonTangentialProperPart A D) CxInner))))))

;; ---- registration --------------------------------------------------------

(deftest the-registered-calculus-list-follows-the-registry
  ;; `registered-calculi` is memoized against the prover registry's *identity*, because
  ;; `calculus-for` is asked per asserted sentence and per antecedent literal.  A memo
  ;; that outlived a registration would report a calculus's own predicates as claimed by
  ;; nobody — silently, and for the life of the process.  Registration swaps the atom, so
  ;; the new registry is a new identity and a miss; what this pins is that a miss is what
  ;; happens, in both directions, since the memo holds one entry.
  ;;
  ;; Read straight off a `{:provers atom}` map: that is the whole of what the function
  ;; touches, and a second KB here would clear the shared scratch space out from under
  ;; the fixture.
  (let [registered {:provers (atom [(space/spatial-prover)])}
        bare       {:provers (atom [])}]
    (testing "a registry with no calculus prover claims nothing"
      (is (= [] (qkb/registered-calculi bare)))
      (is (nil? (qkb/calculus-for bare 'nonTangentialProperPart))))
    (testing "and one that registered the prover claims its calculus"
      (is (= [space/rcc8] (qkb/registered-calculi registered)))
      (is (= space/rcc8 (qkb/calculus-for registered 'nonTangentialProperPart))))
    (testing "asking about either afterwards still answers about that one"
      (is (= [] (qkb/registered-calculi bare)))
      (is (= [space/rcc8] (qkb/registered-calculi registered))))
    (testing "and a registration on a registry already asked about is picked up"
      (swap! (:provers bare) conj (space/spatial-prover))
      (is (= [space/rcc8] (qkb/registered-calculi bare))))))

(tu/deftest-kb the-prover-ships-opt-in
  (testing "nothing spatial is in the default registry, so a KB pays for the network
            only once it asks for it"
    (is (not-any? #(qkb/prover-for? :rcc8 %) provers/default-provers)
        "the three calculi share one prover record, so opt-in is asked by which
         calculus a registered prover speaks for, not by its class")))

(tu/deftest-kb without-the-prover-the-facts-are-inert
  ;; the same KB, queried through the *default* registry — the extension point is the prover list,
  ;; so this isolates what registering it adds without building a second KB on the
  ;; shared scratch space (which would clear this one out from under the fixture)
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "an asserted spatial relation is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'nonTangentialProperPart A B) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'nonTangentialProperPart A D) C)))
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'partOfRegion A D) C))))
    (testing "the registered prover on the very same facts does"
      (is (v/ask? kb (list 'nonTangentialProperPart A D) C))
      (is (v/ask? kb (list 'partOfRegion A D) C)))))
