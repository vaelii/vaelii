;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-integration-test
  "The protocol every calculus reaches through `vaelii.impl.qcn-kb`: what a registered
  prover is reachable from, the readers, negative facts, the resident network, the
  semi-naive re-join, and what an unsatisfiable network reports."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.space :as space]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; both spatial calculi and the interval one, all three provers registered — the point
;; being that they coexist without seeing each other's facts
;; The KB is built per test because tests record join baselines on CxUniverse
;; (`qkb/note-joined`), and `a-delta-with-no-baseline-is-all-and-an-unchanged-network-moves-nothing`
;; expects none.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/empty-kb)
                        (tu/load-core!)
                        (v/add-prover (space/spatial-prover))
                        (v/add-prover (iv/allen-prover)))))

(def ^:private C 'CxUniverse)

;; ---- reachable from a rule ----------------------------------------------

(tu/deftest-kb a-rule-antecedent-is-discharged-by-the-prover
  ;; a backward rule's leaf is the whole registry
  (tu/with-terms [A B D tmpInside tmpWatched]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (v/assert kb (list tmpWatched A) C)
    ;; properPartOfRegion, not partOfRegion: the latter denotes EQ too, so it holds of a
    ;; region and itself and the open enumeration below would answer A as well
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y) (list tmpWatched '?x)]
                   (list tmpInside '?x '?y) C {:direction :backward})
    (testing "the asserted step is answered"
      (is (v/query? kb (list tmpInside A B) C {:max-depth 2})))
    (testing "and so is the step only the composition entails — A is inside D by the
              table, and no sentex says so"
      (is (nil? (v/handle-of kb (list 'partOfRegion A D) C))
          "nothing was stored for the composed pair")
      (is (v/query? kb (list tmpInside A D) C {:max-depth 2})))
    (testing "an open goal enumerates through the prover too"
      (is (= #{B D} (set (map #(get % '?y)
                              (v/query kb (list tmpInside A '?y) C {:max-depth 2}))))))))

(tu/deftest-kb a-rule-exception-can-be-a-qualitative-goal
  ;; `exceptWhen` evaluates its query over the registry
  (tu/with-terms [Cage Room Sparrow Canary tmpBird tmpFlies]
    (v/assert kb (list tmpBird Sparrow) C)
    (v/assert kb (list tmpBird Canary) C)
    ;; the canary is inside a cage, and the cage inside the room: the containment that
    ;; blocks flight is one composition away from anything asserted
    (v/assert kb (list 'nonTangentialProperPart Canary Cage) C)
    (v/assert kb (list 'nonTangentialProperPart Cage Room) C)
    (v/assert kb (list 'exceptWhen (list 'properPartOfRegion '?x Room)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list 'and (list tmpBird '?x))
                                                          (list tmpFlies '?x)))))
              C)
    (testing "the bird nothing contains flies"
      (is (v/ask? kb (list tmpFlies Sparrow) C)))
    (testing "the bird the network places inside the room does not — the exception is a
              spatial entailment, not a stored fact"
      (is (not (v/query? kb (list tmpFlies Canary) C {:max-depth 2})))
      (is (= :excepted (:reason (v/why-not kb (list tmpFlies Canary) C)))))
    (testing "and freeing it lets the rule fire again"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart Cage Room) C))
      (is (v/query? kb (list tmpFlies Canary) C {:max-depth 2})))))

(tu/deftest-kb why-not-names-the-exception-over-a-firing-the-network-derives
  ;; the antecedent is a composition no fact states, so `why-not` re-solves the rule
  ;; against the network outside any chaining run to find the firing its exception blocks
  (tu/with-terms [Cage Room Canary caged indoors]
    (v/assert kb (list 'nonTangentialProperPart Canary Cage) C)
    (v/assert kb (list 'nonTangentialProperPart Cage Room) C)
    (v/assert kb (list caged Canary) C)
    (v/assert kb (list 'exceptWhen (list caged '?x)
                       (list 'set/forwardRule (list 'implies (list 'and (list 'properPartOfRegion '?x Room))
                                                    (list indoors '?x))))
              C)
    (is (= [{'?x Cage}] (v/ask kb (list indoors '?x) C)))
    (is (= [:excepted (list caged Canary)]
           ((juxt :reason :exception) (v/why-not kb (list indoors Canary) C))))))

(tu/deftest-kb a-composed-exception-withdraws-a-firing-on-the-network-it-composes-over
  ;; the rule joins on the network and its exception is a relation only composition
  ;; answers, so the fact completing the composition shares no argument with the
  ;; exception's instance: the canary is disconnected from the room because its cage is
  (tu/with-terms [Cage Room Canary indoors]
    (v/assert kb (list 'exceptWhen (list 'spatiallyDisconnected '?x Room)
                       (list 'set/forwardRule
                             (list 'implies (list 'and (list 'properPartOfRegion '?x '?y))
                                   (list indoors '?x))))
              C)
    (v/assert kb (list 'nonTangentialProperPart Canary Cage) C)
    (is (seq (v/sentexes-matching kb (list indoors Canary) C)))
    (v/assert kb (list 'spatiallyDisconnected Cage Room) C)
    (is (v/ask? kb (list 'spatiallyDisconnected Canary Room) C))
    (is (empty? (v/sentexes-matching kb (list indoors Canary) C)))))

(tu/deftest-kb a-composed-exception-withdraws-a-firing-whatever-the-rule-joins-on
  ;; the rule joins on an ordinary predicate, so only its exception is on the calculus:
  ;; neither composing fact names the canary and the room together, and whichever arrives
  ;; last must still put the firing in front of its exception
  (doseq [order [[:dc :ntpp] [:ntpp :dc]]]
    (tu/with-terms [Cage Room Canary bird flies]
      (let [facts {:dc   (list 'spatiallyDisconnected Cage Room)
                   :ntpp (list 'nonTangentialProperPart Canary Cage)}]
        (v/assert kb (list 'exceptWhen (list 'spatiallyDisconnected '?x Room)
                           (list 'set/defaultRule
                                 (list 'set/forwardRule
                                       (list 'implies (list 'and (list bird '?x))
                                             (list flies '?x)))))
                  C)
        (v/assert kb (list bird Canary) C)
        (is (seq (v/sentexes-matching kb (list flies Canary) C)))
        (doseq [f order] (v/assert kb (facts f) C))
        (is (v/ask? kb (list 'spatiallyDisconnected Canary Room) C) (str order))
        (is (empty? (v/sentexes-matching kb (list flies Canary) C)) (str order))
        (testing "and the composing fact leaving releases it"
          (v/retract! kb (v/handle-of kb (facts :ntpp) C))
          (is (seq (v/sentexes-matching kb (list flies Canary) C)) (str order)))))))

(tu/deftest-kb a-composed-exception-sees-a-sub-predicate-fact-and-the-edge-under-it
  ;; the network reads a sub-predicate's facts through the matcher's fan, so a fact on
  ;; one, and the `genl` edge that makes it one, each move the composition
  (doseq [order [[:edge :caged] [:caged :edge]]]
    (tu/with-terms [Cage Room Canary bird flies caged]
      (let [steps {:edge  (list 'genl caged 'nonTangentialProperPart)
                   :caged (list caged Canary Cage)}]
        (v/assert kb (list 'exceptWhen (list 'spatiallyDisconnected '?x Room)
                           (list 'set/defaultRule
                                 (list 'set/forwardRule
                                       (list 'implies (list 'and (list bird '?x))
                                             (list flies '?x)))))
                  C)
        (v/assert kb (list bird Canary) C)
        (v/assert kb (list 'spatiallyDisconnected Cage Room) C)
        (is (seq (v/sentexes-matching kb (list flies Canary) C)))
        (doseq [s order] (v/assert kb (steps s) C))
        (is (v/ask? kb (list 'spatiallyDisconnected Canary Room) C) (str order))
        (is (empty? (v/sentexes-matching kb (list flies Canary) C)) (str order))))))

(tu/deftest-kb a-rule-joining-on-a-calculus-gains-a-firing-from-a-sub-predicate-fact
  ;; the sub-predicate fact composes with the `ntpp` one into the rule's antecedent, and
  ;; names the cage where the firing names the canary, so the trigger position misses it
  (doseq [order (tu/orders [:rule :edge :sub :ntpp])]
    (tu/with-terms [Cage Room Canary bird caged dc]
      (let [steps {:rule #(v/assert kb (list 'set/forwardRule
                                             (list 'implies
                                                   (list 'and (list 'spatiallyDisconnected '?x '?y)
                                                         (list bird '?x))
                                                   (list caged '?x)))
                                    C)
                   :edge #(v/assert kb (list 'genl dc 'spatiallyDisconnected) C)
                   :sub  #(v/assert kb (list dc Cage Room) C)
                   :ntpp #(v/assert kb (list 'nonTangentialProperPart Canary Cage) C)}]
        (v/assert kb (list bird Canary) C)
        (doseq [s order] ((steps s)))
        (is (v/ask? kb (list 'spatiallyDisconnected Canary Room) C) (str order))
        (is (seq (v/sentexes-matching kb (list caged Canary) C)) (str order))
        (testing "and the edge leaving withdraws it: the pair's support names the edge"
          (v/retract! kb (v/handle-of kb (list 'genl dc 'spatiallyDisconnected) C))
          (is (empty? (v/sentexes-matching kb (list caged Canary) C)) (str order)))))))

(tu/deftest-kb a-rule-joining-on-a-calculus-loses-a-firing-a-sub-predicate-fact-contradicts
  ;; `(dc Canary Cage)` read as `spatiallyDisconnected` makes the network unsatisfiable,
  ;; with every fact behind the standing firing still believed
  (doseq [order [[:edge :sub] [:sub :edge]]]
    (tu/with-terms [Cage Room Canary bird caged dc]
      (let [steps {:edge (list 'genl dc 'spatiallyDisconnected)
                   :sub  (list dc Canary Cage)}]
        (v/assert kb (list 'set/forwardRule
                           (list 'implies
                                 (list 'and (list 'spatiallyDisconnected '?x Room) (list bird '?x))
                                 (list caged '?x)))
                  C)
        (v/assert kb (list bird Canary) C)
        (v/assert kb (list 'nonTangentialProperPart Canary Cage) C)
        (v/assert kb (list 'spatiallyDisconnected Cage Room) C)
        (is (seq (v/sentexes-matching kb (list caged Canary) C)) (str order))
        (doseq [s order] (v/assert kb (steps s) C))
        (is (qkb/inconsistent? space/rcc8 kb C) (str order))
        (is (empty? (v/sentexes-matching kb (list caged Canary) C)) (str order))
        (testing "and the contradicting fact leaving restores it"
          (v/retract! kb (v/handle-of kb (steps :sub) C))
          (is (seq (v/sentexes-matching kb (list caged Canary) C)) (str order)))))))

;; ---- forward chaining ----------------------------------------------------

(tu/deftest-kb forward-chaining-fires-on-an-asserted-qualitative-fact
  ;; a spatial relation is an ordinary stored sentex, so it goes on the agenda and fires
  ;; rules keyed by its predicate exactly like any other fact
  (tu/with-terms [A B tmpEnclosed]
    (v/assert-rule kb [(list 'nonTangentialProperPart '?x '?y)]
                   (list tmpEnclosed '?x) C {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (is (seq (v/sentexes-matching kb (list tmpEnclosed A) C))
        "the conclusion is derived and placed, with a justification naming the fact")
    (testing "and it is withdrawn when the fact it rests on goes"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart A B) C))
      (is (empty? (v/sentexes-matching kb (list tmpEnclosed A) C))))))

(tu/deftest-kb forward-chaining-fires-on-an-entailed-relation
  (tu/with-terms [A B D tmpEnclosed]
    (v/assert-rule kb [(list 'nonTangentialProperPart '?x D)]
                   (list tmpEnclosed '?x) C {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "the network entails that A is strictly inside D"
      (is (= #{:ntpp} (qkb/possible space/rcc8 kb C A D)))
      (is (nil? (v/handle-of kb (list 'nonTangentialProperPart A D) C))
          "and it is genuinely not stored"))
    (testing "the rule fires on it anyway, resting on the two facts that entailed it"
      (is (seq (v/sentexes-matching kb (list tmpEnclosed A) C)))
      (is (seq (v/sentexes-matching kb (list tmpEnclosed B) C))
          "B's relation to D is stored, so B's conclusion comes the ordinary way"))
    (testing "and breaking the chain withdraws what the entailment supported"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart A B) C))
      (is (empty? (v/sentexes-matching kb (list tmpEnclosed A) C)))
      (is (seq (v/sentexes-matching kb (list tmpEnclosed B) C))
          "B is untouched — it never depended on the entailment"))))

;; ---- which networks the re-join runs against ----------------------------
;; docs/qcn.md, "Which networks it joins against".

(defn- placements
  "The contexts a derived `(pred arg)` was placed in, read across every context rather
  than from one — `sentexes-matching` is level 2 and answers about the context it is
  handed, which is the wrong question when the point is *where* a firing landed."
  [kb pred arg]
  (set (map :context (v/sentexes-matching kb (list pred arg) '?ctx))))

(tu/deftest-kb an-entailment-only-a-context-below-two-others-sees-fires-a-forward-rule
  ;; the chain is split across two incomparable contexts
  (tu/with-terms [A B D CxA CxB CxBoth tmpEnclosed]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxBoth CxA) C)
    (v/assert kb (list 'genlCx CxBoth CxB) C)
    (v/assert-rule kb [(list 'nonTangentialProperPart '?x D)] (list tmpEnclosed '?x) C
                   {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) CxA)
    (v/assert kb (list 'nonTangentialProperPart B D) CxB)
    (testing "neither sibling composes the chain, and the context below both does"
      (is (= 8 (count (qkb/possible space/rcc8 kb CxA A D)))
          "A's context cannot see B's half, so A to D is wide open there")
      (is (= #{:ntpp} (qkb/possible space/rcc8 kb CxBoth A D)))
      (is (v/ask? kb (list 'nonTangentialProperPart A D) CxBoth))
      (is (nil? (v/handle-of kb (list 'nonTangentialProperPart A D) CxBoth))
          "and it is genuinely not stored anywhere"))
    (testing "so the rule fires on it, in the context that sees why"
      (is (= #{CxBoth} (placements kb tmpEnclosed A))))
    (testing "and the firing rests on both halves, so either one withdraws it"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart A B) CxA))
      (is (empty? (placements kb tmpEnclosed A))))))

(tu/deftest-kb a-fact-that-licenses-nothing-is-not-what-makes-that-firing-appear
  ;; a firing must not wait for an unrelated fact in the meeting context
  (tu/with-terms [A B D X Y CxA CxB CxBoth tmpEnclosed]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxBoth CxA) C)
    (v/assert kb (list 'genlCx CxBoth CxB) C)
    (v/assert-rule kb [(list 'nonTangentialProperPart '?x D)] (list tmpEnclosed '?x) C
                   {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) CxA)
    (v/assert kb (list 'nonTangentialProperPart B D) CxB)
    (let [before (placements kb tmpEnclosed A)]
      (v/assert kb (list 'nonTangentialProperPart X Y) CxBoth)
      (is (= before (placements kb tmpEnclosed A))
          "a fact about two other regions entirely decides nothing about this one")
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart X Y) CxBoth))
      (is (= before (placements kb tmpEnclosed A))
          "and taking it away again decides nothing either"))))

(tu/deftest-kb a-cross-context-chain-composes-one-arriving-fact-at-a-time
  ;; each arrival moves the meeting context's network and nothing else's
  (tu/with-terms [A B D E CxA CxB CxBoth tmpIn]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxBoth CxA) C)
    (v/assert kb (list 'genlCx CxBoth CxB) C)
    (v/assert-rule kb [(list 'partOfRegion '?x E)] (list tmpIn '?x) C {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) CxA)
    (is (empty? (placements kb tmpIn A)) "nothing reaches E yet")
    (v/assert kb (list 'nonTangentialProperPart B D) CxB)
    (is (empty? (placements kb tmpIn A)))
    (v/assert kb (list 'nonTangentialProperPart D E) CxA)
    (testing "the last link closes it for every region on the chain at once"
      (is (= #{CxBoth} (placements kb tmpIn A)))
      (is (= #{CxBoth} (placements kb tmpIn B)))
      (is (= #{CxA} (placements kb tmpIn D))
          "D reaches E within one context, so that is where its conclusion belongs"))))

(tu/deftest-kb a-context-holding-only-sub-predicate-facts-is-a-reader
  ;; CxSub holds no fact on a calculus predicate, only facts on a spec of one
  (doseq [order [[:rule :edge :f1 :f2] [:edge :f1 :f2 :rule] [:rule :f1 :f2 :edge]]]
    (tu/with-terms [A B D CxSub caged tmpInside]
      (v/assert kb (list 'genlCx CxSub C) C)
      (let [steps {:rule #(v/assert-rule kb [(list 'properPartOfRegion '?x D)]
                                         (list tmpInside '?x) C {:direction :forward})
                   :edge #(v/assert kb (list 'genl caged 'nonTangentialProperPart) C)
                   :f1   #(v/assert kb (list caged A B) CxSub)
                   :f2   #(v/assert kb (list caged B D) CxSub)}]
        (doseq [s order] ((steps s)))
        (is (v/ask? kb (list 'properPartOfRegion A D) CxSub) (str order))
        (is (= #{CxSub} (placements kb tmpInside A)) (str order))
        (testing "a fact leaving withdraws the firing a load without it never makes"
          (v/retract! kb (v/handle-of kb (list caged B D) CxSub))
          (is (not (v/ask? kb (list 'properPartOfRegion A D) CxSub)) (str order))
          (is (empty? (placements kb tmpInside A)) (str order)))))))

(tu/deftest-kb a-context-meeting-a-sub-predicate-edge-and-its-facts-is-a-reader
  ;; the edge making `caged` a spec of ntpp is visible from CxBoth and not from CxFacts
  (doseq [order [[:rule :edge :f1 :f2] [:edge :f1 :f2 :rule] [:rule :f1 :f2 :edge]]]
    (tu/with-terms [A B D CxEdge CxFacts CxBoth caged tmpInside]
      (v/assert kb (list 'genlCx CxEdge C) C)
      (v/assert kb (list 'genlCx CxFacts C) C)
      (v/assert kb (list 'genlCx CxBoth CxEdge) C)
      (v/assert kb (list 'genlCx CxBoth CxFacts) C)
      (let [steps {:rule #(v/assert-rule kb [(list 'properPartOfRegion '?x D)]
                                         (list tmpInside '?x) C {:direction :forward})
                   :edge #(v/assert kb (list 'genl caged 'nonTangentialProperPart) CxEdge)
                   :f1   #(v/assert kb (list caged A B) CxFacts)
                   :f2   #(v/assert kb (list caged B D) CxFacts)}]
        (doseq [s order] ((steps s)))
        (is (v/ask? kb (list 'properPartOfRegion A D) CxBoth) (str order))
        (is (not (v/ask? kb (list 'properPartOfRegion A D) CxFacts)) (str order))
        (is (= #{CxBoth} (placements kb tmpInside A)) (str order))
        (testing "the edge leaving withdraws the firing a load without it never makes"
          (v/retract! kb (v/handle-of kb (list 'genl caged 'nonTangentialProperPart) CxEdge))
          (is (empty? (placements kb tmpInside A)) (str order)))))))

(tu/deftest-kb a-variable-context-asks-what-some-reader-entails-not-what-all-facts-would
  ;; two incomparable contexts with no common descendant compose for no reader
  (tu/with-terms [A B D CxA CxB CxBoth]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) C)
    (v/assert kb (list 'nonTangentialProperPart A B) CxA)
    (v/assert kb (list 'nonTangentialProperPart B D) CxB)
    (testing "no context in the KB entails the composition"
      (is (not (v/ask? kb (list 'partOfRegion A D) CxA)))
      (is (not (v/ask? kb (list 'partOfRegion A D) CxB)))
      (is (not (v/ask? kb (list 'partOfRegion A D) C))))
    (testing "so neither does 'some context'"
      (is (not (v/ask? kb (list 'partOfRegion A D) '?ctx))))
    (testing "while what a reader does entail is still answered there and at ?ctx"
      (is (v/ask? kb (list 'partOfRegion A B) CxA))
      (is (v/ask? kb (list 'partOfRegion A B) '?ctx))
      (is (v/ask? kb (list 'partOfRegion B D) '?ctx)
          "from the other context, which no single reader shares with the first"))
    (testing "and an open goal enumerates the union of what the readers answer"
      (is (= #{[A B] [B D]}
             (set (for [s (v/ask kb (list 'properPartOfRegion '?x '?y) '?ctx)]
                    [(get s '?x) (get s '?y)])))))
    (testing "give the two a common descendant and there is now a reader that composes
              them, so 'some context' answers — the same question, a different lattice"
      (v/assert kb (list 'genlCx CxBoth CxA) C)
      (v/assert kb (list 'genlCx CxBoth CxB) C)
      (is (v/ask? kb (list 'partOfRegion A D) CxBoth))
      (is (v/ask? kb (list 'partOfRegion A D) '?ctx)))))

;; ---- a negative fact is a constraint, on every path a positive one is ----
;; A negative fact owes the re-join and the re-check a positive one owes.

(tu/deftest-kb a-negative-fact-arriving-after-the-rule-licenses-the-firing-it-entails
  ;; the companion below asserts the same two sentences the other way round
  (tu/with-terms [A D tmpApart]
    (v/assert-rule kb [(list 'spatiallyDisconnected '?x D)] (list tmpApart '?x) C
                   {:direction :forward})
    (v/assert kb (list 'not (list 'regionConnectedTo A D)) C)
    (testing "the negative fact alone determines the pair"
      (is (= #{:dc} (qkb/possible space/rcc8 kb C A D)))
      (is (v/ask? kb (list 'spatiallyDisconnected A D) C))
      (is (nil? (v/handle-of kb (list 'spatiallyDisconnected A D) C))))
    (is (= #{C} (placements kb tmpApart A)))))

(tu/deftest-kb a-negative-fact-arriving-before-the-rule-licenses-the-firing-it-entails
  (tu/with-terms [A D tmpApart]
    (v/assert kb (list 'not (list 'regionConnectedTo A D)) C)
    (v/assert-rule kb [(list 'spatiallyDisconnected '?x D)] (list tmpApart '?x) C
                   {:direction :forward})
    (is (= #{:dc} (qkb/possible space/rcc8 kb C A D)))
    (is (= #{C} (placements kb tmpApart A)))))

(tu/deftest-kb a-network-a-negative-fact-makes-impossible-withdraws-what-it-licensed
  (tu/with-terms [A B D tmpIn]
    (v/assert-rule kb [(list 'partOfRegion '?x D)] (list tmpIn '?x) C {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (is (= #{C} (placements kb tmpIn A)) "drawn from the composition")
    (v/assert kb (list 'not (list 'partOfRegion A D)) C)
    (testing "the network is now unsatisfiable and answers no goal of the calculus"
      (is (qkb/inconsistent? space/rcc8 kb C))
      (is (not (v/ask? kb (list 'partOfRegion A D) C))))
    (testing "so what it licensed is withdrawn, and comes back when the clash goes"
      (is (empty? (placements kb tmpIn A)))
      (v/retract! kb (v/handle-of kb (list 'not (list 'partOfRegion A D)) C))
      (is (= #{C} (placements kb tmpIn A))))))

;; ---- the invariant underneath all of the above ---------------------------

(defn- shuffled
  "`coll` permuted by a seeded PRNG, so a failure reproduces."
  [seed coll]
  (let [r (java.util.Random. seed)
        a (java.util.ArrayList. ^java.util.Collection (vec coll))]
    (java.util.Collections/shuffle a r)
    (vec a)))

(defn- qualitative-case
  "A rule, four facts of mixed polarity, two contexts and the context below both, over
  the terms `t` names: the `genlCx` setup, the six steps an order permutes, and the
  derived set a KB holds afterwards, placement contexts included."
  [{:syms [A B D P Q X Y CxA CxB CxBoth tmpIn tmpApart]}]
  {:setup   [(list 'genlCx CxA 'CxUniverse)
             (list 'genlCx CxB 'CxUniverse)
             (list 'genlCx CxBoth CxA)
             (list 'genlCx CxBoth CxB)]
   :steps   [;; the containment chain, split so only CxBoth composes it
             #(v/assert % (list 'nonTangentialProperPart A B) CxA)
             #(v/assert % (list 'nonTangentialProperPart B D) CxB)
             ;; a negative fact, which narrows P/Q to DC by complement alone
             #(v/assert % (list 'not (list 'regionConnectedTo P Q)) CxA)
             ;; and one about two regions neither pair mentions
             #(v/assert % (list 'nonTangentialProperPart X Y) CxB)
             #(v/assert-rule % [(list 'partOfRegion '?x D)] (list tmpIn '?x)
                             'CxUniverse {:direction :forward})
             #(v/assert-rule % [(list 'spatiallyDisconnected '?x Q)] (list tmpApart '?x)
                             'CxUniverse {:direction :forward})]
   :derived (fn [k]
              (set (for [pred [tmpIn tmpApart]
                         s    (v/sentexes-matching k (list pred '?x) '?ctx)]
                     [(:sentence s) (:context s)])))})

(defn- agree-on-something
  "Every order's derived set is one set, holding the two firings only the case's
  contexts and negative fact make."
  [answers {:syms [A P CxA CxBoth tmpIn tmpApart]}]
  (testing "every order agrees, and on something rather than on nothing"
    (is (apply = answers))
    (is (contains? (first answers) [(list tmpIn A) CxBoth])
        "the composition only CxBoth sees")
    (is (contains? (first answers) [(list tmpApart P) CxA])
        "and the relation only the negative fact determines")))

(tu/deftest-kb the-same-qualitative-knowledge-derives-the-same-belief-in-sampled-orders
  ;; Three of the orders the `^:slow` test below runs, into the namespace's KB, each on
  ;; fresh terms that are read back to their base names before the sets are compared.
  (let [names   '[A B D P Q X Y CxA CxB CxBoth tmpIn tmpApart]
        answers (for [seed (range 3)]
                  (let [t    (zipmap names (map #(tu/fresh-term (tu/term-role %) %) names))
                        back (zipmap (vals t) (keys t))
                        {:keys [setup steps derived]} (qualitative-case t)]
                    (doseq [s setup] (v/assert kb s 'CxUniverse))
                    (doseq [step (shuffled seed steps)] (step kb))
                    (walk/postwalk-replace back (derived kb))))]
    (agree-on-something (vec answers) (zipmap names names))))

(tu/deftest-kb ^:slow the-same-qualitative-knowledge-derives-the-same-belief-in-any-order
  ;; `qualitative-case` in eight orders, rules permuted with the facts, each into a KB
  ;; built from nothing: every order reaches the identical derived set
  (tu/with-terms [A B D P Q X Y CxA CxB CxBoth tmpIn tmpApart]
    (let [t       (zipmap '[A B D P Q X Y CxA CxB CxBoth tmpIn tmpApart]
                          [A B D P Q X Y CxA CxB CxBoth tmpIn tmpApart])
          {:keys [setup steps derived]} (qualitative-case t)
          run     (fn [order]
                    (let [k (doto (tu/isolated-fresh)
                              (tu/load-core!)
                              (v/add-prover (space/spatial-prover)))]
                      (doseq [s setup] (v/assert k s 'CxUniverse))
                      (doseq [step order] (step k))
                      (derived k)))]
      (agree-on-something (mapv #(run (shuffled % steps)) (range 8)) t))))

(deftest a-context-edge-arriving-last-composes-what-it-lets-a-reader-see
  ;; each `genlCx` edge putting `CxQlBoth` under a fact's context arrives last in one
  ;; ordering; the edges-first ordering is the control
  (let [ops    {:e1 #(v/assert % '(genlCx CxQlBoth CxQlA) 'CxUniverse)
                :e2 #(v/assert % '(genlCx CxQlBoth CxQlB) 'CxUniverse)
                :f1 #(v/assert % '(nonTangentialProperPart QlA QlB) 'CxQlA)
                :f2 #(v/assert % '(nonTangentialProperPart QlB QlD) 'CxQlB)
                :r  #(v/assert % '(implies (partOfRegion ?x QlD) (ql_in ?x)) 'CxUniverse
                               {:direction :forward})}
        orders [[:e1 :e2 :f1 :f2 :r]
                [:e2 :f1 :f2 :r :e1]
                [:e1 :r :f2 :f1 :e2]
                [:r :f1 :f2 :e2 :e1]]
        run    (fn [order]
                 (let [k (doto (tu/isolated-fresh)
                           (tu/load-core!)
                           (v/add-prover (space/spatial-prover)))]
                   (try
                     (v/assert k '(genlCx CxQlA CxUniverse) 'CxUniverse)
                     (v/assert k '(genlCx CxQlB CxUniverse) 'CxUniverse)
                     (doseq [op order] ((ops op) k))
                     (boolean (seq (v/sentexes-matching k '(ql_in QlA) 'CxQlBoth)))
                     (finally (tu/clear-kb! k)))))]
    (doseq [order orders]
      (is (run order) (str "the composition only CxQlBoth sees, in the order " order)))))

;; ---- inconsistency is reported, not merely silent ------------------------

(tu/deftest-kb an-unsatisfiable-network-reaches-the-violations-ledger
  (tu/with-terms [A B]
    (v/clear-violations! kb)
    (v/assert kb (list 'spatiallyDisconnected A B) C)
    (v/assert kb (list 'spatiallyEqual A B) C)
    (testing "the query answers nothing, as before"
      (is (not (v/ask? kb (list 'regionOverlaps A B) C))))
    (testing "and now says why, in the ledger the engine already keeps"
      (let [es (filter #(= :qualitative-inconsistency (:violation %)) (v/violations kb))]
        (is (= 1 (count es)))
        (is (= :rcc8 (:calculus (first es))))
        (is (= C (:context (first es))))
        (is (contains? (set (:pairs (:detail (first es)))) [A B])
            "the pair the reader emptied is named, since the facts about it clash
             outright rather than through a composition")))
    (testing "a second query does not re-report — the pass is memoized on the network,
              and a cache hit records nothing"
      (v/ask? kb (list 'regionOverlaps A B) C)
      (v/ask? kb (list 'partOfRegion A B) C)
      (is (= 1 (count (filter #(= :qualitative-inconsistency (:violation %))
                              (v/violations kb))))))
    (testing "but a change of belief yields a different network, and reports again"
      (v/retract! kb (v/handle-of kb (list 'spatiallyEqual A B) C))
      (v/clear-violations! kb)
      (is (v/ask? kb (list 'regionDiscreteFrom A B) C))
      (is (empty? (filter #(= :qualitative-inconsistency (:violation %))
                          (v/violations kb)))
          "and the consistent network reports nothing at all"))))

(tu/deftest-kb an-inconsistency-only-composition-finds-is-reported-without-a-pair
  (tu/with-terms [A B D]
    (v/clear-violations! kb)
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (v/assert kb (list 'after A D) C)
    (is (not (v/ask? kb (list 'before A B) C)))
    (let [e (first (filter #(= [:qualitative-inconsistency :allen] [(:violation %) (:calculus %)])
                           (v/violations kb)))]
      (is (some? e))
      (is (nil? (:pairs (:detail e)))
          "no single pair is at fault — every constraint is satisfiable as written, and
           only composing them empties one")
      (is (= #{A B D} (set (:nodes (:detail e))))))))

(defn- inconsistencies [kb]
  (filterv #(= :qualitative-inconsistency (:violation %)) (v/violations kb)))

(defn- by-calculus [es]
  (into {} (map (juxt :calculus identity)) es))

(tu/deftest-kb a-write-that-makes-a-network-unsatisfiable-files-its-entry-at-the-write
  ;; no rule joins on the calculus and nothing reads the network: the settle asks
  (tu/with-terms [A B]
    (v/assert kb (list 'before A B) C)
    (is (empty? (inconsistencies kb)))
    (v/assert kb (list 'after A B) C)
    (let [es (inconsistencies kb)
          e  (:allen (by-calculus es))]
      (is (= 2 (count es)) "filed by the write, before any read")
      (is (= [:allen C] [(:calculus e) (:context e)]))
      (is (= [A B] (:nodes (:detail e))))
      (testing "the two Allen facts' endpoint orders leave the point network unsatisfiable too"
        (is (= (set (for [x [A B] f ['StartFn 'EndFn]] (list f x)))
               (set (:nodes (:detail (:point (by-calculus es)))))))))
    (testing "a read of the same network files nothing more"
      (is (not (v/ask? kb (list 'before A B) C)))
      (is (= 2 (count (inconsistencies kb)))))))

(tu/deftest-kb try-assert-refuses-a-write-that-makes-a-network-unsatisfiable
  (tu/with-terms [A B D E]
    (let [h (v/assert kb (list 'before A B) C)
          e (try (v/try-assert kb (list 'after A B) C) nil
                 (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= [:definitional-clash :unsatisfiable-network] [(:type e) (:violation e)]))
      (is (= [h] (mapv :handle (:clashes-with e))) "the stored fact the pass blames")
      (is (= {:calculus :allen :context C :nodes [A B]}
             (select-keys (:detail e) [:calculus :context :nodes])))
      (testing "and the call stores nothing and files nothing"
        (is (nil? (v/handle-of kb (list 'after A B) C)))
        (is (true? (:consistent? (v/qualitative-network kb :allen C))))
        (is (empty? (inconsistencies kb))))
      (testing "a write into a satisfiable component beside an unsatisfiable one is stored"
        (v/assert kb (list 'after A B) C)
        (is (some? (v/try-assert kb (list 'before D E) C))))
      (testing "{:refuse-unsatisfiable? false} stores the write"
        (is (some? (v/try-assert kb (list 'after D E) C {:refuse-unsatisfiable? false})))
        (is (false? (:consistent? (v/qualitative-network kb :allen C))))))))

(tu/deftest-kb a-feed-event-carries-the-network-its-settle-made-unsatisfiable
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (let [events (atom [])
          t      (v/watch kb #(swap! events conj %))]
      (try
        (v/assert kb (list 'before B D) C)
        (is (nil? (:unsatisfiable (last @events))) "a satisfiable network rides on nothing")
        (v/assert kb (list 'after A D) C)
        (let [[e :as es] (:unsatisfiable (last @events))]
          (is (= 1 (count es)))
          (is (= (:allen (by-calculus (inconsistencies kb))) e) "the ledger's entry, in the ledger's shape")
          (is (= #{A B D} (set (:nodes (:detail e))))))
        (finally (v/unwatch kb t))))))

;; ---- the calculi are independent ----------------------------------------

(tu/deftest-kb two-calculi-over-one-kb-do-not-see-each-other
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'before A B) C)
    (testing "each answers its own predicates from its own network"
      (is (v/ask? kb (list 'partOfRegion A B) C))
      (is (v/ask? kb (list 'precedes A B) C)))
    (testing "and neither is disturbed by the other's facts"
      (is (= #{:ntpp} (qkb/possible space/rcc8 kb C A B)))
      (is (= #{:before} (iv/possible-allen-relations kb C A B))))
    (testing "a spatially impossible network leaves the interval one answering"
      (v/assert kb (list 'spatiallyDisconnected A B) C)
      (is (not (v/ask? kb (list 'partOfRegion A B) C)))
      (is (v/ask? kb (list 'precedes A B) C)))))

;; ---- the resident network -----------------------------------------------
;; These count builds, not calls.

(defn- counting-builds
  "Run `f` with `qcn-kb/build-network` counted, and return `[result build-count]`."
  [f]
  (let [builds (atom 0)
        built  @#'qkb/build-network]
    (with-redefs-fn {#'qkb/build-network (fn [& args] (swap! builds inc) (apply built args))}
      (fn [] [(f) @builds]))))

(tu/deftest-kb the-network-is-resident-between-reads
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (let [n1 (qkb/network kb space/rcc8 C)
          n2 (qkb/network kb space/rcc8 C)]
      (is (identical? n1 n2) "the second read is the resident value, not a rebuild"))
    (testing "keyed by calculus and context, so neither collides"
      (qkb/network kb iv/allen C)
      ;; a calculus keys with an unqualified keyword; the Allen read reads the point
      ;; network too, and adds the tolerance its metric narrowing reads to its key
      (is (= #{[:rcc8 C] [:allen C] [:point C]}
             (into #{} (comp (filter #(and (simple-keyword? (first %)) (= C (second %))
                                           (not-any? keyword? (drop 2 %))))
                             (map #(vec (take 2 %))))
                   (keys @(reasoning/qcn kb))))))
    (testing "and the Allen read leaves its narrowing's own read resident beside them —
              the metric problem, under a key of `stp`'s namespace rather than a calculus
              name, so the two cannot collide either"
      (is (some #(= [::stp/problem C] (take 2 %)) (filter vector? (keys @(reasoning/qcn kb))))))
    (testing "three top-level queries with nothing between them read once"
      ;; the clock is bumped by hand so the first of the three pays a build; without it
      ;; the count is zero, the KB already holding what the asserts above left resident
      (observe/note-change)
      (let [[_ builds] (counting-builds #(dotimes [_ 3] (v/ask? kb (list 'partOfRegion A B) C)))]
        (is (= 1 builds) (str "expected one read, got " builds))))))

(tu/deftest-kb a-mutation-rebuilds-the-resident-network
  ;; residency is not staleness: what makes it sound is that every determinant of a
  ;; network moves the clock.  A store, a retraction and a defeat are the three routes.
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (is (= #{:ntpp} (qkb/possible space/rcc8 kb C A B)))
    (testing "a stored fact"
      (v/assert kb (list 'nonTangentialProperPart B D) C)
      (is (= #{:ntpp} (qkb/possible space/rcc8 kb C A D))
          "the composition the new fact licensed, off a network read after it landed"))
    (testing "a retraction"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart B D) C))
      (is (= (:universe space/rcc8-algebra) (qkb/possible space/rcc8 kb C A D))))
    (testing "a defeat — the fact stays stored and stops being read"
      (v/assert kb (list 'nonTangentialProperPart B D) C {:strength :default})
      (is (= #{:ntpp} (qkb/possible space/rcc8 kb C B D)))
      (v/assert kb (list 'not (list 'nonTangentialProperPart B D)) C {:strength :monotonic})
      (is (some? (v/handle-of kb (list 'nonTangentialProperPart B D) C))
          "the positive is still stored")
      (is (not (contains? (qkb/possible space/rcc8 kb C B D) :ntpp))
          "and out of the network, its believed negation narrowing by the complement"))))

(tu/deftest-kb the-resident-interval-network-answers-the-tolerance-bound-at-the-read
  ;; a gap of 1e-6 s between two intervals reads as `:before` at the default tolerance
  ;; and as `:meets` at 1e-3; no write moves the clock between the first three reads
  (tu/with-terms [I J Is Ie Js Je]
    (doseq [[i s e] [[I Is Ie] [J Js Je]]]
      (v/assert kb (list 'startOf i s) C)
      (v/assert kb (list 'endOf i e) C))
    (v/assert kb (list 'temporalDistance Is Ie '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Js Je '(QuantityFn 3 Hour)) C)
    (v/assert kb (list 'temporalDistance Ie Js '(QuantityFn 0.000001 Second)) C)
    (let [read #(iv/possible-allen-relations kb C I J)
          wide #(binding [provers/*quantity-tolerance* 1e-3] (read))]
      (is (= #{:before} (read)))
      (is (= #{:meets} (wide)) "a rebound tolerance reaches the resident network")
      (is (= #{:before} (read)) "and the default reading stays resident beside it")
      (observe/note-change)
      (is (= #{:meets} (wide)) "a rebuild under the binding")
      (is (= #{:before} (read)) "leaves the default reading to the default tolerance"))))

(tu/deftest-kb a-warm-started-pass-answers-what-a-cold-one-answers
  ;; grown one fact at a time, against the network a batch load computes
  (tu/with-terms [Hub]
    (let [regions (mapv #(symbol (str "TmpChain" % "Node")) (range 6))
          ;; a containment chain, so every pair composes and the closure is dense
          facts   (map (fn [a b] (list 'nonTangentialProperPart a b))
                       regions (concat (rest regions) [Hub]))]
      (doseq [[i f] (map-indexed vector facts)]
        (v/assert kb f C)
        (let [warm (:constraints (v/qualitative-network kb :rcc8 C))
              ;; the reference sweep over the raw network: a read through the engine would hit
              ;; the pass cache the warm run just filled
              cold (qcn/path-consistent-naive (qkb/network kb space/rcc8 C)
                                              (qkb/nodes (qkb/network kb space/rcc8 C))
                                              space/rcc8-algebra)]
          (is (= cold warm) (str "step " i ": the warm-started closure differs")))))))

(tu/deftest-kb a-rule-join-over-many-bindings-reads-the-network-once
  ;; the case residency exists for: a qualitative antecedent is solved once per binding of
  ;; the join variable, and every solve after the first is served from the KB
  (tu/with-terms [Hub tmpThing tmpNear]
    (let [regions (mapv #(symbol (str "TmpRegion" % "Node")) (range 12))]
      (doseq [r regions]
        (v/assert kb (list 'nonTangentialProperPart r Hub) C)
        (v/assert kb (list tmpThing r) C))
      (v/assert-rule kb [(list tmpThing '?x) (list 'partOfRegion '?x Hub)]
                     (list tmpNear '?x) C {:direction :backward})
      (observe/note-change)                            ; as above: pay the first read here
      ;; `vec`, in case the engine hands back a lazy seq: an unrealized one would do
      ;; its reading after the counter came off
      (let [[answers builds] (counting-builds
                              #(vec (v/query kb (list tmpNear '?x) C {:max-depth 2})))]
        (is (= 12 (count answers)))
        (is (= 1 builds)
            (str "one network read for the whole 12-binding join, got " builds))))))

;; ---- the re-join is semi-naive ------------------------------------------
;; docs/qcn.md, "The re-join is semi-naive, over the pairs that moved".

(defn- links!
  "Links `from`..`to` of a chain under `pred`, nodes named `<prefix><i>`, each link
  relating *i* to *i-1* — the structure that makes every pair compose, whichever calculus
  `pred` belongs to."
  ([kb pred prefix n opts] (links! kb pred prefix 1 n opts))
  ([kb pred prefix from to opts]
   (let [node #(symbol (str prefix %))]
     (doseq [i (range from to)]
       (v/assert kb (list pred (node i) (node (dec i))) C opts)))))

(defn- chain!
  "A containment chain of regions — `links!` under RCC-8's `nonTangentialProperPart`."
  ([kb prefix n opts] (links! kb 'nonTangentialProperPart prefix 1 n opts))
  ([kb prefix from to opts] (links! kb 'nonTangentialProperPart prefix from to opts)))

(defn- derived
  "The derived `pred` tuples over a chain named from `prefix`, as the chain's own
  **numbers** — so two loads under different names compare directly."
  [kb pred prefix arity]
  (let [num #(when-let [m (re-matches (re-pattern (str prefix "(\\d+)")) (str %))]
               (parse-long (second m)))]
    (set (for [sx (v/sentexes-matching kb (cons pred (subvec '[?x ?y] 0 arity)) C)
               :when (not= 'not (first (:sentence sx)))
               :let  [t (mapv num (rest (:sentence sx)))]
               :when (every? some? t)]
           t))))

(tu/deftest-kb a-narrowed-rejoin-derives-what-a-full-one-derives
  ;; an interleaved load and a deferred one into one KB, including a rule with two
  ;; qualitative antecedents
  (tu/with-terms [tmpContained tmpNested]
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list tmpContained '?x) C {:direction :forward})
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y) (list 'properPartOfRegion '?y '?z)]
                   (list tmpNested '?x '?z) C {:direction :forward})
    (chain! kb "TmpInterleaved" 9 nil)
    (chain! kb "TmpDeferred" 9 {:chain? false})
    (v/forward-chain kb {})
    (is (= (derived kb tmpContained "TmpInterleaved" 1)
           (derived kb tmpContained "TmpDeferred" 1))
        "one qualitative antecedent")
    (is (seq (derived kb tmpContained "TmpInterleaved" 1)) "and it derived something at all")
    (is (= (derived kb tmpNested "TmpInterleaved" 2)
           (derived kb tmpNested "TmpDeferred" 2))
        "two qualitative antecedents — the delta rule's own case")
    (is (= (* 7 8 1/2) (count (derived kb tmpNested "TmpInterleaved" 2)))
        "every pair two proper-part steps apart, which is the whole transitive closure")))

(tu/deftest-kb the-delta-is-generic-over-the-calculus
  ;; a second calculus, since nothing in the delta knows an algebra
  (tu/with-terms [tmpLate]
    (v/assert-rule kb [(list 'precedes '?x '?y)] (list tmpLate '?y) C {:direction :forward})
    (links! kb 'after "TmpNow" 9 nil)
    (links! kb 'after "TmpThen" 9 {:chain? false})
    (v/forward-chain kb {})
    (is (= (derived kb tmpLate "TmpNow" 1)
           (derived kb tmpLate "TmpThen" 1)))
    (is (= 8 (count (derived kb tmpLate "TmpNow" 1)))
        "every interval but the last one precedes something")))

(tu/deftest-kb a-rule-arriving-mid-load-is-joined-over-both-halves
  ;; a rule's own full join sets no baseline, so a later delta reaches back past it
  (tu/with-terms [tmpEarly tmpAlways]
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list tmpAlways '?x) C {:direction :forward})
    (chain! kb "TmpBoth" 1 9 nil)
    (chain! kb "TmpLate" 1 5 nil)
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list tmpEarly '?x) C {:direction :forward})
    (chain! kb "TmpLate" 5 9 nil)
    (is (= (derived kb tmpAlways "TmpBoth" 1)
           (derived kb tmpEarly "TmpLate" 1))
        "the half asserted before the rule and the half after come out the same")
    (is (= 8 (count (derived kb tmpEarly "TmpLate" 1))))))

(tu/deftest-kb a-retraction-falls-back-to-a-full-rejoin
  ;; a cut chain's survivors against two chains never joined at all
  (tu/with-terms [tmpContained]
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list tmpContained '?x) C {:direction :forward})
    (chain! kb "TmpCut" 9 nil)
    (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart
                                         'TmpCut5 'TmpCut4)
                                C))
    ;; the same two fragments, told to the KB as fragments
    (doseq [[a b] [[1 0] [2 1] [3 2] [4 3] [6 5] [7 6] [8 7]]]
      (v/assert kb (list 'nonTangentialProperPart
                         (symbol (str "TmpWhole" a)) (symbol (str "TmpWhole" b)))
                C))
    (is (= (derived kb tmpContained "TmpCut" 1)
           (derived kb tmpContained "TmpWhole" 1))
        "the cut chain believes what the two fragments do")
    (is (not (v/ask? kb (list 'properPartOfRegion 'TmpCut8 'TmpCut0) C))
        "and the composition across the cut is gone")))

;; The delta itself, with no rule asserted, so the engine records no baseline of its
;; own.

(tu/deftest-kb a-delta-with-no-baseline-is-all-and-an-unchanged-network-moves-nothing
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (is (= :all (:moved (qkb/join-delta kb space/rcc8 C)))
        "nothing has been joined over this network, so nothing may be skipped")
    (let [{:keys [baseline]} (qkb/join-delta kb space/rcc8 C)]
      (qkb/note-joined kb space/rcc8 C baseline))
    (is (= #{} (:moved (qkb/join-delta kb space/rcc8 C)))
        "and immediately afterwards there is nothing to re-join")
    (testing "an arriving fact moves the pairs it composes with, and only those"
      (v/assert kb (list 'nonTangentialProperPart D A) C)
      (let [moved (:moved (qkb/join-delta kb space/rcc8 C))]
        (is (set? moved) "a real delta, not the fallback")
        (is (contains? moved [D A]) "the pair the fact itself narrowed")
        (is (contains? moved [D B]) "and the pair its composition reached")))))

(tu/deftest-kb a-join-baseline-outlives-the-resident-cache-clearing
  ;; the resident cache clears wholesale at its bound; the baselines are kept apart
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (qkb/note-joined kb space/rcc8 C (:baseline (qkb/join-delta kb space/rcc8 C)))
    (is (= #{} (:moved (qkb/join-delta kb space/rcc8 C)))
        "nothing has moved since the network was joined over")
    (let [pressure 400]
      (dotimes [i pressure] (observe/cached (reasoning/qcn kb) [::pressure i] (fn [_] i)))
      (is (< (count @(reasoning/qcn kb)) pressure)
          "the resident cache clears wholesale rather than growing past its bound"))
    (is (= #{} (:moved (qkb/join-delta kb space/rcc8 C)))
        "and the baseline is where it was left, so the next re-join is still a delta")))

(deftest a-wipe-stops-carrying-the-join-baselines
  ;; its own KB: `clear!` empties the store, which the neutral fixture refuses
  (let [kb (doto (v/open-kb tu/plain-memory-space)
             (tu/clear-kb!)
             (tu/load-core!)
             (v/add-prover (space/spatial-prover)))]
    (try
      (v/assert kb (list 'nonTangentialProperPart 'TmpWipedA 'TmpWipedB) C)
      (qkb/note-joined kb space/rcc8 C (:baseline (qkb/join-delta kb space/rcc8 C)))
      (is (seq @(reasoning/qcn-joined kb)) "a baseline is standing")
      (v/clear! kb)
      (is (= {} @(reasoning/qcn-joined kb))
          "the wipe took it with the rest of the resident state")
      (is (= :all (:moved (qkb/join-delta kb space/rcc8 C)))
          "so the next re-join runs over everything, as it does on a KB never joined")
      (finally (tu/clear-kb! kb)))))

(tu/deftest-kb a-lost-handle-makes-the-delta-all
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (qkb/note-joined kb space/rcc8 C (:baseline (qkb/join-delta kb space/rcc8 C)))
    (is (= #{} (:moved (qkb/join-delta kb space/rcc8 C))))
    (testing "a retraction"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart B D) C))
      (is (= :all (:moved (qkb/join-delta kb space/rcc8 C)))))
    (testing "a defeat, which takes the handle out of the network without removing it"
      (v/assert kb (list 'nonTangentialProperPart B D) C {:strength :default})
      (qkb/note-joined kb space/rcc8 C (:baseline (qkb/join-delta kb space/rcc8 C)))
      (v/assert kb (list 'not (list 'nonTangentialProperPart B D)) C {:strength :monotonic})
      (is (= :all (:moved (qkb/join-delta kb space/rcc8 C)))))))

(tu/deftest-kb a-context-the-fact-is-invisible-from-has-an-empty-delta
  ;; the delta is per network, and a network is per context — an arriving fact narrows the
  ;; ones that see it and leaves the rest exactly where they were
  (tu/with-terms [A B D CxSibling1 CxSibling2]
    (doseq [c [CxSibling1 CxSibling2]]
      (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'nonTangentialProperPart A B) CxSibling1)
    (v/assert kb (list 'nonTangentialProperPart A B) CxSibling2)
    (doseq [c [CxSibling1 CxSibling2]]
      (qkb/note-joined kb space/rcc8 c (:baseline (qkb/join-delta kb space/rcc8 c))))
    (v/assert kb (list 'nonTangentialProperPart B D) CxSibling1)
    (is (seq (:moved (qkb/join-delta kb space/rcc8 CxSibling1)))
        "the context the fact landed in moved")
    (is (= #{} (:moved (qkb/join-delta kb space/rcc8 CxSibling2)))
        "its sibling cannot see the fact, so its network is where it was left")))

(tu/deftest-kb a-write-that-leaves-a-network-unmoved-leaves-it-resident
  ;; The write moves the change clock, so the sibling's network is read again; the read
  ;; equals the resident value, which stays, and the delta compares no pair.
  (tu/with-terms [A B D E CxSibling1 CxSibling2]
    (doseq [c [CxSibling1 CxSibling2]]
      (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'nonTangentialProperPart A B) CxSibling1)
    (v/assert kb (list 'nonTangentialProperPart B D) CxSibling1)
    (qkb/note-joined kb space/rcc8 CxSibling1 (:baseline (qkb/join-delta kb space/rcc8 CxSibling1)))
    (let [before (qkb/network kb space/rcc8 CxSibling1)
          diffs  (atom 0)
          real   @#'qkb/differing-pairs]
      (v/assert kb (list 'nonTangentialProperPart D E) CxSibling2)
      (is (identical? before (qkb/network kb space/rcc8 CxSibling1)))
      (with-redefs-fn {#'qkb/differing-pairs (fn [& args] (swap! diffs inc) (apply real args))}
        #(is (= #{} (:moved (qkb/join-delta kb space/rcc8 CxSibling1)))))
      (is (zero? @diffs)))))

(tu/deftest-kb the-rejoin-enumerates-the-pairs-that-moved-not-every-pair
  ;; an arrival answers the n pairs it moved, not the n(n-1)/2 the chain entails
  (tu/with-terms [tmpContained]
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list tmpContained '?x) C {:direction :forward})
    (chain! kb "TmpMoved" 12 nil)
    (let [calls (atom 0)
          real  @#'qkb/support]
      (with-redefs-fn {#'qkb/support (fn [& args] (swap! calls inc) (apply real args))}
        (fn [] (v/assert kb (list 'nonTangentialProperPart 'TmpMoved12 'TmpMoved11) C)))
      (is (= 78 (count (v/ask kb (list 'properPartOfRegion '?x '?y) C)))
          "thirteen regions in a chain entail every one of the 78 nested pairs")
      (is (<= @calls 26)
          (str "the arrival moved 13 pairs and their converses; a full re-join would have "
               "answered 78, and it answered " @calls)))))

