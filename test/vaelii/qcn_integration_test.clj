;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-integration-test
  "Where the qualitative calculi meet the rest of the engine.

  Each algebra's own namespace tests it in isolation; this one tests the protocol they all
  reach through `vaelii.impl.qcn-kb` — what a registered prover is *reachable from*, what
  it is not, and what it reports when the facts it reads cannot all hold.  Several of
  these behaviours fall out of the registry being a KB-held list rather than being
  designed in, which is exactly why they need pinning: nothing else would notice if a
  change to the prover engine took them away."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.space :as space]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; both spatial calculi and the interval one, all three provers registered — the point
;; being that they coexist without seeing each other's facts
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxSpace "upper"] [CxTime "upper"]])
                        (v/add-prover (space/spatial-prover))
                        (v/add-prover (iv/allen-prover)))))

(def ^:private C 'CxUniverse)

;; ---- reachable from a rule ----------------------------------------------

(tu/deftest-kb a-rule-antecedent-is-discharged-by-the-prover
  ;; The node engine's leaf is `solve-goal`, the whole registry, which is what makes a
  ;; rule's antecedent answerable by *any* registered prover.  So a rule can join on a
  ;; spatial relation nobody stored — the composition is found during the proof.
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
  ;; `exceptWhen` evaluates its query over the **registry**, which expands no rule, and
  ;; the registry is the KB's own list, so a registered prover is in it.  A rule can
  ;; therefore state its exception in terms of a relation the network derives rather than
  ;; one anybody stored.
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
  ;; An entailed relation has no handle, so for a long time it could fire nothing: there
  ;; was no antecedent for a justification to rest on, and a conclusion nothing can
  ;; withdraw is worse than one never drawn.  Support closes it — the entailment names
  ;; the stored facts behind it, and those become the firing's antecedents.
  (tu/with-terms [A B D tmpEnclosed]
    (v/assert-rule kb [(list 'nonTangentialProperPart '?x D)]
                   (list tmpEnclosed '?x) C {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "the network entails that A is strictly inside D"
      (is (= #{:ntpp} (space/possible-relations kb C A D)))
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
;; A qualitative fact cannot be matched at a trigger position, so every forward rule
;; mentioning its calculus is re-joined against "the networks the calculus has facts
;; in".  A network is what a *reader* sees, though, and the readers are not only the
;; contexts holding a fact: a context inheriting two of them sees both their facts at
;; once and composes what neither composes alone.

(defn- placements
  "The contexts a derived `(pred arg)` was placed in, read across every context rather
  than from one — `sentexes-matching` is level 2 and answers about the context it is
  handed, which is the wrong question when the point is *where* a firing landed."
  [kb pred arg]
  (set (map :context (v/sentexes-matching kb (list pred arg) '?ctx))))

(tu/deftest-kb an-entailment-only-a-context-below-two-others-sees-fires-a-forward-rule
  ;; The containment chain is split across two incomparable contexts, so neither
  ;; composes it and the entailment exists only for a reader inheriting both.  `ask`
  ;; answers it there, and forward chaining owes the same answer: otherwise the same
  ;; knowledge derives different things according to which context its halves were
  ;; stated in, and the conclusion's own placement context is the one that cannot see
  ;; the reason it was drawn.
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
      (is (= 8 (count (space/possible-relations kb CxA A D)))
          "A's context cannot see B's half, so A to D is wide open there")
      (is (= #{:ntpp} (space/possible-relations kb CxBoth A D)))
      (is (v/ask? kb (list 'nonTangentialProperPart A D) CxBoth))
      (is (nil? (v/handle-of kb (list 'nonTangentialProperPart A D) CxBoth))
          "and it is genuinely not stored anywhere"))
    (testing "so the rule fires on it, in the context that sees why"
      (is (= #{CxBoth} (placements kb tmpEnclosed A))))
    (testing "and the firing rests on both halves, so either one withdraws it"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart A B) CxA))
      (is (empty? (placements kb tmpEnclosed A))))))

(tu/deftest-kb a-fact-that-licenses-nothing-is-not-what-makes-that-firing-appear
  ;; The sharp form of the same defect, and the reason it is one rather than a missing
  ;; optimization: reading the network only where facts are *stated* makes a conclusion
  ;; wait for some unrelated fact to be stated in the context that composes it.  Belief
  ;; would then depend on an assertion that entails nothing — and survive its
  ;; retraction, so a reload of the very same content would not reproduce the KB.
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
  ;; The re-join is semi-naive — it joins over the pairs that moved since these rules
  ;; were last joined, per context — so the contexts it takes a delta for have to be the
  ;; same ones it solves against.  Growing the chain a fact at a time is what asks: each
  ;; arrival moves the meeting context's network and nothing else's.
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

(tu/deftest-kb a-variable-context-asks-what-some-reader-entails-not-what-all-facts-would
  ;; `?ctx` means "in some context" everywhere else in the engine, and a calculus prover
  ;; owes the same reading.  Two incomparable contexts with *no* common descendant
  ;; are the case that separates it: their facts compose for no reader at all, since no
  ;; context inherits both, and a single read over the union of what every context holds
  ;; would report a relation nowhere entailed.
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
;; A believed `(not (P a b))` narrows the pair by the complement of P's denotation, so
;; it moves the network exactly as a positive fact does — it can entail a relation
;; nobody stated, and it can make the theory impossible.  Both halves of the wiring a
;; positive fact triggers are therefore owed to it: the re-join that finds the new
;; entailment, and the re-check that withdraws what an impossible network licensed.

(tu/deftest-kb a-negative-fact-arriving-after-the-rule-licenses-the-firing-it-entails
  ;; `(not (regionConnectedTo A D))` rules out all seven relations C denotes and leaves
  ;; DC, so it *entails* `(spatiallyDisconnected A D)` with nothing positive stored.
  ;; The companion below asserts the identical two sentences the other way round; the
  ;; pair is an order-independence test, and the order is the only difference.
  (tu/with-terms [A D tmpApart]
    (v/assert-rule kb [(list 'spatiallyDisconnected '?x D)] (list tmpApart '?x) C
                   {:direction :forward})
    (v/assert kb (list 'not (list 'regionConnectedTo A D)) C)
    (testing "the negative fact alone pins the pair"
      (is (= #{:dc} (space/possible-relations kb C A D)))
      (is (v/ask? kb (list 'spatiallyDisconnected A D) C))
      (is (nil? (v/handle-of kb (list 'spatiallyDisconnected A D) C))))
    (is (= #{C} (placements kb tmpApart A)))))

(tu/deftest-kb a-negative-fact-arriving-before-the-rule-licenses-the-firing-it-entails
  (tu/with-terms [A D tmpApart]
    (v/assert kb (list 'not (list 'regionConnectedTo A D)) C)
    (v/assert-rule kb [(list 'spatiallyDisconnected '?x D)] (list tmpApart '?x) C
                   {:direction :forward})
    (is (= #{:dc} (space/possible-relations kb C A D)))
    (is (= #{C} (placements kb tmpApart A)))))

(tu/deftest-kb a-network-a-negative-fact-makes-impossible-withdraws-what-it-licensed
  ;; The second half of the same wiring.  An impossible theory is mined for nothing, so
  ;; a firing the network licensed is blocked the way an excepted one is — and which
  ;; polarity the impossibility arrived in cannot decide whether that happens, or the
  ;; KB reports the network unsatisfiable and goes on believing a conclusion drawn
  ;; from it.
  (tu/with-terms [A B D tmpIn]
    (v/assert-rule kb [(list 'partOfRegion '?x D)] (list tmpIn '?x) C {:direction :forward})
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (is (= #{C} (placements kb tmpIn A)) "drawn from the composition")
    (v/assert kb (list 'not (list 'partOfRegion A D)) C)
    (testing "the network is now unsatisfiable and answers no goal of the calculus"
      (is (space/inconsistent? kb C))
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

(tu/deftest-kb ^:slow the-same-qualitative-knowledge-derives-the-same-belief-in-any-order
  ;; The oracle for the whole protocol, and the property the two sections above are each one
  ;; instance of: a rule, four facts of mixed polarity, two contexts and the context
  ;; below both — asserted in eight orders, into a KB built from nothing each time, and
  ;; every order must reach the identical derived set, placement contexts included.
  ;;
  ;; Orders rather than a fixed expectation because the failure this guards is never a
  ;; wrong answer, it is a *missing* one: a network read where no reader stands, or an
  ;; arrival that queues no re-join, both leave a KB that is merely less informative than
  ;; it should be — and reads as correct against anything but another order of the same
  ;; content.  The rules are permuted along with the facts, since "the rule arrived last"
  ;; is exactly the case a rule's own full join would otherwise paper over.
  (tu/with-terms [A B D P Q X Y CxA CxB CxBoth tmpIn tmpApart]
    (let [setup  [(list 'genlCx CxA 'CxUniverse)
                  (list 'genlCx CxB 'CxUniverse)
                  (list 'genlCx CxBoth CxA)
                  (list 'genlCx CxBoth CxB)]
          steps  [;; the containment chain, split so only CxBoth composes it
                  #(v/assert % (list 'nonTangentialProperPart A B) CxA)
                  #(v/assert % (list 'nonTangentialProperPart B D) CxB)
                  ;; a negative fact, which pins P/Q to DC by complement alone
                  #(v/assert % (list 'not (list 'regionConnectedTo P Q)) CxA)
                  ;; and one about two regions neither pair mentions
                  #(v/assert % (list 'nonTangentialProperPart X Y) CxB)
                  #(v/assert-rule % [(list 'partOfRegion '?x D)] (list tmpIn '?x)
                                  'CxUniverse {:direction :forward})
                  #(v/assert-rule % [(list 'spatiallyDisconnected '?x Q)] (list tmpApart '?x)
                                  'CxUniverse {:direction :forward})]
          derived (fn [k]
                    (set (for [pred [tmpIn tmpApart]
                               s    (v/sentexes-matching k (list pred '?x) '?ctx)]
                           [(:sentence s) (:context s)])))
          run    (fn [order]
                   (let [k (doto (tu/isolated-fresh)
                             (core-context/load-into)
                             (seed/load-context 'CxSpace "upper")
                             (v/add-prover (space/spatial-prover)))]
                     (doseq [s setup] (v/assert k s 'CxUniverse))
                     (doseq [step order] (step k))
                     (derived k)))
          answers (mapv #(run (shuffled % steps)) (range 8))]
      (testing "every order agrees, and on something rather than on nothing"
        (is (apply = answers))
        (is (contains? (first answers) [(list tmpIn A) CxBoth])
            "the composition only CxBoth sees")
        (is (contains? (first answers) [(list tmpApart P) CxA])
            "and the relation only the negative fact pins")))))

;; ---- inconsistency is reported, not merely silent ------------------------

(tu/deftest-kb an-unsatisfiable-network-reaches-the-violations-ledger
  (tu/with-terms [A B]
    (v/assert kb (list 'spatiallyDisconnected A B) C)
    (v/assert kb (list 'spatiallyEqual A B) C)
    (v/clear-violations! kb)
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
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (v/assert kb (list 'after A D) C)
    (v/clear-violations! kb)
    (is (not (v/ask? kb (list 'before A B) C)))
    (let [e (first (filter #(= :qualitative-inconsistency (:violation %)) (v/violations kb)))]
      (is (= :allen (:calculus e)))
      (is (nil? (:pairs (:detail e)))
          "no single pair is at fault — every constraint is satisfiable as written, and
           only composing them empties one")
      (is (= #{A B D} (set (:nodes (:detail e))))))))

;; ---- the calculi are independent ----------------------------------------

(tu/deftest-kb two-calculi-over-one-kb-do-not-see-each-other
  (tu/with-terms [A B]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'before A B) C)
    (testing "each answers its own predicates from its own network"
      (is (v/ask? kb (list 'partOfRegion A B) C))
      (is (v/ask? kb (list 'precedes A B) C)))
    (testing "and neither is disturbed by the other's facts"
      (is (= #{:ntpp} (space/possible-relations kb C A B)))
      (is (= #{:before} (iv/possible-allen-relations kb C A B))))
    (testing "a spatially impossible network leaves the interval one answering"
      (v/assert kb (list 'spatiallyDisconnected A B) C)
      (is (not (v/ask? kb (list 'partOfRegion A B) C)))
      (is (v/ask? kb (list 'precedes A B) C)))))

;; ---- the resident network -----------------------------------------------
;; Reading a network is one belief-filtered read per predicate of the calculus per
;; polarity, and every consumer asks for one constantly.  So it lives on the KB between
;; reads, stamped with `observe/change-clock`, and is rebuilt exactly when the engine has
;; mutated something.  These count *builds*, not calls: the call count is the point of
;; the mechanism, and the build count is what it costs.

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
      ;; a calculus names its key with an unqualified keyword; every other resident read
      ;; on this atom keys off its own namespace, which is what keeps them apart
      (is (= #{[:rcc8 C] [:allen C]}
             (into #{} (filter (comp simple-keyword? first)) (keys @(reasoning/qcn kb))))))
    (testing "and the Allen read leaves its narrowing's own read resident beside them —
              the metric problem, under a key of `stp`'s namespace rather than a calculus
              name, so the two cannot collide either"
      (is (contains? (set (keys @(reasoning/qcn kb))) [::stp/problem C])))
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
    (is (= #{:ntpp} (space/possible-relations kb C A B)))
    (testing "a stored fact"
      (v/assert kb (list 'nonTangentialProperPart B D) C)
      (is (= #{:ntpp} (space/possible-relations kb C A D))
          "the composition the new fact licensed, off a network read after it landed"))
    (testing "a retraction"
      (v/retract! kb (v/handle-of kb (list 'nonTangentialProperPart B D) C))
      (is (= (:universe space/rcc8-algebra) (space/possible-relations kb C A D))))
    (testing "a defeat — the fact stays stored and stops being read"
      (v/assert kb (list 'nonTangentialProperPart B D) C {:strength :default})
      (is (= #{:ntpp} (space/possible-relations kb C B D)))
      (v/assert kb (list 'not (list 'nonTangentialProperPart B D)) C {:strength :monotonic})
      (is (some? (v/handle-of kb (list 'nonTangentialProperPart B D) C))
          "the positive is still stored")
      (is (not (contains? (space/possible-relations kb C B D) :ntpp))
          "and out of the network, its believed negation narrowing by the complement"))))

(tu/deftest-kb a-warm-started-pass-answers-what-a-cold-one-answers
  ;; The pass is warm-started off the previous resident answer whenever the new network
  ;; narrows the old — which is what every arriving fact does, so a load takes that path at
  ;; every step.  Grown one fact at a time here, and checked against the network a KB that
  ;; saw the same facts as one batch computes: the two must be identical pair for pair, or
  ;; the shortcut has invented an entailment.
  (tu/with-terms [Hub]
    (let [regions (mapv #(symbol (str "TmpChain" % "Node")) (range 6))
          ;; a containment chain, so every pair composes and the closure is dense
          facts   (map (fn [a b] (list 'nonTangentialProperPart a b))
                       regions (concat (rest regions) [Hub]))]
      (doseq [[i f] (map-indexed vector facts)]
        (v/assert kb f C)
        (let [warm (:constraints (v/qualitative-network kb :rcc8 C))
              ;; the reference sweep, straight over the raw network — **not** a second
              ;; read through the engine, which would hit the content-keyed pass cache the
              ;; warm run just filled and so compare the answer with itself
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
;; A qualitative fact cannot be matched at a trigger position — a new `ntpp` fact licenses
;; a `partOfRegion` antecedent and the two are unrelated by genl — so every rule mentioning
;; the calculus is re-joined whenever one arrives.  Re-joining over every pair the network
;; entails means the nth arriving fact redoes the (n-1)th's work, so the join runs over the
;; pairs whose entailment has **moved** since these same rules were last joined
;; (`qcn-kb/join-delta`).  What must not change is which conclusions come out.

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
  ;; Two loads of the same shape into one KB: the first interleaved, so every arrival takes
  ;; a delta, and the second `{:chain? false}` with one `forward-chain`, so the whole of it
  ;; arrives as one delta against the first load's baseline.  Both must derive the same
  ;; tuples, including the rule with **two** qualitative antecedents — the case a delta that
  ;; narrowed both at once would silently halve.
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
  ;; Nothing in the delta knows an algebra — it diffs closed networks and counts handles —
  ;; so a second calculus is the check that it is the *protocol* being tested rather than
  ;; RCC-8.  Allen's `after` chain is the same shape in a different algebra, and the two
  ;; networks coexist in one KB without seeing each other.
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
  ;; A rule is fully joined at its own datum, and that join is not what sets the baseline —
  ;; only a re-join of *all* the calculus's rules may claim that.  So the delta a later fact
  ;; takes can reach back past the rule's arrival, which costs a repeat the TMS dedups and
  ;; must lose nothing.  Checked against the same chain with the rule there from the start.
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
  ;; A widening is not computable from the answer it widened, so a delta cannot describe
  ;; one — the handle it lost is what says so, and the re-join goes back to full.  Checked
  ;; against a chain that was never joined at all: the survivors of a cut chain are two
  ;; shorter chains, and the KB must believe exactly what it would have believed if that is
  ;; what it had been told.
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

;; The three tests above are end to end — they say the conclusions are right.  These three
;; are about the delta itself, because "right conclusions" is also what a delta that always
;; answered `:all` would produce, and the whole value of one is in the cases where it does
;; not.  None of them asserts a rule: with no rule mentioning the calculus the engine never
;; re-joins and so never records a baseline of its own, which leaves the mechanism visible.

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
  ;; A baseline is bookkeeping rather than a memo, and that is the whole difference: a
  ;; memo lost is recomputed at its own cost, where a baseline lost cannot be recomputed
  ;; at all — what it records is the network as of the last re-join, a moment that has
  ;; passed — so every later delta for that calculus and context silently falls back to a
  ;; full join.  The resident network cache is cleared wholesale when it grows past its
  ;; bound, so a baseline sharing that atom is dropped by traffic that is not about it.
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
  ;; The baselines are the one piece of resident state a *clock* tick does not reach —
  ;; that is what they are for, a claim about a network rather than a memo of one — so
  ;; the wholesale wipe is the only thing that can retire them, and it is where the
  ;; other resident maps are retired.  Its own KB: `clear!` empties the store, which is
  ;; the one thing the neutral fixture will not accept.
  (let [kb (doto (v/open-kb tu/plain-memory-space)
             (tu/clear-kb!)
             (core-context/load-into)
             (seed/load-context 'CxSpace "upper")
             (v/add-prover (space/spatial-prover)))]
    (v/assert kb (list 'nonTangentialProperPart 'TmpWipedA 'TmpWipedB) C)
    (qkb/note-joined kb space/rcc8 C (:baseline (qkb/join-delta kb space/rcc8 C)))
    (is (seq @(reasoning/qcn-joined kb)) "a baseline is standing")
    (v/clear! kb)
    (is (= {} @(reasoning/qcn-joined kb))
        "the wipe took it with the rest of the resident state")
    (is (= :all (:moved (qkb/join-delta kb space/rcc8 C)))
        "so the next re-join runs over everything, as it does on a KB never joined")
    (tu/clear-kb! kb)))

(tu/deftest-kb a-lost-handle-makes-the-delta-all
  ;; a derived support is a union along whatever chain narrowed it, so a handle that goes
  ;; moves the support at pairs whose *constraint* never moved — undiffable pair by pair,
  ;; and answered coarsely instead
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

(tu/deftest-kb the-rejoin-enumerates-the-pairs-that-moved-not-every-pair
  ;; The structural claim a timing cannot make: an arriving fact answers the pairs it
  ;; moved, not the pairs the network entails.  In a containment chain those are n and
  ;; n(n-1)/2 — one `support` call per pair answered, so counting them says which of the
  ;; two the join ran over.
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
