;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.context-scoping-test
  "**No context is affected by sentexes in contexts it does not inherit.**

  The closure reads are scoped (`taxonomy_scoped_test`), the checks are scoped
  (`disjoint_test`), and a clash only a descendant can see is reported rather than
  refused (`exposure_test`).  This namespace is about the *consumers*: every place the
  engine reaches for a taxonomy edge, a rule, an equality, or a metadata mark on
  behalf of some context, and could reach past what that context can see.

  Each mechanism gets a **pair** — the leak and its control — because a scoping test
  that only checks the negative passes just as well when the feature is broken
  outright.  The lattice throughout is two siblings under CxUniverse, neither
  seeing the other, which is the sharpest shape: whatever A knows, B must not, and B
  is a perfectly ordinary context that inherits the whole shipped ontology.

  Two of these are **order-independence** tests wearing a visibility coat.  A rule
  that fires by subsumption rests on the `genl` edge it subsumed through as much as on
  its antecedents, so that edge has to be visible from the placement *and* has to
  re-trigger the firing when it arrives late.  Get either wrong and the same three
  sentences derive different things in different orders, which is the one thing belief
  may not depend on (docs/nmtms.md).

  The deliberately-global reads are pinned here too, at the end — a reader finding
  `genl?` refusing a cycle across invisible contexts should find it *stated* rather
  than have to decide whether it is a bug."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- siblings!
  "Wire `a` and `b` as incomparable contexts under CxUniverse: each sees the
  whole shipped ontology, neither sees the other, and no context sees both."
  [kb a b]
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse))

;; ---- the genl closure, walked on someone's behalf -----------------------
;;
;; A walk scoped to context C reads the edges of every context C inherits, and none of
;; the edges of a context it does not.

(tu/deftest-kb a-genl-walk-reads-the-contexts-it-inherits-and-no-others
  (tu/with-terms [sub_t mid_t sup_t CxA CxChild CxOther]
    (siblings! kb CxA CxOther)
    (v/assert kb (list 'genlCx CxChild CxA) 'CxUniverse)
    (v/assert kb (list 'genl sub_t mid_t) CxA)
    (v/assert kb (list 'genl mid_t sup_t) CxA)
    (testing "the asserting context sees its own chain"
      (is (contains? (v/genls kb sub_t CxA) sup_t))
      (is (v/genl? kb sub_t sup_t CxA)))
    (testing "a context that inherits it sees it too"
      (is (contains? (v/genls kb sub_t CxChild) sup_t))
      (is (v/genl? kb sub_t sup_t CxChild)))
    (testing "a context that does not inherit it sees none of it"
      (is (not (contains? (v/genls kb sub_t CxOther) sup_t)))
      (is (not (v/genl? kb sub_t sup_t CxOther))))
    (testing "and the downward walk agrees, node for node"
      (is (contains? (v/specs kb sup_t CxChild) sub_t))
      (is (not (contains? (v/specs kb sup_t CxOther) sub_t))))))

(tu/deftest-kb type-membership-follows-the-visible-edges
  (tu/with-terms [pug_t dog_t Rex CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genl pug_t dog_t) CxA)
    (v/assert kb (list pug_t Rex) CxB)
    (testing "B holds the membership but not the edge, so it does not hold the supertype"
      (is (seq (v/sentexes-matching kb (list pug_t Rex) CxB)))
      (is (= #{pug_t} (set (v/types-of kb Rex CxB))) "the asserted type, and only it")
      (is (not (v/isa? kb Rex dog_t CxB)))
      (is (not (v/isa? kb Rex dog_t CxA))
          "nor from A, which has the edge and not the membership — each half alone
           proves nothing, which is the point"))
    (testing "every retrieval level agrees — none answers what B cannot see"
      (is (every? #(empty? (v/lookup kb % (list dog_t Rex) CxB)) [2 3 4 5 6 7])))))

;; ---- forward chaining: the edge a subsumption match rests on ------------

(tu/deftest-kb a-firing-is-placed-only-where-its-subsumption-is-visible
  (tu/with-terms [fatherOf2 parentOf2 ancestorOf2 Tom Bob CxA CxB]
    (siblings! kb CxA CxB)
    ;; the predicate hierarchy is A's; the rule and the fact are B's
    (v/assert kb (list 'genl fatherOf2 parentOf2) CxA)
    (v/assert kb (list 'implies (list parentOf2 '?x '?y) (list ancestorOf2 '?x '?y)) CxB {:direction :forward})
    (v/assert kb (list fatherOf2 Tom Bob) CxB)
    (testing "B does not conclude on the strength of an edge it cannot see"
      (is (empty? (v/sentexes-matching kb (list ancestorOf2 Tom Bob) CxB)))
      (is (empty? (v/sentexes-matching kb (list ancestorOf2 Tom Bob)))))
    (testing "and the drop is reported, naming the subsumption rather than the facts"
      (let [vs (filter #(= :no-placement (:violation %)) (v/violations kb))]
        (is (seq vs))
        (is (= [fatherOf2] (get-in (first vs) [:detail :subsumed])))))))

(tu/deftest-kb a-firing-whose-subsumption-is-visible-is-placed
  (tu/with-terms [fatherOf3 parentOf3 ancestorOf3 Tom Bob CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genl fatherOf3 parentOf3) 'CxUniverse)
    (v/assert kb (list 'implies (list parentOf3 '?x '?y) (list ancestorOf3 '?x '?y)) CxB {:direction :forward})
    (v/assert kb (list fatherOf3 Tom Bob) CxB)
    (is (= [CxB] (mapv :context (v/sentexes-matching kb (list ancestorOf3 Tom Bob) CxB))))))

(tu/deftest-kb a-late-genl-edge-fires-what-it-newly-connects
  ;; the order-independence half: the edge arriving last must reach the facts already
  ;; stored, or the same three sentences mean different things in different orders
  (tu/with-terms [dog4_t animal4_t breathes4 Muffet]
    (v/assert kb (list 'genl animal4_t 'thing) 'CxUniverse)
    (v/assert kb (list 'implies (list animal4_t '?x) (list breathes4 '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog4_t Muffet) 'CxUniverse)
    (is (empty? (v/sentexes-matching kb (list breathes4 Muffet) 'CxUniverse))
        "nothing yet — dog4_t is not a kind of animal4_t")
    (v/assert kb (list 'genl dog4_t animal4_t) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list breathes4 Muffet) 'CxUniverse))
        "the edge arriving is what makes the stored fact match the rule")))

(tu/deftest-kb the-same-three-sentences-in-the-other-order-agree
  (tu/with-terms [dog5_t animal5_t breathes5 Muffet]
    (v/assert kb (list 'genl animal5_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog5_t animal5_t) 'CxUniverse)
    (v/assert kb (list 'implies (list animal5_t '?x) (list breathes5 '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog5_t Muffet) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list breathes5 Muffet) 'CxUniverse)))))

;; ---- backward chaining: a rule is a sentex ------------------------------

(tu/deftest-kb a-rule-in-an-invisible-context-answers-nothing
  (tu/with-terms [parentOf6 ancestorOf6 Tom Bob CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list parentOf6 '?x '?y) (list ancestorOf6 '?x '?y)))
              CxA)
    (v/assert kb (list parentOf6 Tom Bob) CxB)
    (testing "every backward path agrees: B does not reason with A's rule"
      (is (empty? (v/ask kb (list ancestorOf6 Tom Bob) CxB)))
      (is (empty? (v/prove kb (list ancestorOf6 Tom Bob) CxB)))
      (is (empty? (v/query kb (list ancestorOf6 Tom Bob) CxB {:max-depth 2})))
      (is (empty? (v/lookup kb 7 (list ancestorOf6 Tom Bob) CxB))))
    (testing "and the forward firing of that same rule agrees — no placement"
      (is (empty? (v/sentexes-matching kb (list ancestorOf6 Tom Bob)))))))

(tu/deftest-kb a-rule-the-goal-context-inherits-answers
  (tu/with-terms [parentOf7 ancestorOf7 Tom Bob CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list parentOf7 '?x '?y) (list ancestorOf7 '?x '?y)))
              'CxUniverse)
    (v/assert kb (list parentOf7 Tom Bob) CxB)
    (is (seq (v/query kb (list ancestorOf7 Tom Bob) CxB {:max-depth 2})))
    (is (seq (v/prove kb (list ancestorOf7 Tom Bob) CxB)))))

;; ---- the change feed: a watch matches through the edges its context sees -
;;
;; A standing query is a read that fires on a moved region, and it subsumes the region's
;; facts through the predicate-genl closure exactly as a rule antecedent does
;; (`res/match1`).  Walked globally, it fires on a match its own context cannot see —
;; while `ask` from that context answers nothing, so the feed and the query disagree
;; about one context.  The pair: the invisible edge and the visible one.

(tu/deftest-kb a-watch-does-not-fire-through-a-predicate-edge-it-cannot-see
  (tu/with-terms [fdog9 fanimal9 Muffet9 CxA CxE]
    (siblings! kb CxA CxE)
    (v/assert kb (list 'genl fdog9 fanimal9) CxE)         ; the edge lives where CxA cannot see it
    (let [seen (atom [])]
      (v/watch kb (list fanimal9 '?x) CxA (fn [e] (swap! seen conj e)))
      (v/assert kb (list fdog9 Muffet9) CxA)
      (is (not (v/ask? kb (list fanimal9 Muffet9) CxA))
          "the fact is a dog CxA can see, but the edge that makes it an animal is not")
      (is (empty? @seen)
          "so the watch on (fanimal ?x) does not fire, agreeing with ask"))))

(tu/deftest-kb a-watch-fires-through-a-predicate-edge-it-can-see
  (tu/with-terms [gdog9 ganimal9 Rex9 CxA CxE]
    (siblings! kb CxA CxE)
    (v/assert kb (list 'genl gdog9 ganimal9) CxA)         ; the edge is visible to the watcher
    (let [seen (atom [])]
      (v/watch kb (list ganimal9 '?x) CxA (fn [e] (swap! seen conj e)))
      (v/assert kb (list gdog9 Rex9) CxA)
      (is (v/ask? kb (list ganimal9 Rex9) CxA) "CxA sees the edge, so Rex is an animal")
      (is (= 1 (count @seen)) "and the watch fires on the subsumed match")
      (is (= Rex9 (get-in (first @seen) [:believed-added 0 :bindings '?x]))
          "binding the argument the subsumption unified"))))

;; ---- transitiveInArg: a claim travels the edges the asker can see ---------

(tu/deftest-kb an-inherited-claim-stops-at-an-invisible-edge
  (tu/with-terms [biggerThan8 retriever_t dog8_t cat8_t CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'binary_predicate biggerThan8) 'CxUniverse)
    (v/assert kb (list 'transitiveInArg biggerThan8 1 'genl) 'CxUniverse)
    (v/assert kb (list 'genl retriever_t dog8_t) CxA)
    (v/assert kb (list biggerThan8 dog8_t cat8_t) CxB)
    (is (empty? (v/ask kb (list biggerThan8 retriever_t cat8_t) CxB))
        "B holds the claim about dogs and no edge putting retrievers under them")))

(tu/deftest-kb an-inherited-claim-travels-a-visible-edge
  (tu/with-terms [biggerThan9 retriever_t dog9_t cat9_t CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'binary_predicate biggerThan9) 'CxUniverse)
    (v/assert kb (list 'transitiveInArg biggerThan9 1 'genl) 'CxUniverse)
    (v/assert kb (list 'genl retriever_t dog9_t) 'CxUniverse)
    (v/assert kb (list biggerThan9 dog9_t cat9_t) CxB)
    (is (seq (v/ask kb (list biggerThan9 retriever_t cat9_t) CxB)))))

;; The pair above travels `genl`, whose transitivity is the engine's own.  When the
;; relation is an ordinary predicate, the *licence to walk it at all* is a stored
;; `(transitive R)`, and `inherit/usable-relation?` reads that from the asker's vantage
;; like everything else — which on this KB deliberately changes nothing, and the
;; control below is why.  There is no leak to pair it with here: the leak is
;; unconstructible on a KB carrying CxCore, and `inherit_test` builds the pair on
;; one that does not.

(tu/deftest-kb predicate-metadata-is-a-licence-the-whole-kb-holds
  ;; `transitive` is a `decontextualized_predicate`, so A's declaration is *lifted* into
  ;; CxUniverse and B sees it — predicate metadata is a claim about the vocabulary
  ;; rather than a claim of a context, and the lift is what says so.  So B may walk
  ;; the relation, and what licensed it is the lift, not a peek into a sibling.
  (tu/with-terms [cursed8 begat8 A8 B8 CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'transitive begat8) CxA)
    (is (seq (v/sentexes-matching kb (list 'transitive begat8) 'CxUniverse))
        "the lift put it where every context can see it")
    (v/assert kb (list 'transitiveInArg cursed8 1 begat8) CxB)
    (v/assert kb (list begat8 A8 B8) CxB)
    (v/assert kb (list cursed8 B8) CxB)
    (is (seq (v/ask kb (list cursed8 A8) CxB))
        "so the claim travels the relation for B as much as for A")))

;; ---- equality: a merge renames only what it is visible from -------------
;;
;; The one that *loses* knowledge rather than adding it.  Migration and supersession
;; check visibility per sentex; if the goal rewrite does not, a context asks under a
;; spelling nothing renamed and gets nothing back — for a fact it still believes.

(tu/deftest-kb an-invisible-merge-does-not-rename-a-context-s-question
  (tu/with-terms [canFly10 Clark Superman CxA CxB]
    (siblings! kb CxA CxB)
    (let [h (v/assert kb (list canFly10 Clark) CxB)]
      (v/assert kb (list 'rewriteOf Superman Clark) CxA)
      (testing "B keeps believing its fact"
        (is (v/in? kb h))
        (is (some? (v/handle-of kb (list canFly10 Clark) CxB))))
      (testing "...and can still retrieve it, under the only spelling B knows"
        (is (seq (v/sentexes-matching kb (list canFly10 Clark) CxB)))
        (is (seq (v/ask kb (list canFly10 Clark) CxB))))
      (testing "no twin was made in B — the merge is not B's to apply"
        (is (empty? (v/contexts-of kb (list canFly10 Superman)))))
      (testing "and the class reads scope with it"
        (is (not (v/same-class? kb Clark Superman CxB)))
        (is (v/same-class? kb Clark Superman CxA))
        (is (= Clark (v/representative kb Clark CxB)))
        (is (= Superman (v/representative kb Clark CxA)))))))

(tu/deftest-kb a-visible-merge-renames-and-supersedes
  (tu/with-terms [canFly11 Clark Superman CxA CxB]
    (siblings! kb CxA CxB)
    (let [h (v/assert kb (list canFly11 Clark) CxB)]
      (v/assert kb (list 'rewriteOf Superman Clark) 'CxUniverse)
      (is (not (v/in? kb h)) "the retired spelling stops being believed")
      (is (= [CxB] (vec (v/contexts-of kb (list canFly11 Superman))))
          "the twin is placed where the fact lives")
      (is (seq (v/sentexes-matching kb (list canFly11 Clark) CxB)) "the old question still works")
      (is (seq (v/sentexes-matching kb (list canFly11 Superman) CxB))))))

(tu/deftest-kb the-unique-name-assumption-survives-an-invisible-merge
  (tu/with-terms [Clark12 Superman12 CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'sameAs Clark12 Superman12) CxA)
    (is (seq (v/ask kb (list 'different Clark12 Superman12) CxB))
        "B has been told nothing, so the two names still denote two things there")
    (is (empty? (v/ask kb (list 'different Clark12 Superman12) CxA))
        "A has been told")))

(tu/deftest-kb a-functional-equality-is-derived-though-an-invisible-merge-exists
  ;; The functional-clash derivation skips a pair its idempotence guard finds already
  ;; merged.  Read globally, a merge in a sibling context suppressed a derivation the
  ;; reader is owed — so a context could hold two functional fillers for one argument
  ;; and merge neither, because some *other* context happened to merge them.
  (tu/with-terms [fp13 X13 V1 V2 CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'functional fp13) 'CxUniverse)
    (v/assert kb (list 'sameAs V1 V2) CxB)                 ; a merge CxA cannot see
    (is (not (v/same-class? kb V1 V2 CxA)) "CxA cannot see the sibling's merge")
    (v/assert kb (list fp13 X13 V1) CxA)
    (v/assert kb (list fp13 X13 V2) CxA)                   ; the functional clash
    (testing "CxA derives the equality its own two fillers license"
      (is (v/same-class? kb V1 V2 CxA)
          "the reader merges the fillers it stated, not skipping on an invisible merge"))
    (testing "and the sibling keeps its own merge"
      (is (v/same-class? kb V1 V2 CxB)))))

(tu/deftest-kb a-functional-equality-is-derived-across-two-genlcx-edges-from-below
  ;; The literal shape from GitHub issue #43's own repro: two contexts blind to each
  ;; other, each holding one of two clashing `functional` fillers, and a third context
  ;; wired under **both** -- not one edge widening a single existing ancestor set (the
  ;; order-independence suite covers that shape), but two separate edges whose union is
  ;; what first makes the pair jointly visible.  `special/equate-under-context-edge`'s
  ;; `readers` binding has to fold the contribution of both edges together: after only
  ;; one, the joining context still sees exactly one filler, and there is nothing yet to
  ;; merge.
  (tu/with-terms [fbP FbTom FbV1 FbV2 CxFbA CxFbB CxFbBelow]
    (siblings! kb CxFbA CxFbB)
    (v/assert kb (list 'functional fbP) 'CxUniverse)
    (v/assert kb (list fbP FbTom FbV1) CxFbA)
    (v/assert kb (list fbP FbTom FbV2) CxFbB)
    (testing "blind siblings hold one filler each and merge nothing"
      (is (not (v/same-class? kb FbV1 FbV2 CxFbA)))
      (is (not (v/same-class? kb FbV1 FbV2 CxFbB))))
    (v/assert kb (list 'genlCx CxFbBelow CxFbA) 'CxUniverse)
    (testing "one edge alone still sees only one of the two fillers"
      (is (not (v/same-class? kb FbV1 FbV2 CxFbBelow))))
    (v/assert kb (list 'genlCx CxFbBelow CxFbB) 'CxUniverse)
    (testing "both edges together complete the clash, and the reader below derives it"
      (is (v/same-class? kb FbV1 FbV2 CxFbBelow))
      (let [[lo hi] (sort [FbV1 FbV2])]
        (is (some? (v/handle-of kb (list 'equals lo hi) CxFbBelow)))))))

(tu/deftest-kb an-unmergeable-genlcx-clash-is-still-only-weighed-not-thrown-or-silent
  ;; This arm's job stops at the mergeable case (docs/equality.md, `mergeable-values?`) —
  ;; two *numbers* under a `functional` slot are the hard clash no equality can resolve,
  ;; and issue #43 leaves what happens there a deliberate open design question, not a
  ;; bug.  What this pins is only that adding `equate-under-context-edge` did not change
  ;; that path: a genlCx edge completing an unmergeable clash still neither throws nor
  ;; does nothing — CxUbBelow is the vantage and weighs the pair, and two `:default`
  ;; numbers tie, so both stand and `contradictions` names them.
  ;;
  ;; The KB is the namespace's and the violation ledger accumulates across tests
  ;; (`v/violations`), so the check is on the entries this test adds.  An earlier test's
  ;; `:no-placement` entry stays in the ledger after the fixture retracts its terms.
  (tu/with-terms [ubP UbTom CxUbA CxUbB CxUbBelow]
    (siblings! kb CxUbA CxUbB)
    (let [filed-before (set (v/violations kb))]
      (v/assert kb (list 'functional ubP) 'CxUniverse)
      (v/assert kb (list ubP UbTom 1980) CxUbA)
      (v/assert kb (list ubP UbTom 1990) CxUbB)
      (v/assert kb (list 'genlCx CxUbBelow CxUbA) 'CxUniverse)
      (is (empty? (v/contradictions kb))
          "one edge alone still sees only one of the two values")
      (v/assert kb (list 'genlCx CxUbBelow CxUbB) 'CxUniverse)
      (testing "the completed clash is weighed, not refused and not silent"
        (is (= [:functional] (mapv :kind (v/contradictions kb))))
        (is (empty? (remove filed-before (v/violations kb))) "decided is not exposed")
        (is (empty? (v/conflicts kb)))))))

;; ---- equality down a chain: the reader is not the fact's own context ----
;;
;; The sibling lattice above is the case migration *declines*: nothing sees both the
;; fact and the merge, so there is no reader to serve.  A **chain** is the case it has
;; to serve, and it is the one where "check visibility per sentex" stops being enough —
;; because the party whose spelling is at stake is whoever reads the fact, and that is
;; any context below it, each electing over a different set of visible edges.

(defn- nested!
  "Wire `inner` under `outer` under CxUniverse: a strict chain, so `inner` sees
  everything `outer` does and `outer` sees none of `inner`'s."
  [kb outer inner]
  (v/assert kb (list 'genlCx outer 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx inner outer) 'CxUniverse))

(tu/deftest-kb a-reader-below-the-fact-retrieves-it-under-the-name-it-elects
  ;; The fact is CxMid's; the merge is CxLeaf's alone.  Leaf sees both, so
  ;; Leaf elects Alpha — and a reader that can see a fact must be able to ask for it.
  (tu/with-terms [likes15 Tom15 Alpha15 Bravo15 CxMid CxLeaf]
    (nested! kb CxMid CxLeaf)
    (v/assert kb (list likes15 Tom15 Bravo15) CxMid)
    (v/assert kb (list 'rewriteOf Alpha15 Bravo15) CxLeaf)
    (testing "Mid is told nothing and keeps its fact under its own spelling"
      (is (v/ask? kb (list likes15 Tom15 Bravo15) CxMid))
      (is (not (v/ask? kb (list likes15 Tom15 Alpha15) CxMid))
          "and does not acquire a name only Leaf can justify"))
    (testing "Leaf sees the fact and sees the merge, so it can ask under either name"
      (is (v/ask? kb (list likes15 Tom15 Alpha15) CxLeaf)
          "the spelling Leaf elects")
      (is (v/ask? kb (list likes15 Tom15 Bravo15) CxLeaf)
          "and the retired one, which is rewritten to it"))
    (testing "the twin is placed in the context whose view elected it"
      (is (= [CxLeaf] (vec (v/contexts-of kb (list likes15 Tom15 Alpha15))))))
    (testing "and each reader gets the one fact once, under the name it elects"
      ;; Mid's spelling is believed where it lives and Leaf inherits it, so without a
      ;; reader-scoped staleness filter Leaf reports one fact twice under two names it
      ;; knows denote one thing — and every count over the answer set doubles
      (is (= [{'?x Alpha15}] (v/query kb (list likes15 Tom15 '?x) CxLeaf)))
      (is (= [{'?x Bravo15}] (v/query kb (list likes15 Tom15 '?x) CxMid))))))

(tu/deftest-kb a-merge-a-context-cannot-see-does-not-choose-its-spelling
  ;; A class split across the chain: Mid sees only Bravo~Charlie and elects Bravo;
  ;; Leaf sees Alpha~Bravo too and elects Alpha.  One fact, two readers, two normal
  ;; forms — and neither reader may be handed the other's.
  (tu/with-terms [likes16 Tom16 Alpha16 Bravo16 Charlie16 CxMid CxLeaf]
    (nested! kb CxMid CxLeaf)
    (v/assert kb (list 'rewriteOf Bravo16 Charlie16) CxMid)
    (v/assert kb (list 'rewriteOf Alpha16 Bravo16) CxLeaf)
    (v/assert kb (list likes16 Tom16 Charlie16) CxMid)
    (testing "each context elects over the edges it can see"
      (is (= Bravo16 (v/representative kb Charlie16 CxMid)))
      (is (= Alpha16 (v/representative kb Charlie16 CxLeaf))))
    (testing "Mid can still retrieve the fact it asserted"
      (is (v/ask? kb (list likes16 Tom16 Charlie16) CxMid)
          "under the retired spelling, which Mid's own election rewrites")
      (is (v/ask? kb (list likes16 Tom16 Bravo16) CxMid)
          "and under the one Mid elects"))
    (testing "Mid is not handed the spelling only Leaf's edge produces"
      (is (not (v/ask? kb (list likes16 Tom16 Alpha16) CxMid))))
    (testing "Leaf, which sees both edges, retrieves it under all three"
      (is (v/ask? kb (list likes16 Tom16 Alpha16) CxLeaf))
      (is (v/ask? kb (list likes16 Tom16 Bravo16) CxLeaf))
      (is (v/ask? kb (list likes16 Tom16 Charlie16) CxLeaf)))))

(tu/deftest-kb why-not-names-the-supersession-the-fact-s-own-context-elected
  ;; `why-not`'s `:superseded-by` is a read on behalf of the superseded fact's context —
  ;; the only context that supersedes it.  Mid elects Bravo over Charlie and stores the
  ;; twin; Leaf then elects Alpha over Bravo, which Mid cannot see.  The report must name
  ;; Bravo (what Mid elected and stored), not the global Alpha — a spelling Mid never
  ;; elected and never stored, whose handle would miss while the `:rewrites` map beside it
  ;; stays correct, so the report would contradict itself.
  (tu/with-terms [likes18 Tom18 Alpha18 Bravo18 Charlie18 CxMid CxLeaf]
    (nested! kb CxMid CxLeaf)
    (let [h (v/assert kb (list likes18 Tom18 Charlie18) CxMid)]
      (v/assert kb (list 'rewriteOf Bravo18 Charlie18) CxMid)
      (v/assert kb (list 'rewriteOf Alpha18 Bravo18) CxLeaf)
      (is (not= (v/representative kb Charlie18 CxMid) (v/representative kb Charlie18))
          "global and Mid-scoped election of the head diverge, so the read must choose")
      (let [wn (v/why-not kb h)
            sb (:superseded-by wn)]
        (is (= :superseded (:reason wn)) "the fact was restated under Mid's election")
        (is (= (list likes18 Tom18 (v/representative kb Charlie18 CxMid)) (:sentence sb))
            "the report names the spelling the fact's own context elected")
        (is (some? (:handle sb))
            "which is a spelling stored in that context, so the handle resolves")))))

(tu/deftest-kb deprecated-scopes-like-the-three-class-reads-beside-it
  ;; `representative` / `same-class?` / `equiv-class` each take a context; without one
  ;; `deprecated?` reports a retirement no reader outside the merge's ancestor set can see, and
  ;; the four reads of one partition disagree about one context.
  (tu/with-terms [Alpha17 Bravo17 CxMid CxLeaf]
    (nested! kb CxMid CxLeaf)
    (v/assert kb (list 'rewriteOf Alpha17 Bravo17) CxLeaf)
    (testing "the merge's own ancestor set sees the retirement"
      (is (v/deprecated? kb Bravo17 CxLeaf))
      (is (= Alpha17 (v/representative kb Bravo17 CxLeaf))))
    (testing "a context above it does not"
      (is (not (v/deprecated? kb Bravo17 CxMid)))
      (is (= Bravo17 (v/representative kb Bravo17 CxMid))
          "the control: Mid elects Bravo itself, so calling it deprecated contradicts"))
    (testing "the unscoped arity still answers globally"
      (is (v/deprecated? kb Bravo17)))))

;; ---- predicate metadata: declared in a theory, not published -----------

(tu/deftest-kb a-metadata-declaration-concludes-where-it-was-made
  (tu/with-terms [palOf13 CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'binary_predicate palOf13) CxA)
    (v/assert kb (list 'symmetric palOf13) CxA)
    (testing "the mark's own sentex is the declaring context's — its decontextualized
              copy lands in CxUniverse, below CxCore's sight"
      (is (seq (v/sentexes-matching kb (list 'symmetric palOf13) CxA)))
      (is (empty? (v/sentexes-matching kb (list 'symmetric palOf13) 'CxCore))))
    (testing "the two ways of asking give one answer, from either vantage — the mark is
              both the property and the (binary_predicate) type membership"
      (is (= (v/has-prop? kb :symmetric palOf13 CxA)
             (v/isa? kb palOf13 'symmetric CxA)))
      (is (= (v/has-prop? kb :symmetric palOf13 CxB)
             (v/isa? kb palOf13 'symmetric CxB))))))

(tu/deftest-kb a-derived-declaration-installs-live-not-only-on-recover
  ;; `recover` replays every stored sentex of the functor, so a declaration that
  ;; reaches the cache only there makes a restart change the answer
  (tu/with-terms [needsSep14 q1_t q2_t]
    (v/assert kb (list 'genl q1_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl q2_t 'thing) 'CxUniverse)
    (v/assert kb (list 'implies (list needsSep14 '?x) (list 'disjoint q1_t q2_t))
              'CxUniverse {:direction :forward})
    (v/assert kb (list needsSep14 'Go) 'CxUniverse)
    (is (v/disjoint? kb q1_t q2_t 'CxUniverse)
        "the rule-concluded separation constrains the moment it is believed")))

;; ---- what is global, and stated to be ----------------------------------
;;
;; Not leaks: each is a property of a structure the whole KB shares, and narrowing it
;; would break something worse than it fixes.  Pinned so the next reader does not have
;; to guess (docs/taxonomy.md, docs/contexts.md).

(tu/deftest-kb the-genl-cycle-check-is-global-on-purpose
  ;; A context-narrowed check would admit a globally cyclic edge, and a type cycle
  ;; claims two types are coextensive — a claim about *terms*, which is the equality
  ;; partition's job, and which would make a `disjoint` pair disjoint from itself.  So
  ;; the refusal is about what the edge means, not about what the reads can survive:
  ;; they survive a cycle either way, which is the test below.
  (tu/with-terms [a15_t b15_t CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genl a15_t b15_t) CxA)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'genl b15_t a15_t) CxB))
        "refused although B cannot see the edge it closes a cycle with")))

(tu/deftest-kb a-cycle-belief-assembles-is-answered-alike-by-every-reader-of-it
  ;; The check above reads the **active** adjacency, so belief walks around it: defeat an
  ;; edge, assert its reverse — nothing is cyclic while the first is out — then retract
  ;; the defeater and both stand.  Nothing refuses the result, so the reads owe it an
  ;; answer rather than an assumption, and the three readers of one question owe the
  ;; *same* answer.  The potential ranks the condensation, so the two types are level
  ;; rather than ordered, and a scoped walk pruned on a strict descent alone denies the
  ;; edge its own closure returns.
  (tu/with-terms [c18_t d18_t e18_t CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genl c18_t d18_t) CxA)
    (let [h (v/assert kb (list 'not (list 'genl c18_t d18_t)) CxA {:strength :monotonic})]
      (v/assert kb (list 'genl d18_t c18_t) CxA)    ; admitted: the first edge is out
      (v/retract! kb h))                                 ; and now both of them stand
    (v/assert kb (list 'genl e18_t 'thing) CxB)     ; a second asserting context
    (testing "A sees both edges, and every read of them agrees"
      (is (contains? (v/genls kb c18_t CxA) d18_t))
      (is (v/genl? kb c18_t d18_t CxA))
      (is (contains? (v/genls kb d18_t CxA) c18_t))
      (is (v/genl? kb d18_t c18_t CxA))
      (is (contains? (v/specs kb d18_t CxA) c18_t)))
    (testing "B sees neither, and every read of them agrees about that too"
      (is (not (contains? (v/genls kb c18_t CxB) d18_t)))
      (is (not (v/genl? kb c18_t d18_t CxB)))
      (is (not (v/genl? kb d18_t c18_t CxB))))))

(tu/deftest-kb the-genlCx-closure-is-global-on-purpose
  ;; visibility scoped by visibility is circular, and every genlCx edge is forced
  ;; into CxUniverse anyway (`forced_decontextualized_predicate`)
  (tu/with-terms [CxA CxB]
    (siblings! kb CxA CxB)
    (is (= ['CxUniverse] (vec (v/contexts-of kb (list 'genlCx CxA 'CxUniverse))))
        "the topology has one canonical home, whoever asserted the edge")))

(tu/deftest-kb argument-sorting-is-a-storage-key-and-so-is-global
  ;; a sentex has one key: if whether a predicate sorts its arguments varied by reader,
  ;; one literal would store under two keys and dedup, retraction and the mirror probe
  ;; would all break at once
  (tu/with-terms [palOf16 Bob Ann CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'binary_predicate palOf16) 'CxUniverse)
    (v/assert kb (list 'symmetric palOf16) CxA)
    (v/assert kb (list palOf16 Bob Ann) CxB)
    (is (seq (v/sentexes-matching kb (list palOf16 Ann Bob) CxB))
        "B retrieves the mirror, because storage sorted the arguments and storage
         does not vary by reader")))

(tu/deftest-kb an-open-context-query-requires-one-reader-to-see-the-whole-join
  ;; A **variable** context is the joint reading: the answer must hold from some one
  ;; vantage, and that vantage is unified into the variable the caller named.  So a
  ;; conjunctive read does *not* join literals no single context sees — an answer no reader
  ;; of the KB actually has.  The union is spelled `CxEverything`, the reading that asks
  ;; about the store rather than about what any reader holds (docs/contexts.md).
  (tu/with-terms [leftP17 rightP17 Item CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list leftP17 Item) CxA)
    (v/assert kb (list rightP17 Item) CxB)
    (let [goal [(list leftP17 '?x) (list rightP17 '?x)]]
      (is (empty? (v/prove kb goal '?ctx))
          "no context sees both, so the joint reading has no answer")
      (is (seq (v/prove kb goal 'CxEverything))
          "the union still joins them, under the name that means the union")
      (is (empty? (v/prove kb goal CxA))
          "asked from a context, it answers only what that context holds")
      (is (empty? (v/prove kb goal CxB))))
    (testing "and when a reader does see both, it answers and names itself"
      (tu/with-terms [CxBoth]
        (v/assert kb (list 'genlCx CxBoth CxA) 'CxUniverse)
        (v/assert kb (list 'genlCx CxBoth CxB) 'CxUniverse)
        (is (= [CxBoth] (mapv '?ctx (v/prove kb [(list leftP17 '?x) (list rightP17 '?x)]
                                             '?ctx))))))))

;; ---- (ist Ctx S) as a read ----------------------------------------------
;;
;; `ist` names the context a sentence is about, and a read resolves it exactly as
;; `assert` does — the named context winning over the argument.  The scoping question
;; this raises answers itself: the form grants **no** visibility a context argument did
;; not already grant, because naming A is what `(sentexes-matching kb S 'CxA)` has
;; always done.  That is what separates a read from a rule antecedent, where the same
;; shape is refused (`sentex/ist-rule-problem`): a caller asking about A has said so,
;; while a rule reading A on the sly decides belief from a context its own cannot see.

(tu/deftest-kb an-ist-read-is-a-spelling-of-the-context-argument
  (tu/with-terms [heldP18 Item CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list heldP18 Item) CxA)
    (let [goal (list heldP18 '?x)
          ist  (list 'ist CxA goal)]
      (testing "asked from B, which cannot see A, it answers exactly as naming A does"
        (is (= (mapv (juxt :sentence :context) (v/sentexes-matching kb goal CxA))
               (mapv (juxt :sentence :context) (v/sentexes-matching kb ist CxB)))
            "no visibility the context argument did not already carry")
        (is (seq (v/sentexes-matching kb ist CxB))
            "and it is a real answer rather than two empties agreeing"))
      (testing "the named context wins over the argument, as it does at assert"
        (is (= [CxA] (mapv :context (v/sentexes-matching kb ist 'CxUniverse))))
        (is (= [CxA] (mapv :context (v/sentexes-matching kb ist CxB)))))
      (testing "and a plain goal is untouched by any of it"
        (is (empty? (v/sentexes-matching kb goal CxB)))))))

(tu/deftest-kb every-read-taking-a-sentence-and-a-context-takes-an-ist
  ;; The rule is the whole surface, so the test is the whole surface: a reader should
  ;; not have to learn which entry point happens to have been wired.
  (tu/with-terms [litP19 Item CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list litP19 Item) CxA)
    (let [ist   (list 'ist CxA (list litP19 '?x))
          ist-g (list 'ist CxA (list litP19 Item))]
      (testing "the retrieval and reasoning entry points"
        (is (seq (v/sentexes-matching kb ist CxB)))
        (is (some? (v/handle-of kb ist-g CxB)))
        (is (seq (v/ask kb ist CxB)))
        (is (v/ask? kb ist-g CxB))
        (is (seq (v/prove kb ist CxB)))
        (is (v/provable? kb ist-g CxB))
        (is (seq (v/query kb ist CxB)))
        (is (v/query? kb ist-g CxB))
        (is (some? (v/query-plan kb ist CxB))))
      (testing "the anytime entry points"
        (is (seq (:results (v/ask-within kb ist CxB {:max-results 1}))))
        (is (seq (:results (v/prove-within kb ist CxB {:max-results 1})))))
      (testing "the level diagnostics"
        (is (seq (v/lookup kb 2 ist-g CxB)))
        (is (some? (:level (v/escalate kb ist-g CxB))))
        (is (some? (v/explain-levels kb ist-g CxB))))
      (testing "and why-not, which reports under the context it was told about"
        (let [r (v/why-not kb (list 'ist CxA (list litP19 'TmpAbsent19)) CxB)]
          (is (= :not-stored (:reason r)))
          (is (= CxA (:context r))))))))

(tu/deftest-kb an-ist-read-answers-at-each-entry-points-own-notion-of-a-context
  ;; The two families disagree, and the disagreement is theirs rather than ist's:
  ;; `sentexes-matching` is an exact-context retrieval, while the reasoning entry points answer
  ;; from everything the context inherits.  `(ist A S)` means "in A" under both readings
  ;; — a fact A inherits *is* true in A — so it is pinned rather than reconciled.
  (tu/with-terms [seenP20 Near Far CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list seenP20 Near) CxA)
    (v/assert kb (list seenP20 Far) 'CxUniverse)
    (let [ist (list 'ist CxA (list seenP20 '?x))]
      (is (= [Near] (mapv (comp second :sentence) (v/sentexes-matching kb ist CxB)))
          "retrieval answers the facts stored in A")
      (is (= #{Near Far} (into #{} (map '?x) (v/ask kb ist CxB)))
          "the registry answers what A inherits as well"))))

(tu/deftest-kb the-two-ist-read-shapes-that-are-refused-rather-than-answered-empty
  ;; Both would otherwise report nothing, which reads exactly like a true negative.
  (tu/with-terms [shapeP21 Item CxA]
    (v/assert kb (list shapeP21 Item) CxA)
    (testing "a wrong arity is assert's own :shape, on every read entry point"
      (doseq [bad [(list 'ist CxA)
                   (list 'ist CxA (list shapeP21 '?x) 'junk)]]
        (doseq [[label f] {"sentexes-matching" #(v/sentexes-matching kb bad 'CxUniverse)
                           "ask"               #(v/ask kb bad 'CxUniverse)
                           "prove"             #(v/prove kb bad 'CxUniverse)}]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (f))
                      (str label " refuses " (pr-str bad)))]
            (is (= :shape (:type (ex-data e))))))))
    (testing "and an ist conjunct of a join is :not-well-formed — a join has no
              per-literal context, which is the antecedent question in another frame"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (v/prove kb [(list 'ist CxA (list shapeP21 '?x))
                                        (list shapeP21 '?y)]
                                    'CxUniverse)))]
        (is (= :not-well-formed (:type (ex-data e))))))
    (testing "while an ordinary vector goal still joins"
      (is (seq (v/prove kb [(list shapeP21 '?x)] CxA))))))
