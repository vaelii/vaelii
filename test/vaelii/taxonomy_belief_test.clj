;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.taxonomy-belief-test
  "The taxonomy caches must agree with the KB about what it entails.

  The cached genl / genlCx closures are derived state — the source of truth is the
  set of *believed* sentexes asserting each edge. Four ways that agreement can
  break, each covered here: defeat leaving a stale edge, a derived edge never
  arriving, `recover` disagreeing with the running KB, and a shared edge dying with
  the first of its several asserting sentexes.

  The four flat caches — `disjoint`, disjoint metatypes + members, the predicate
  properties, and `inverse` — follow belief the same way: `refresh-beliefs`
  reconciles each `:cache-support` entry after every relabel. So a defeated
  `(disjoint A B)` stops constraining, a defeated `(functional P)` stops merging, and a
  defeated `(inverse P Q)` stops answering the swapped goal — each reviving when the
  defeater is retracted. The end-to-end half of that is at the foot of this file."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb a-defeated-genl-leaves-the-closure
  (tu/with-terms [sub_t super_t Ind1 CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (v/assert kb (list sub_t Ind1) CxStory)
    (testing "while believed, the edge entails membership"
      (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))
      (is (v/isa? kb Ind1 super_t)))
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory {:strength :monotonic})
    (testing "once defeated, the edge is gone from the closure"
      (is (empty? (v/sentexes-matching kb (list 'genl sub_t super_t) CxStory)))
      (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))))
    (testing "so isa? cannot answer through it any more"
      (is (not (v/isa? kb Ind1 super_t))))))

(tu/deftest-kb a-revived-genl-comes-back
  (tu/with-terms [sub_t super_t CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (let [neg (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory
                        {:strength :monotonic})]
      (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))
      (testing "retracting the defeater revives the edge, closure included"
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb (list 'genl sub_t super_t) CxStory)))
        (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))))))

(tu/deftest-kb a-defeat-in-one-of-two-supporting-contexts-withdraws-only-its-context
  ;; An edge asserted from two *disconnected* sibling contexts is one edge with two
  ;; supporters.  A negation asserted in one context forms a nogood with the
  ;; supporter there alone — the siblings share no descendant, so the other
  ;; supporter never pairs with it — and the edge must keep its liveness while
  ;; `edge-contexts` loses exactly the defeated side.  This is the end-to-end shape
  ;; of `refresh-relation`'s retarget arm; the raw-taxonomy version is
  ;; `a-context-only-belief-move-retargets-the-edge` in taxonomy_test.
  (tu/with-terms [sub_t super_t CxA CxB]
    (v/assert kb (list 'genl sub_t super_t) CxA)
    (v/assert kb (list 'genl sub_t super_t) CxB)
    (is (= #{CxA CxB}
           (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))
    (let [neg (v/assert kb (list 'not (list 'genl sub_t super_t)) CxB
                        {:strength :monotonic})]
      (testing "the edge survives on A's believed supporter, B's context leaves"
        (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))
        (is (= #{CxA}
               (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t]))))
      (testing "retracting the defeater brings B's context back"
        (v/retract! kb neg)
        (is (= #{CxA CxB}
               (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))))))

(tu/deftest-kb retracting-the-last-believed-supporter-of-a-shared-edge-drops-it
  ;; The retract twin of the test above, and the form a belief-blind writer gets wrong on
  ;; its own.  `del-edge` runs on the retract path with no `believed?` in hand: it sees a
  ;; surviving supporter, keeps the edge, and recomputes its contexts from every
  ;; *recorded* one — so between the write and the settle the edge reads as live, asserted
  ;; from the very context whose supporter is defeated.  Losing the last *believed*
  ;; supporter of a still-supported edge is a deactivation only a `believed?` can make, so
  ;; the reconcile is the whole of what fixes it, and this is the end-to-end claim that it
  ;; does.  (What puts the edge in the reconcile's scope is `refresh-relation`'s `:dirty`;
  ;; it is not what makes *this* test pass, since the retraction's own region turns out to
  ;; name the surviving supporter anyway.  The synthetic driver in `taxonomy_test` is
  ;; where `:dirty` is required, because it passes the honest flip set rather than
  ;; `jtms/touched`'s superset.)
  (tu/with-terms [sub_t super_t Ind1 CxA CxB]
    (v/assert kb (list 'genl sub_t super_t) CxA)
    (v/assert kb (list 'genl sub_t super_t) CxB)
    (v/assert kb (list sub_t Ind1) CxA)
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxB {:strength :monotonic})
    (let [ha (v/handle-of kb (list 'genl sub_t super_t) CxA)]
      (testing "A's supporter is believed, so the edge stands and entails membership"
        (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))
        (is (= #{CxA} (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))
        (is (v/isa? kb Ind1 super_t)))
      (v/retract! kb ha)
      (testing "with it gone, B's supporter is stored but defeated — nothing believes it"
        (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))
        (is (= #{} (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))
        (is (not (v/isa? kb Ind1 super_t))))
      (testing "and retracting the defeater revives it on the supporter that survived"
        (v/retract! kb (v/handle-of kb (list 'not (list 'genl sub_t super_t)) CxB))
        (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))
        (is (= #{CxB} (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))
        (is (v/isa? kb Ind1 super_t))))))

(tu/deftest-kb a-forward-derived-genl-reaches-the-taxonomy
  (tu/with-terms [marker foo_t bar_t Trigger1 CxStory]
    (v/assert-rule kb [(list marker '?x)] (list 'genl foo_t bar_t) CxStory {:direction :forward :chain? false})
    (v/assert kb (list marker Trigger1) CxStory)
    (testing "the rule fired and the sentex is believed"
      (is (seq (v/sentexes-matching kb (list 'genl foo_t bar_t) CxStory))))
    (testing "and the closure knows the edge — a derived genl is still a genl"
      (is (tax/genl?-global (reasoning/taxonomy kb) foo_t bar_t)))))

(tu/deftest-kb recover-agrees-with-the-running-kb
  (tu/with-terms [marker foo_t bar_t Trigger1 CxStory]
    (v/assert-rule kb [(list marker '?x)] (list 'genl foo_t bar_t) CxStory {:direction :forward :chain? false})
    (v/assert kb (list marker Trigger1) CxStory)
    (let [before (tax/genl?-global (reasoning/taxonomy kb) foo_t bar_t)]
      (v/recover kb)
      (testing "a restart does not change what the KB entails"
        (is (= before (tax/genl?-global (reasoning/taxonomy kb) foo_t bar_t)))))))

(tu/deftest-kb recover-does-not-revive-a-defeated-edge
  ;; `rebuild-taxonomy` replays **stored** declarations, so it activates a defeated `genl`
  ;; exactly as it activates a believed one, and two things tell them apart: `recover`'s
  ;; own unconditional reconcile, and the closing `settle`.  A defeated edge is reached by
  ;; either, its opposition being an event the settle reacts to — the *unsupported* edge
  ;; is reached only by the reconcile, which is why that one is unconditional.  The settle
  ;; reconciles the region it relabelled, which makes this a claim about what the rebuild
  ;; relabels: it installs the JTMS from nothing, so every datum is labelled and the
  ;; region is the whole KB.  Nothing narrows the reconcile there, and
  ;; this is the test that says so — the failure if something ever did is silent in the
  ;; worst way, the running KB right and only a restart answering `isa?` through a type
  ;; nothing believes.
  (tu/with-terms [sub_t super_t Ind1 CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (v/assert kb (list sub_t Ind1) CxStory)
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory {:strength :monotonic})
    (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)) "defeated before the restart")
    (v/recover kb)
    (testing "and defeated after it — the rebuild replayed the edge, belief took it back"
      (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))
      (is (not (v/isa? kb Ind1 super_t))))))

(tu/deftest-kb recover-ignores-a-negated-declaration
  ;; `sentexes-with-functor` returns both polarities, and a `(not (genl a b))`
  ;; *opposes* the edge rather than asserting it — the assert path's functor dispatch
  ;; (`not`) never routes one to an integrate arm, so neither may the rebuild.  Read
  ;; positionally it binds its inner sentence as a taxonomy node and nil as the
  ;; other, and one stored `(not (sameAs …))` turns the per-symbol equality filter on
  ;; for every query, permanently.
  (tu/with-terms [d_t e_t pp qq Aa Bb CxSub]
    (v/assert kb (list 'not (list 'genl d_t e_t)) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list 'sameAs Aa Bb)) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list 'genlCx CxSub 'CxUniverse))
              'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list 'transitive pp)) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list 'inverse pp qq)) 'CxUniverse {:strength :monotonic})
    (let [snapshot #(hash-map :types     (set (v/types kb))
                              :contexts  (set (v/contexts kb))
                              :merged?   (some? (tax/merged-term-pred (reasoning/taxonomy kb)))
                              :genl-edge (tax/genl?-global (reasoning/taxonomy kb) d_t e_t))
          before (snapshot)]
      (v/recover kb)
      (testing "recovery integrates exactly what assertion integrated"
        (is (= before (snapshot))))
      (testing "and no cache holds a nil node or a compound non-term"
        (is (every? symbol? (v/types kb)))
        (is (every? symbol? (v/contexts kb)))
        (is (not (:merged? (snapshot))) "no equality class exists, so no filter")))))

(tu/deftest-kb retracting-a-defeated-merge-leaves-the-partition-no-trace-of-it
  ;; `:out` is the partition's record of which supporters are defeated, read against
  ;; `:support`.  A supporter that is *retracted* while defeated leaves `:handles`,
  ;; `:handle-edge` and `:support` — and `:out` with them, or the set grows by one entry
  ;; per such retraction for the KB's life.  A merge rewrites its own negation's terms,
  ;; so the defeated supporter here is a rule-derived equality whose trigger is defeated;
  ;; retracting the trigger sweeps it.
  (tu/with-terms [flag Switch Aa Bb]
    (v/assert kb (list 'implies (list flag '?s) (list 'sameAs Aa Bb)) 'CxUniverse
              {:direction :forward :strength :monotonic})
    (let [h   (v/assert kb (list flag Switch) 'CxUniverse)
          eq  #(:equality @(reasoning/taxonomy kb))
          e   (first (:handles (eq)))]
      (is (some? e) "the rule derives the merge")
      (is (= Aa (tax/representative (reasoning/taxonomy kb) Bb)))
      (v/assert kb (list 'not (list flag Switch)) 'CxUniverse {:strength :monotonic})
      (is (false? (v/in? kb e)) "the derived merge is defeated with its trigger")
      (is (contains? (:out (eq)) e) "and the partition records it OUT")
      (is (= Bb (tax/representative (reasoning/taxonomy kb) Bb)) "merging nothing")
      (v/retract! kb h)
      (is (nil? (v/sentex kb e)) "retracting the trigger sweeps the derived merge")
      (is (not (contains? (:out (eq)) e)) "and it leaves :out")
      (is (not (contains? (:handles (eq)) e)))
      (is (not (contains? (:handle-edge (eq)) e))))))

(tu/deftest-kb recover-drops-an-edge-whose-sentex-is-gone
  (tu/with-terms [sub_t super_t CxStory]
    (let [h (v/assert kb (list 'genl sub_t super_t) CxStory)]
      (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))
      (v/retract! kb h)
      (testing "recover rebuilds from the store rather than merging into the cache"
        (v/recover kb)
        (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))))))

(tu/deftest-kb an-edge-asserted-in-two-contexts-survives-one-retraction
  (tu/with-terms [sub_t super_t CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (let [ha (v/assert kb (list 'genl sub_t super_t) CxA)]
      (v/assert kb (list 'genl sub_t super_t) CxB)
      (testing "two sentexes, one edge"
        (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))
      (v/retract! kb ha)
      (testing "CxB still asserts it, so the edge stands"
        (is (seq (v/sentexes-matching kb (list 'genl sub_t super_t) CxB)))
        (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))))))

(tu/deftest-kb a-defeated-genlCx-stops-making-facts-visible
  (tu/with-terms [parentOf Tom Bob CxSub CxSuper]
    (v/assert kb (list 'genlCx CxSub CxSuper) 'CxUniverse)
    (v/assert kb (list parentOf Tom Bob) CxSuper)
    (testing "the inherited fact is visible from the sub-context"
      (is (seq (v/ask kb (list parentOf Tom '?y) CxSub))))
    (v/assert kb (list 'not (list 'genlCx CxSub CxSuper)) 'CxUniverse
              {:strength :monotonic})
    (testing "defeating the context edge withdraws the inheritance"
      (is (not (tax/sees? (reasoning/taxonomy kb) CxSub CxSuper)))
      (is (empty? (v/ask kb (list parentOf Tom '?y) CxSub))))))

(tu/deftest-kb a-revived-genlCx-arbitrates-the-pair-it-rejoins
  ;; `clear-defeats!` revives a defeated edge at the top of the settle, so the closures
  ;; discovery reads must be refreshed *before* `constraint-nogoods` asks them a
  ;; question: a P/¬P pair made jointly visible by the revival is arbitrated in the
  ;; same settle, never left with both sides believed — a state `recover` over the
  ;; same records would disagree with.  The edge's defeater is *derived*, so lifting
  ;; it removes no record and the revival happens purely in the settle.
  (tu/with-terms [happy qq Tom Trigger CxSub CxSuper]
    (v/assert kb (list 'genlCx CxSub CxSuper) 'CxUniverse)
    (let [hn (v/assert kb (list 'not (list happy Tom)) CxSuper {:strength :monotonic})
          hp (v/assert kb (list happy Tom) CxSub)]
      (testing "with the edge in place, the default fact loses to the monotonic negation"
        (is (v/in? kb hn))
        (is (not (v/in? kb hp))))
      (v/assert-rule kb [(list qq '?x)]
                     (list 'not (list 'genlCx CxSub CxSuper))
                     'CxUniverse {:direction :forward})
      (let [ht (v/assert kb (list qq Trigger) 'CxUniverse {:strength :monotonic})]
        (testing "the derived monotonic negation defeats the edge"
          (is (not (tax/sees? (reasoning/taxonomy kb) CxSub CxSuper)))
          (is (v/in? kb hn)))
        (v/retract! kb ht)
        (testing "the retract's own settle revives the edge and re-arbitrates the pair"
          (is (tax/sees? (reasoning/taxonomy kb) CxSub CxSuper))
          (is (v/in? kb hn))
          (is (not (v/in? kb hp))))))))

(tu/deftest-kb a-quiet-settle-does-not-resurrect-a-defeated-edge
  ;; `refresh-beliefs` runs only when a settle actually moved belief (defeat, revival,
  ;; or an exceptWhen block change).  A later, unrelated assert moves no belief about
  ;; this edge, so the reconcile is skipped — and the skip must not let the earlier
  ;; defeat's effect leak back.  It must also not stop a *new* edge (installed on the
  ;; assert path, not by refresh-beliefs) from taking effect in the same quiet settle.
  (tu/with-terms [sub_t super_t other_t CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory {:strength :monotonic})
    (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))            ; defeated, out of the closure
    (testing "an unrelated assert (a belief-quiet settle) keeps the defeat in place"
      (v/assert kb (list 'genl other_t 'thing) CxStory)
      (is (not (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t))))
    (testing "and the new edge, installed on the assert path, is active regardless"
      (is (tax/genl?-global (reasoning/taxonomy kb) other_t 'thing)))))

(deftest refresh-beliefs-skips-a-relation-no-moved-supporter-touches   ; perf-review #11
  ;; refresh-beliefs takes the set of handles whose belief just moved.  A genl edge
  ;; whose supporter is not among them cannot have changed active-status, so the O(edges)
  ;; scan is skipped — proven here by a `believed?` that says the edge is disbelieved:
  ;; the edge survives while its supporter is out of `moved`, and drops the moment it is
  ;; in.  A pure taxonomy so nothing else is in play.
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1)
    (is (tax/genl?-global t 'dog 'animal))
    (testing "supporter 1 is not in moved → the relation is skipped, edge survives"
      (tax/refresh-beliefs t (constantly false) #{2 3})
      (is (tax/genl?-global t 'dog 'animal)))
    (testing "supporter 1 in moved → reconcile runs, and belief says drop it"
      (tax/refresh-beliefs t (constantly false) #{1})
      (is (not (tax/genl?-global t 'dog 'animal))))
    (testing "moved=nil forces the full unconditional reconcile (recover / supersession)"
      (tax/add-genl t 'dog 'animal 1)
      (is (tax/genl?-global t 'dog 'animal))
      (tax/refresh-beliefs t (constantly false) nil)
      (is (not (tax/genl?-global t 'dog 'animal))))))

;; ---- the four flat caches follow belief end-to-end ----------------------
;; Same shape as the genl tests above, exercised through the KB: assert a default
;; declaration, defeat it with a monotonic `(not …)`, and watch the thing it enabled
;; stop happening — then retract the defeater and watch it come back.

(tu/deftest-kb a-defeated-disjoint-stops-constraining
  (tu/with-terms [dog cat Felix]
    ;; one context: the disjointness check is scoped, and this KB is fresh
    (let [_hd (v/assert kb (list 'disjoint dog cat) 'CxNaturalWorld {:strength :default})]
      (v/assert kb (list cat Felix) 'CxNaturalWorld)
      (testing "believed: the pair is disjoint and the conflicting membership is refused"
        (is (v/disjoint? kb dog cat))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog Felix) 'CxNaturalWorld))))
      (let [hn (v/assert kb (list 'not (list 'disjoint dog cat)) 'CxNaturalWorld
                         {:strength :monotonic})]
        (testing "defeated: no longer disjoint, so the membership is accepted"
          (is (not (v/disjoint? kb dog cat)))
          (is (v/assert kb (list dog Felix) 'CxNaturalWorld)))
        (testing "retracting the defeater restores the constraint"
          ;; drop the now-admitted membership so the revived disjoint has no live clash
          (when-let [hf (v/handle-of kb (list dog Felix) 'CxNaturalWorld)]
            (v/retract! kb hf))
          (v/retract! kb hn)
          (is (v/disjoint? kb dog cat)))))))

(tu/deftest-kb a-defeated-functional-stops-rejecting
  (tu/with-terms [ageOf Bob]
    (let [_hf (v/assert kb (list 'functional ageOf) 'CxUniverse {:strength :default})]
      (v/assert kb (list ageOf Bob 40) 'CxUniverse)
      (testing "believed: a second, unmergeable numeric value is refused"
        (is (v/has-prop? kb :functional ageOf))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list ageOf Bob 41) 'CxUniverse))))
      (let [hn (v/assert kb (list 'not (list 'functional ageOf)) 'CxUniverse
                         {:strength :monotonic})]
        (testing "defeated: the declaration no longer constrains"
          (is (not (v/has-prop? kb :functional ageOf)))
          (is (v/assert kb (list ageOf Bob 41) 'CxUniverse)))
        (testing "retracting the defeater re-arms the constraint"
          (when-let [h41 (v/handle-of kb (list ageOf Bob 41) 'CxUniverse)]
            (v/retract! kb h41))
          (v/retract! kb hn)
          (is (v/has-prop? kb :functional ageOf))
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list ageOf Bob 41) 'CxUniverse))))))))

(tu/deftest-kb a-defeated-inverse-stops-answering-the-swapped-goal
  (tu/with-terms [parentOf childOf Tom Bob]
    (let [_hi (v/assert kb (list 'inverse parentOf childOf) 'CxUniverse {:strength :default})]
      (v/assert kb (list parentOf Tom Bob) 'CxUniverse)
      (testing "believed: the inverse goal is answerable"
        (is (= childOf (v/inverse-of kb parentOf)))
        (is (v/ask? kb (list childOf Bob Tom) 'CxUniverse)))
      (let [hn (v/assert kb (list 'not (list 'inverse parentOf childOf)) 'CxUniverse
                         {:strength :monotonic})]
        (testing "defeated: the inverse map is empty and the swapped goal fails"
          (is (nil? (v/inverse-of kb parentOf)))
          (is (nil? (v/inverse-of kb childOf)))
          (is (not (v/ask? kb (list childOf Bob Tom) 'CxUniverse))))
        (testing "retracting the defeater revives the inverse"
          (v/retract! kb hn)
          (is (= childOf (v/inverse-of kb parentOf)))
          (is (v/ask? kb (list childOf Bob Tom) 'CxUniverse)))))))

(tu/deftest-kb a-defeated-transitive-stops-composing
  (tu/with-terms [before A B C]
    (let [_ht (v/assert kb (list 'transitive before) 'CxUniverse {:strength :default})]
      (v/assert kb (list before A B) 'CxUniverse)
      (v/assert kb (list before B C) 'CxUniverse)
      (testing "believed: the transitive step composes A→B→C into A→C"
        (is (v/has-prop? kb :transitive before))
        (is (v/ask? kb (list before A C) 'CxUniverse)))
      (let [hn (v/assert kb (list 'not (list 'transitive before)) 'CxUniverse
                         {:strength :monotonic})]
        (testing "defeated: no composition, only the stored steps hold"
          (is (not (v/has-prop? kb :transitive before)))
          (is (not (v/ask? kb (list before A C) 'CxUniverse))))
        (testing "retracting the defeater restores composition"
          (v/retract! kb hn)
          (is (v/has-prop? kb :transitive before))
          (is (v/ask? kb (list before A C) 'CxUniverse)))))))
