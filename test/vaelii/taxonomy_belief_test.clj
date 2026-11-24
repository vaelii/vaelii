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
  properties, and `inverse` — follow the network the same way: `refresh-beliefs`
  reconciles each `:cache-support` entry after every relabel, and a scoped read filters
  each supporter through the read walk. So a defeated `(transitive P)` stops composing
  and a defeated `(inverse P Q)` stops answering the swapped goal at the contexts that
  see the defeat — each reviving when the defeater is retracted, and a defeated
  `(disjoint A B)` stops constraining there. A `functional` mark, a `genlCx` edge and an
  equality are on the engine's baseline forced-monotonic set, so no denial defeats one.
  The end-to-end half of that is at the foot of this file."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb a-defeated-genl-leaves-the-closure-its-context-reads
  (tu/with-terms [sub_t super_t Ind1 CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (v/assert kb (list sub_t Ind1) CxStory)
    (testing "while believed, the edge entails membership"
      (is (v/genl? kb sub_t super_t CxStory))
      (is (v/isa? kb Ind1 super_t CxStory)))
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory {:strength :monotonic})
    (testing "once defeated, the edge is gone from the closure its context reads"
      (is (empty? (v/sentexes-matching kb (list 'genl sub_t super_t) CxStory)))
      (is (not (v/genl? kb sub_t super_t CxStory))))
    (testing "so isa? cannot answer through it there"
      (is (not (v/isa? kb Ind1 super_t CxStory))))
    (testing "the closure with no context reads the network, which keeps the edge IN"
      (is (tax/genl?-global (reasoning/taxonomy kb) sub_t super_t)))))

(defn- two-route-firing
  "The firing over dog ⊑ mammal ⊑ animal beside CxA's (genl dog animal), its parts arriving
  in `order` (`:knock` a monotonic denial of `(genl dog mammal)` in CxUniverse), read as
  `{:genl :isa :stored :believed}` at CxUniverse and CxA."
  [kb order]
  (tu/with-terms [dog mammal animal alive_t Fido CxA]
    (let [parts {:long  [[(list 'genl dog mammal) 'CxUniverse] [(list 'genl mammal animal) 'CxUniverse]]
                 :short [[(list 'genl dog animal) CxA]]
                 :claim [[(list dog Fido) 'CxUniverse]]}
          at    ['CxUniverse CxA]]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (doseq [t [dog mammal animal]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
      (v/assert kb (list 'set/forwardRule (list 'implies (list animal '?x) (list alive_t '?x)))
                'CxUniverse)
      (doseq [part order]
        (if (= :knock part)
          (v/assert kb (list 'not (list 'genl dog mammal)) 'CxUniverse {:strength :monotonic})
          (doseq [[s c] (get parts part)] (v/assert kb s c))))
      {:genl     (mapv #(v/genl? kb dog mammal %) at)
       :isa      (mapv #(v/isa? kb Fido mammal %) at)
       :stored   (mapv #(some? (v/handle-of kb (list alive_t Fido) %)) at)
       :believed (mapv #(v/ask? kb (list alive_t Fido) %) at)})))

(tu/deftest-kb a-defeated-genl-edge-is-hidden-at-its-placement-and-moves-no-firing
  ;; A monotonic denial of `(genl dog mammal)` in CxUniverse places a defeat of the edge
  ;; there.  The scoped reads at and below CxUniverse read the defeat, so neither
  ;; CxUniverse nor CxA reaches mammal from dog.  The witness search reads the network
  ;; and no defeat, so the firing over the long route is stored in CxUniverse in every
  ;; order, and the store is what the same order holds with no denial; CxA reads the
  ;; firing over its own (genl dog animal).
  (doseq [order [[:knock :long :short :claim] [:long :short :claim :knock]
                 [:short :claim :knock :long] [:claim :knock :long :short]
                 [:long :knock :claim :short] [:short :long :knock :claim]]]
    (testing (str order)
      (let [r (two-route-firing kb order)]
        (is (= [false false] (:genl r)))
        (is (= [false false] (:isa r)))
        (is (= [false true] (:believed r)))
        (is (true? (first (:stored r))))
        (is (= (:stored (two-route-firing kb (filterv #(not= :knock %) order))) (:stored r)))))))

(tu/deftest-kb a-revived-genl-comes-back
  (tu/with-terms [sub_t super_t CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (let [neg (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory
                        {:strength :monotonic})]
      (is (not (v/genl? kb sub_t super_t CxStory)))
      (testing "retracting the defeater revives the edge, closure included"
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb (list 'genl sub_t super_t) CxStory)))
        (is (v/genl? kb sub_t super_t CxStory))))))

(tu/deftest-kb a-defeat-in-one-of-two-supporting-contexts-withdraws-only-its-context
  ;; An edge asserted from two *disconnected* sibling contexts is one edge with two
  ;; supporters.  A negation asserted in one context forms a nogood with the
  ;; supporter there alone — the siblings share no descendant, so the other
  ;; supporter never pairs with it — and places a defeat of that supporter there.  The
  ;; defeat moves no label, so `edge-contexts` keeps both sides, and the context
  ;; holding the defeat stops reading the edge while the other keeps it.
  (tu/with-terms [sub_t super_t CxA CxB]
    (v/assert kb (list 'genl sub_t super_t) CxA)
    (v/assert kb (list 'genl sub_t super_t) CxB)
    (is (= #{CxA CxB}
           (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))
    (let [neg (v/assert kb (list 'not (list 'genl sub_t super_t)) CxB
                        {:strength :monotonic})]
      (testing "the edge survives at A, and B stops reading it"
        (is (v/genl? kb sub_t super_t CxA))
        (is (not (v/genl? kb sub_t super_t CxB)))
        (is (= #{CxA CxB}
               (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t]))))
      (testing "retracting the defeater gives B the edge back"
        (v/retract! kb neg)
        (is (v/genl? kb sub_t super_t CxB))))))

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
  ;; where `:dirty` is required, because it passes the exact flip set rather than
  ;; `jtms/touched`'s superset.)
  (tu/with-terms [sub_t super_t Ind1 CxA CxB]
    (v/assert kb (list 'genl sub_t super_t) CxA)
    (v/assert kb (list 'genl sub_t super_t) CxB)
    (v/assert kb (list sub_t Ind1) CxA)
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxB {:strength :monotonic})
    (let [ha (v/handle-of kb (list 'genl sub_t super_t) CxA)]
      (testing "A's supporter is believed, so the edge stands and entails membership"
        (is (v/genl? kb sub_t super_t CxA))
        (is (not (v/genl? kb sub_t super_t CxB)))
        (is (v/isa? kb Ind1 super_t CxA)))
      (v/retract! kb ha)
      (testing "with it gone, B's supporter is stored but defeated — no context reads it"
        (is (not (v/genl? kb sub_t super_t CxA)))
        (is (not (v/genl? kb sub_t super_t CxB)))
        (is (= #{CxB} (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))
        (is (not (v/isa? kb Ind1 super_t CxA))))
      (testing "and retracting the defeater gives B the supporter that survived"
        (v/retract! kb (v/handle-of kb (list 'not (list 'genl sub_t super_t)) CxB))
        (is (v/genl? kb sub_t super_t CxB))
        (is (= #{CxB} (tax/edge-contexts (reasoning/taxonomy kb) :genl [sub_t super_t])))))))

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
    (is (not (v/genl? kb sub_t super_t CxStory)) "defeated before the restart")
    (v/recover kb)
    (testing "and defeated after it — the rebuild replayed the edge, belief took it back"
      (is (not (v/genl? kb sub_t super_t CxStory)))
      (is (not (v/isa? kb Ind1 super_t CxStory))))))

(tu/deftest-kb the-census-a-scoped-read-intersects-is-read-from-the-predicate-extents
  ;; A context stating only a `partition` supports `genl` edges, and one stating only a
  ;; denied `genl` states a fact of the functor: the predicate extents list both, and a
  ;; KB's taxonomy reads its census there on each call.
  (tu/with-terms [whole_t p_t q_t d_t e_t CxA CxB]
    (let [tax (reasoning/taxonomy kb)]
      (is (= #{} (tax/asserting-contexts-among tax [CxA CxB])))
      (v/assert kb (list 'partition whole_t p_t q_t) CxA)
      (v/assert kb (list 'not (list 'genl d_t e_t)) CxB {:strength :monotonic})
      (is (= #{CxA CxB} (tax/asserting-contexts-among tax [CxA CxB])))
      (is (= #{CxA} (tax/asserting-contexts-in tax :genl #{CxA})))
      (is (pos? (tax/supporter-count-in tax :genl #{CxA}))))))

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

(tu/deftest-kb retracting-a-merge-held-out-leaves-the-partition-no-trace-of-it
  ;; `:out` is the partition's record of which supporters are not believed, read against
  ;; `:support`.  A supporter retracted while OUT leaves `:handles`, `:handle-edge` and
  ;; `:support`, and `:out` with them, or the set grows by one entry per such retraction
  ;; for the KB's life.  The OUT supporter here is a merge a void firing concludes (its
  ;; antecedent is not forced-monotonic); retracting the trigger sweeps it.
  (tu/with-terms [aliasOf Aa Bb]
    (v/assert-rule kb [(list aliasOf '?x '?y)] '(sameAs ?x ?y) 'CxUniverse {:direction :forward})
    (let [h  (v/assert kb (list aliasOf Aa Bb) 'CxUniverse)
          eq #(:equality @(reasoning/taxonomy kb))
          e  (first (:handles (eq)))]
      (is (some? e) "the firing stores the merge")
      (is (false? (v/believed? kb e)) "held void")
      (is (contains? (:out (eq)) e) "and the partition records it OUT")
      (is (= #{Bb} (set (v/equiv-class kb Bb))) "merging nothing")
      (v/retract! kb h)
      (is (nil? (v/sentex kb e)) "retracting the trigger sweeps the merge")
      (is (not (contains? (:out (eq)) e)) "and it leaves :out")
      (is (not (contains? (:handles (eq)) e)))
      (is (not (contains? (:handle-edge (eq)) e))))))

(tu/deftest-kb a-cover-is-a-stored-supporter-of-each-edge-it-installs
  ;; `(covering W P Q)` installs `(genl P W)` and `(genl Q W)` under its own handle, so the
  ;; supporter family lists that handle under each edge beside the `genl` fact stating one
  (tu/with-terms [whole_t p_t q_t CxA]
    (let [hg (v/assert kb (list 'genl p_t whole_t) CxA)
          hc (v/assert kb (list 'covering whole_t p_t q_t) CxA)
          sup #(reads/as-stored-supporters-global (:index kb) [:genl % whole_t])]
      (is (= {hg CxA hc CxA} (sup p_t)))
      (is (= {hc CxA} (sup q_t)))
      (is (contains? (reads/as-stored-installed-keys (:index kb) hc) [:genl q_t whole_t]))
      (v/retract! kb hc)
      (is (= {hg CxA} (sup p_t)))
      (is (= {} (sup q_t)))
      (is (= #{} (reads/as-stored-installed-keys (:index kb) hc))))))

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

(tu/deftest-kb a-quiet-settle-does-not-resurrect-a-defeated-edge
  ;; `refresh-beliefs` runs only when a settle actually moved belief (defeat, revival,
  ;; or an exceptWhen block change).  A later, unrelated assert moves no belief about
  ;; this edge, so the reconcile is skipped — and the skip must not let the earlier
  ;; defeat's effect leak back.  It must also not stop a *new* edge (installed on the
  ;; assert path, not by refresh-beliefs) from taking effect in the same quiet settle.
  (tu/with-terms [sub_t super_t other_t CxStory]
    (v/assert kb (list 'genl sub_t super_t) CxStory)
    (v/assert kb (list 'not (list 'genl sub_t super_t)) CxStory {:strength :monotonic})
    (is (not (v/genl? kb sub_t super_t CxStory)))            ; defeated, out of the closure
    (testing "an unrelated assert (a belief-quiet settle) keeps the defeat in place"
      (v/assert kb (list 'genl other_t 'thing) CxStory)
      (is (not (v/genl? kb sub_t super_t CxStory))))
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

;; ---- the flat caches follow belief end-to-end ---------------------------
;; Same shape as the genl tests above, exercised through the KB: assert a default
;; declaration, defeat it with a monotonic `(not …)`, and watch the thing it enabled
;; stop happening — then retract the defeater and watch it come back.

(tu/deftest-kb a-defeated-disjoint-stops-constraining
  (tu/with-terms [dog cat Felix CxNature]
    (v/assert kb (list 'disjoint dog cat) CxNature {:strength :default})
    (v/assert kb (list cat Felix) CxNature)
    (testing "believed: the pair is disjoint and the conflicting membership is a clash"
      (is (v/disjoint? kb dog cat CxNature))
      (is (tu/stored-in-clash? kb (list dog Felix) CxNature)))
    (let [hn (v/assert kb (list 'not (list 'disjoint dog cat)) CxNature
                       {:strength :monotonic})]
      (testing "defeated: no longer disjoint there, so the membership clashes with nothing"
        (is (not (v/disjoint? kb dog cat CxNature)))
        (is (v/ask? kb (list dog Felix) CxNature))
        (is (v/ask? kb (list cat Felix) CxNature))
        (is (empty? (v/contradictions kb))))
      (testing "the network keeps it IN, and a read naming no context reads it at CxNature"
        (is (tax/disjoint? (reasoning/taxonomy kb) dog cat))
        (is (not (v/disjoint? kb dog cat))))
      (testing "retracting the defeater restores the constraint"
        (when-let [hf (v/handle-of kb (list dog Felix) CxNature)]
          (v/retract! kb hf))
        (v/retract! kb hn)
        (is (v/disjoint? kb dog cat CxNature))))))

(tu/deftest-kb a-defeated-inverse-stops-answering-the-swapped-goal
  (tu/with-terms [parentOf childOf Tom Bob]
    (let [_hi (v/assert kb (list 'inverse parentOf childOf) 'CxUniverse {:strength :default})]
      (v/assert kb (list parentOf Tom Bob) 'CxUniverse)
      (testing "believed: the inverse goal is answerable"
        (is (= childOf (v/inverse-of kb parentOf)))
        (is (v/ask? kb (list childOf Bob Tom) 'CxUniverse)))
      (let [hn (v/assert kb (list 'not (list 'inverse parentOf childOf)) 'CxUniverse
                         {:strength :monotonic})]
        (testing "defeated: the context reads no inverse and the swapped goal fails there"
          (is (nil? (v/inverse-of kb parentOf 'CxUniverse)))
          (is (nil? (v/inverse-of kb childOf 'CxUniverse)))
          (is (not (v/ask? kb (list childOf Bob Tom) 'CxUniverse))))
        (testing "the network keeps it IN, and a read naming no context reads it at CxUniverse"
          (is (= childOf (tax/inverse-of (reasoning/taxonomy kb) parentOf)))
          (is (nil? (v/inverse-of kb parentOf))))
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
        (testing "defeated: no composition at the context, only the stored steps hold"
          (is (not (v/has-prop? kb :transitive before 'CxUniverse)))
          (is (not (v/ask? kb (list before A C) 'CxUniverse))))
        (testing "the network keeps it IN, and a read naming no context reads it at CxUniverse"
          (is (tax/has-prop? (reasoning/taxonomy kb) :transitive before))
          (is (not (v/has-prop? kb :transitive before))))
        (testing "retracting the defeater restores composition"
          (v/retract! kb hn)
          (is (v/has-prop? kb :transitive before))
          (is (v/ask? kb (list before A C) 'CxUniverse)))))))

;; ---- an edge or entry resting on a defeated handle ------------------------

(defn- derived-edge-reading
  "E = `(genl poodle cat)`, derived in CxA by `(breedOf ?b ?s) ⇒ (genl ?b ?s)` from
  L = `(breedOf poodle cat)` :default in CxA, beside `(poodle Fifi)` in CxA.  A monotonic
  denial of L in `deny-in` (CxB or CxA) places a defeat of L at CxD (below CxA and CxB) or
  at CxA.  The parts arrive in `order`, and with `recover?` the KB is recovered after.
  Answers `{:genl :isa :believed}`, each over CxA, CxD and CxE (below CxD)."
  [kb order deny-in recover?]
  (tu/with-terms [poodle cat breedOf Fifi CxA CxB CxD CxE]
    (let [M     {:strength :monotonic}
          deny  (if (= :a deny-in) CxA CxB)
          L     (list breedOf poodle cat)
          E     (list 'genl poodle cat)
          parts {:rule   #(v/assert-rule kb [(list breedOf '?b '?s)] (list 'genl '?b '?s) CxA
                                         {:direction :forward})
                 :fact   #(v/assert kb L CxA)
                 :member #(v/assert kb (list poodle Fifi) CxA)
                 :deny   #(v/assert kb (list 'not L) deny M)}
          at    [CxA CxD CxE]]
      (doseq [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxD CxA] [CxD CxB] [CxE CxD]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse M))
      (doseq [p order] ((get parts p)))
      (when recover? (v/recover kb))
      (let [eh (v/handle-of kb E CxA)]
        {:genl     (mapv #(v/genl? kb poodle cat %) at)
         :isa      (mapv #(v/isa? kb Fifi cat %) at)
         :believed (mapv #(boolean (and eh (v/believed? kb eh %))) at)}))))

(tu/deftest-kb a-derived-genl-edge-over-a-defeated-fact-is-hidden-where-the-fact-is
  ;; L is no supporter of E, so the defeat reaches E through E's justification alone.
  ;; Every scoped read at and below the defeat's placement agrees with `believed?` of E.
  (doseq [[deny-in want] [[:b [true false false]] [:a [false false false]]]
          order (take-nth 5 (tu/orders [:rule :fact :member :deny]))
          recover? [false true]]
    (testing (str deny-in " " (vec order) (when recover? " recovered"))
      (let [r (derived-edge-reading kb order deny-in recover?)]
        (is (= want (:believed r)))
        (is (= want (:genl r)))
        (is (= want (:isa r)))))))

(defn- derived-mark-reading
  "`(transitive before)`, derived in CxA by `(relKind ?p ?k) ⇒ (transitive ?p)` from
  L = `(relKind before Kind)` :default in CxA, beside `(before A B)` and `(before B C)` in
  CxA.  A monotonic denial of L in `deny-in` places a defeat of L at CxD (below CxA and
  CxB) or at CxA.  The parts arrive in `order`, and with `recover?` the KB is recovered
  after.  Answers `{:prop :own :composes}`: the mark's cache entry, the mark read with no
  context, and `(before A C)` asked at CxA and CxD."
  [kb order deny-in recover?]
  (tu/with-terms [before relKind Kind A B C CxA CxB CxD]
    (let [M     {:strength :monotonic}
          L     (list relKind before Kind)
          parts {:rule  #(v/assert-rule kb [(list relKind '?p '?k)] (list 'transitive '?p) CxA
                                        {:direction :forward})
                 :fact  #(v/assert kb L CxA)
                 :steps #(do (v/assert kb (list before A B) CxA) (v/assert kb (list before B C) CxA))
                 :deny  #(v/assert kb (list 'not L) (if (= :a deny-in) CxA CxB) M)}]
      (doseq [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxD CxA] [CxD CxB]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse M))
      (doseq [p order] ((get parts p)))
      (when recover? (v/recover kb))
      {:prop     (tax/has-prop? (reasoning/taxonomy kb) :transitive before)
       :own      (v/has-prop? kb :transitive before)
       :composes (mapv #(v/ask? kb (list before A C) %) [CxA CxD])})))

(tu/deftest-kb a-derived-mark-over-a-defeated-fact-is-in-the-cache-and-hidden-where-the-fact-is
  ;; The mark's cache entry reads the network and is the same in every order and through
  ;; `recover`. A read with no context filters the supporter at CxA, where it is stated.
  (doseq [[deny-in own composes] [[:b true [true false]] [:a false [false false]]]
          order (take-nth 5 (tu/orders [:rule :fact :steps :deny]))
          recover? [false true]]
    (testing (str deny-in " " (vec order) (when recover? " recovered"))
      (let [r (derived-mark-reading kb order deny-in recover?)]
        (is (true? (:prop r)))
        (is (= own (:own r)))
        (is (= composes (:composes r)))))))

(tu/deftest-kb a-guard-defeat-of-a-derived-edge-released-by-a-defeat-of-its-blocker-shows-the-edge
  ;; F = (genl poodle cat) is fired in CxA by a rule guarded by `(unknown (blk ?b))`.  The
  ;; blocker B = (blk poodle) in CxB places a guard defeat of F at CxD.  A monotonic denial
  ;; of B in CxE places a defeat of B there, which takes the guard defeat out of force at
  ;; CxE.  B is no supporter; the scoped closure CxE read before the denial is retired.
  (tu/with-terms [poodle cat breedOf blk CxA CxB CxD CxE]
    (let [rule (list 'set/forwardRule
                     (list 'implies (list 'and (list breedOf '?b '?s) (list 'unknown (list blk '?b)))
                           (list 'genl '?b '?s)))]
      (doseq [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxD CxA] [CxD CxB] [CxE CxD]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse {:strength :monotonic}))
      (v/assert kb rule CxA)
      (v/assert kb (list breedOf poodle cat) CxA)
      (v/assert kb (list blk poodle) CxB)
      (let [fh   (v/handle-of kb (list 'genl poodle cat) CxA)
            read (fn [] (mapv (fn [c] [(contains? (set (v/genls kb poodle c)) cat)
                                       (v/genl? kb poodle cat c)
                                       (v/believed? kb fh c)])
                              [CxA CxD CxE]))]
        (is (= [[true true true] [false false false] [false false false]] (read)))
        (v/assert kb (list 'not (list blk poodle)) CxE {:strength :monotonic})
        (is (= [[true true true] [false false false] [true true true]] (read)))))))

(defn- memo-against-fresh
  "Each step `[tag memo fresh]` at which `(read tx)` over the live taxonomy differs from
  the same read over a detached copy, whose memo is empty, under either reading."
  [kb steps read]
  (into []
        (comp (mapcat (fn [[tag]] (for [net? [false true]] [tag net?])))
              (keep (fn [[tag net?]]
                      (let [[m f] (binding [tax/*network-belief* net?]
                                    (let [tx (reasoning/taxonomy kb)]
                                      [(read tx) (read (tax/detached-copy tx))]))]
                        (when (not= m f) [tag net? m f])))))
        steps))

(defn- joined-edge-steps
  "E = (genl ka_t ke_t) is fired in CxP by (kc_t ?x) ⇒ E, over (kc_t B) and then (kc_t A),
  the parts arriving in `order`; retracting (kc_t A) drops the second firing.  `:defeat`
  hides the firing over (kc_t B) at CxP by the defeat (kb_t B) and (disjoint kb_t kc_t)
  place; `:except` hides it at CxR below CxP by an except of (kc_t B) there.  E is network
  IN throughout.  Answers, after each step, its tag, the memo-against-fresh differences of
  the closures at the reader, and whether the reader's closures cross E."
  [kb order hide]
  (tu/with-terms [ka_t ke_t kb_t kc_t A B CxP CxR]
    (let [M      {:strength :monotonic}
          reader (if (= :except hide) CxR CxP)
          parts  {:rule #(v/assert kb (list 'set/forwardRule
                                            (list 'implies (list kc_t '?x) (list 'genl ka_t ke_t)))
                                   CxP M)
                  :kc-b #(v/assert kb (list kc_t B) CxP)
                  :hide #(if (= :except hide)
                           (v/assert kb (list 'except (list 'sentexHandle (v/handle-of kb (list kc_t B) CxP)))
                                     CxR M)
                           (v/assert kb (list kb_t B) CxP M))
                  :kc-a #(v/assert kb (list kc_t A) CxP)
                  :drop #(v/retract! kb (v/handle-of kb (list kc_t A) CxP))}
          read   (fn [tx] [(tax/genls tx ka_t reader) (tax/specs tx ke_t reader)])]
      (doseq [[c up] [[CxP 'CxUniverse] [CxR CxP]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse M))
      (doseq [t [ka_t ke_t kb_t kc_t]] (v/assert kb (list 'genl t 'thing) 'CxUniverse M))
      (v/assert kb (list 'disjoint kb_t kc_t) 'CxUniverse M)
      (mapv (fn [p]
              ((get parts p))
              (let [[genls specs] (read (reasoning/taxonomy kb))]
                [p (memo-against-fresh kb [[p]] read) [(contains? genls ke_t) (contains? specs ka_t)]]))
            (concat order [:drop])))))

(tu/deftest-kb a-justification-joining-a-hidden-edge-moves-the-scoped-closures-that-cross-it
  ;; A second justification over no hidden handle shows E at the reader with no relabel,
  ;; and dropping it hides E again.  After every step the memoized scoped closures, under
  ;; the belief reading and the network reading, read what a fresh memo reads.  The
  ;; network reading reads no defeat, so it sees E throughout in the `:defeat` shape.
  (doseq [hide [:defeat :except]
          order (tu/orders [:rule :kc-b :hide :kc-a])
          :when (or (= :defeat hide) (< (.indexOf ^java.util.List order :kc-b)
                                        (.indexOf ^java.util.List order :hide)))]
    (testing (str hide " " (vec order))
      (let [steps (joined-edge-steps kb order hide)]
        (is (= [] (into [] (mapcat second) steps)))
        (is (= [[true true] [false false]] (mapv #(nth % 2) (take-last 2 steps))))))))

(tu/deftest-kb a-justification-joining-a-hidden-genlCx-edge-moves-the-scoped-ancestor-sets
  ;; (genlCx CxS CxB) is fired in CxUniverse from (irreflexive relI), which an except at
  ;; CxS hides there, and then from (functional relF), which shows the edge at CxS with no
  ;; relabel; retracting (functional relF) hides it again.  A `genlCx` firing rests only on
  ;; forced-monotonic literals, and each antecedent here is one.
  (doseq [order (tu/orders [:rule-i :rule-a :fact-a])]
    (tu/with-terms [relI relF CxS CxB]
      (let [M     {:strength :monotonic}
            edge  (list 'genlCx CxS CxB)
            parts {:rule-i #(v/assert kb (list 'set/forwardRule (list 'implies (list 'irreflexive relI) edge))
                                      'CxUniverse M)
                   :rule-a #(v/assert kb (list 'set/forwardRule (list 'implies (list 'functional relF) edge))
                                      'CxUniverse M)
                   :fact-a #(v/assert kb (list 'functional relF) 'CxUniverse M)
                   :drop   #(v/retract! kb (v/handle-of kb (list 'functional relF) 'CxUniverse))}
            read  (fn [tx] (tax/context-up tx CxS))]
        (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse M)
        (doseq [r [relI relF]] (v/assert kb (list 'arity r 2) 'CxUniverse M))
        (v/assert kb (list 'irreflexive relI) 'CxUniverse M)
        (v/assert kb (list 'except (list 'sentexHandle (v/handle-of kb (list 'irreflexive relI) 'CxUniverse)))
                  CxS M)
        (let [steps (mapv (fn [p] ((get parts p))
                            [p (memo-against-fresh kb [[p]] read)
                             (contains? (read (reasoning/taxonomy kb)) CxB)])
                          (concat order [:drop]))]
          (testing (vec order)
            (is (= [] (into [] (mapcat second) steps)))
            (is (= [true false] (mapv #(nth % 2) (take-last 2 steps))))))))))

(tu/deftest-kb a-member-s-denial-leaves-a-default-type-edge-believed
  ;; A stated type `genl` edge loses only in a nogood it is a member of (docs/nmtms.md),
  ;; and a denial of one member's supertype membership is not one: the edge and the other
  ;; members' supertype memberships stay.  A per-member default is a rule (below).
  (tu/with-terms [organism mortal Bob Jelly]
    (v/assert kb (list 'genl organism mortal) 'CxUniverse)
    (doseq [x [Bob Jelly]] (v/assert kb (list organism x) 'CxUniverse))
    (v/assert kb (list 'not (list mortal Jelly)) 'CxUniverse {:strength :monotonic})
    (is (v/genl? kb organism mortal 'CxUniverse))
    (is (v/isa? kb Bob mortal 'CxUniverse))))

(defn- default-back-rule
  "`(organism ?x) ⇒ (mortal ?x)` as a forward default rule."
  [organism mortal]
  (list 'set/defaultRule
        (list 'set/forwardRule (list 'implies (list 'and (list organism '?x)) (list mortal '?x)))))

(tu/deftest-kb a-default-rule-back-along-a-genl-edge-holds-for-each-member-but-the-denied-one
  ;; `(genl mortal organism)` and a default rule back from organism to mortal state two
  ;; types that coincide by default.  Each firing is defeasible on its own, so a denial of
  ;; one member's conclusion defeats that firing alone and the member keeps its type.
  (doseq [order (take-nth 4 (tu/orders [:edge :rule :members :deny]))]
    (tu/with-terms [organism mortal Bob Jelly]
      (let [parts {:edge    #(v/assert kb (list 'genl mortal organism) 'CxUniverse
                                       {:strength :monotonic})
                   :rule    #(v/assert kb (default-back-rule organism mortal) 'CxUniverse)
                   :members #(doseq [x [Bob Jelly]] (v/assert kb (list organism x) 'CxUniverse))
                   :deny    #(v/assert kb (list 'not (list mortal Jelly)) 'CxUniverse
                                       {:strength :monotonic})}]
        (doseq [p order] ((get parts p)))
        (testing (vec order)
          (is (= [true false true]
                 (mapv #(v/ask? kb % 'CxUniverse)
                       [(list mortal Bob) (list mortal Jelly) (list organism Jelly)])))
          (is (empty? (v/conflicts kb)))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb a-context-excepting-the-default-rule-reads-the-two-types-apart
  ;; Two types coextensive by default in one context and not in another: the rule holds
  ;; where its context is seen, and an `except` of it in a context below hides the firing
  ;; there.  A context that does not see the rule's context never reads the firing.
  (tu/with-terms [organism mortal Bob CxBiology CxTotoro CxOther]
    (doseq [[sub super] [[CxBiology 'CxUniverse] [CxTotoro CxBiology] [CxOther 'CxUniverse]]]
      (v/assert kb (list 'genlCx sub super) 'CxUniverse))
    (v/assert kb (list 'genl mortal organism) 'CxUniverse {:strength :monotonic})
    (let [rh (v/assert kb (default-back-rule organism mortal) CxBiology)]
      (v/assert kb (list 'except (list 'sentexHandle rh)) CxTotoro)
      (v/assert kb (list organism Bob) 'CxUniverse)
      (is (= [true false false]
             (mapv #(v/ask? kb (list mortal Bob) %) [CxBiology CxTotoro CxOther]))))))

(tu/deftest-kb a-read-naming-no-context-reads-each-edge-and-declaration-at-its-own-context
  (tu/with-terms [dog mammal reptile Rex insideOf parentOf childOf CxA CxB]
    (let [M     {:strength :monotonic}
          _     (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse M)
          _     (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse M)
          _     (v/assert kb (list dog Rex) CxA M)
          hs    {:genl       (v/assert kb (list 'genl dog mammal) CxA)
                 :disjoint   (v/assert kb (list 'disjoint mammal reptile) CxA)
                 :transitive (v/assert kb (list 'transitive insideOf) CxA)
                 :inverse    (v/assert kb (list 'inverse parentOf childOf) CxA)}
          reads (fn []
                  {:genl       [(v/genl? kb dog mammal)
                                (contains? (v/genls kb dog) mammal)
                                (contains? (v/specs kb mammal) dog)
                                (contains? (v/direct-genls kb dog) mammal)
                                (contains? (v/direct-specs kb mammal) dog)
                                (contains? (v/min-genls kb dog) mammal)
                                (contains? (v/max-specs kb mammal) dog)
                                (contains? (v/common-genls kb [dog]) mammal)
                                (v/isa? kb Rex mammal)]
                   :disjoint   [(v/disjoint? kb mammal reptile)]
                   :transitive [(v/has-prop? kb :transitive insideOf)]
                   :inverse    [(= childOf (v/inverse-of kb parentOf))]})
          all   (fn [b] (into {} (map (fn [[k v]] [k (mapv (constantly b) v)])) (reads)))
          hider {:except-own   (fn [h] (v/assert kb (list 'except (list 'sentexHandle h)) CxA M))
                 :denial-own   (fn [h] (v/assert kb (list 'not (v/sentence-of (v/sentex kb h))) CxA M))
                 :except-below (fn [h] (v/assert kb (list 'except (list 'sentexHandle h)) CxB M))}
          seen  (vec (for [[hk hide!] hider
                           [k h] hs]
                       (let [x       (hide! h)
                             hidden  (reads)
                             _       (v/retract! kb x)
                             back    (reads)]
                         [hk k hidden back])))]
      (is (= (all true) (reads)) "every read holds the stated edges and declarations")
      (doseq [[hk k hidden back] seen]
        (is (= (cond-> (all true) (not= hk :except-below) (update k #(mapv (constantly false) %)))
               hidden)
            (str hk " of " k))
        (is (= (all true) back) (str "retracting the " hk " of " k " restores it"))))))
