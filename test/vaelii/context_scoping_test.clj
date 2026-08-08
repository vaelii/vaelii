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
  outright.  The lattice throughout is two siblings under UniverseContext, neither
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
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- siblings!
  "Wire `a` and `b` as incomparable contexts under UniverseContext: each sees the
  whole shipped ontology, neither sees the other, and no context sees both."
  [kb a b]
  (v/assert kb (list 'genlContext a 'UniverseContext) 'UniverseContext)
  (v/assert kb (list 'genlContext b 'UniverseContext) 'UniverseContext))

;; ---- the genl closure, walked on someone's behalf -----------------------
;;
;; A walk scoped to context C reads the edges of every context C inherits, and none of
;; the edges of a context it does not.

(tu/deftest-kb a-genl-walk-reads-the-contexts-it-inherits-and-no-others
  (tu/with-terms [sub_t mid_t sup_t AContext ChildContext OtherContext]
    (siblings! kb AContext OtherContext)
    (v/assert kb (list 'genlContext ChildContext AContext) 'UniverseContext)
    (v/assert kb (list 'genl sub_t mid_t) AContext)
    (v/assert kb (list 'genl mid_t sup_t) AContext)
    (testing "the asserting context sees its own chain"
      (is (contains? (v/genls kb sub_t AContext) sup_t))
      (is (v/genl? kb sub_t sup_t AContext)))
    (testing "a context that inherits it sees it too"
      (is (contains? (v/genls kb sub_t ChildContext) sup_t))
      (is (v/genl? kb sub_t sup_t ChildContext)))
    (testing "a context that does not inherit it sees none of it"
      (is (not (contains? (v/genls kb sub_t OtherContext) sup_t)))
      (is (not (v/genl? kb sub_t sup_t OtherContext))))
    (testing "and the downward walk agrees, node for node"
      (is (contains? (v/specs kb sup_t ChildContext) sub_t))
      (is (not (contains? (v/specs kb sup_t OtherContext) sub_t))))))

(tu/deftest-kb type-membership-follows-the-visible-edges
  (tu/with-terms [pug_t dog_t Rex AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'genl pug_t dog_t) AContext)
    (v/assert kb (list pug_t Rex) BContext)
    (testing "B holds the membership but not the edge, so it does not hold the supertype"
      (is (seq (v/sentexes-matching kb (list pug_t Rex) BContext)))
      (is (= #{pug_t} (set (v/types-of kb Rex BContext))) "the asserted type, and only it")
      (is (not (v/isa? kb Rex dog_t BContext)))
      (is (not (v/isa? kb Rex dog_t AContext))
          "nor from A, which has the edge and not the membership — each half alone
           proves nothing, which is the point"))
    (testing "every retrieval level agrees — none answers what B cannot see"
      (is (every? #(empty? (v/lookup kb % (list dog_t Rex) BContext)) [2 3 4 5 6 7])))))

;; ---- forward chaining: the edge a subsumption match rests on ------------

(tu/deftest-kb a-firing-is-placed-only-where-its-subsumption-is-visible
  (tu/with-terms [fatherOf2 parentOf2 ancestorOf2 Tom Bob AContext BContext]
    (siblings! kb AContext BContext)
    ;; the predicate hierarchy is A's; the rule and the fact are B's
    (v/assert kb (list 'genl fatherOf2 parentOf2) AContext)
    (v/assert kb (list 'implies (list parentOf2 '?x '?y) (list ancestorOf2 '?x '?y)) BContext)
    (v/assert kb (list fatherOf2 Tom Bob) BContext)
    (testing "B does not conclude on the strength of an edge it cannot see"
      (is (empty? (v/sentexes-matching kb (list ancestorOf2 Tom Bob) BContext)))
      (is (empty? (v/sentexes-matching kb (list ancestorOf2 Tom Bob)))))
    (testing "and the drop is reported, naming the subsumption rather than the facts"
      (let [vs (filter #(= :no-placement (:violation %)) (v/violations kb))]
        (is (seq vs))
        (is (= [fatherOf2] (get-in (first vs) [:detail :subsumed])))))))

(tu/deftest-kb a-firing-whose-subsumption-is-visible-is-placed
  (tu/with-terms [fatherOf3 parentOf3 ancestorOf3 Tom Bob AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'genl fatherOf3 parentOf3) 'UniverseContext)
    (v/assert kb (list 'implies (list parentOf3 '?x '?y) (list ancestorOf3 '?x '?y)) BContext)
    (v/assert kb (list fatherOf3 Tom Bob) BContext)
    (is (= [BContext] (mapv :context (v/sentexes-matching kb (list ancestorOf3 Tom Bob) BContext))))))

(tu/deftest-kb a-late-genl-edge-fires-what-it-newly-connects
  ;; the order-independence half: the edge arriving last must reach the facts already
  ;; stored, or the same three sentences mean different things in different orders
  (tu/with-terms [dog4_t animal4_t breathes4 Muffet]
    (v/assert kb (list 'genl animal4_t 'thing) 'UniverseContext)
    (v/assert kb (list 'implies (list animal4_t '?x) (list breathes4 '?x)) 'UniverseContext)
    (v/assert kb (list dog4_t Muffet) 'UniverseContext)
    (is (empty? (v/sentexes-matching kb (list breathes4 Muffet) 'UniverseContext))
        "nothing yet — dog4_t is not a kind of animal4_t")
    (v/assert kb (list 'genl dog4_t animal4_t) 'UniverseContext)
    (is (seq (v/sentexes-matching kb (list breathes4 Muffet) 'UniverseContext))
        "the edge arriving is what makes the stored fact match the rule")))

(tu/deftest-kb the-same-three-sentences-in-the-other-order-agree
  (tu/with-terms [dog5_t animal5_t breathes5 Muffet]
    (v/assert kb (list 'genl animal5_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl dog5_t animal5_t) 'UniverseContext)
    (v/assert kb (list 'implies (list animal5_t '?x) (list breathes5 '?x)) 'UniverseContext)
    (v/assert kb (list dog5_t Muffet) 'UniverseContext)
    (is (seq (v/sentexes-matching kb (list breathes5 Muffet) 'UniverseContext)))))

;; ---- backward chaining: a rule is a sentex ------------------------------

(tu/deftest-kb a-rule-in-an-invisible-context-answers-nothing
  (tu/with-terms [parentOf6 ancestorOf6 Tom Bob AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list parentOf6 '?x '?y) (list ancestorOf6 '?x '?y)))
              AContext)
    (v/assert kb (list parentOf6 Tom Bob) BContext)
    (testing "every backward path agrees: B does not reason with A's rule"
      (is (empty? (v/ask kb (list ancestorOf6 Tom Bob) BContext)))
      (is (empty? (v/prove kb (list ancestorOf6 Tom Bob) BContext)))
      (is (empty? (v/prove kb (list ancestorOf6 Tom Bob) BContext)))
      (is (empty? (v/lookup kb 7 (list ancestorOf6 Tom Bob) BContext))))
    (testing "and the forward firing of that same rule agrees — no placement"
      (is (empty? (v/sentexes-matching kb (list ancestorOf6 Tom Bob)))))))

(tu/deftest-kb a-rule-the-goal-context-inherits-answers
  (tu/with-terms [parentOf7 ancestorOf7 Tom Bob AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list parentOf7 '?x '?y) (list ancestorOf7 '?x '?y)))
              'UniverseContext)
    (v/assert kb (list parentOf7 Tom Bob) BContext)
    (is (seq (v/query kb (list ancestorOf7 Tom Bob) BContext {:max-depth 2})))
    (is (seq (v/prove kb (list ancestorOf7 Tom Bob) BContext)))
    (is (seq (v/prove kb (list ancestorOf7 Tom Bob) BContext)))))

;; ---- argPreserving: a claim travels the edges the asker can see ---------

(tu/deftest-kb an-inherited-claim-stops-at-an-invisible-edge
  (tu/with-terms [biggerThan8 retriever_t dog8_t cat8_t AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'binaryPredicate biggerThan8) 'UniverseContext)
    (v/assert kb (list 'argPreserving biggerThan8 1 'genl) 'UniverseContext)
    (v/assert kb (list 'genl retriever_t dog8_t) AContext)
    (v/assert kb (list biggerThan8 dog8_t cat8_t) BContext)
    (is (empty? (v/ask kb (list biggerThan8 retriever_t cat8_t) BContext))
        "B holds the claim about dogs and no edge putting retrievers under them")))

(tu/deftest-kb an-inherited-claim-travels-a-visible-edge
  (tu/with-terms [biggerThan9 retriever_t dog9_t cat9_t AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'binaryPredicate biggerThan9) 'UniverseContext)
    (v/assert kb (list 'argPreserving biggerThan9 1 'genl) 'UniverseContext)
    (v/assert kb (list 'genl retriever_t dog9_t) 'UniverseContext)
    (v/assert kb (list biggerThan9 dog9_t cat9_t) BContext)
    (is (seq (v/ask kb (list biggerThan9 retriever_t cat9_t) BContext)))))

;; The pair above travels `genl`, whose transitivity is the engine's own.  When the
;; relation is an ordinary predicate, the *licence to walk it at all* is a stored
;; `(transitive R)`, and `inherit/usable-relation?` reads that from the asker's vantage
;; like everything else — which on this KB deliberately changes nothing, and the
;; control below is why.  There is no leak to pair it with here: the leak is
;; unconstructible on a KB carrying CoreContext, and `inherit_test` builds the pair on
;; one that does not.

(tu/deftest-kb predicate-metadata-is-a-licence-the-whole-kb-holds
  ;; `transitive` is a `decontextualizedPredicate`, so A's declaration is *lifted* into
  ;; UniverseContext and B sees it — predicate metadata is a claim about the vocabulary
  ;; rather than a claim of a context, and the lift is what says so.  So B may walk
  ;; the relation, and what licensed it is the lift, not a peek into a sibling.
  (tu/with-terms [cursed8 begat8 A8 B8 AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'transitive begat8) AContext)
    (is (seq (v/sentexes-matching kb (list 'transitive begat8) 'UniverseContext))
        "the lift put it where every context can see it")
    (v/assert kb (list 'argPreserving cursed8 1 begat8) BContext)
    (v/assert kb (list begat8 A8 B8) BContext)
    (v/assert kb (list cursed8 B8) BContext)
    (is (seq (v/ask kb (list cursed8 A8) BContext))
        "so the claim travels the relation for B as much as for A")))

;; ---- equality: a merge renames only what it is visible from -------------
;;
;; The one that *loses* knowledge rather than adding it.  Migration and supersession
;; check visibility per sentex; if the goal rewrite does not, a context asks under a
;; spelling nothing renamed and gets nothing back — for a fact it still believes.

(tu/deftest-kb an-invisible-merge-does-not-rename-a-context-s-question
  (tu/with-terms [canFly10 Clark Superman AContext BContext]
    (siblings! kb AContext BContext)
    (let [h (v/assert kb (list canFly10 Clark) BContext)]
      (v/assert kb (list 'rewriteOf Superman Clark) AContext)
      (testing "B keeps believing its fact"
        (is (v/in? kb h))
        (is (some? (v/handle-of kb (list canFly10 Clark) BContext))))
      (testing "...and can still retrieve it, under the only spelling B knows"
        (is (seq (v/sentexes-matching kb (list canFly10 Clark) BContext)))
        (is (seq (v/ask kb (list canFly10 Clark) BContext))))
      (testing "no twin was made in B — the merge is not B's to apply"
        (is (empty? (v/contexts-of kb (list canFly10 Superman)))))
      (testing "and the class reads scope with it"
        (is (not (v/same-class? kb Clark Superman BContext)))
        (is (v/same-class? kb Clark Superman AContext))
        (is (= Clark (v/representative kb Clark BContext)))
        (is (= Superman (v/representative kb Clark AContext)))))))

(tu/deftest-kb a-visible-merge-renames-and-supersedes
  (tu/with-terms [canFly11 Clark Superman AContext BContext]
    (siblings! kb AContext BContext)
    (let [h (v/assert kb (list canFly11 Clark) BContext)]
      (v/assert kb (list 'rewriteOf Superman Clark) 'UniverseContext)
      (is (not (v/in? kb h)) "the retired spelling stops being believed")
      (is (= [BContext] (vec (v/contexts-of kb (list canFly11 Superman))))
          "the twin is placed where the fact lives")
      (is (seq (v/sentexes-matching kb (list canFly11 Clark) BContext)) "the old question still works")
      (is (seq (v/sentexes-matching kb (list canFly11 Superman) BContext))))))

(tu/deftest-kb the-unique-name-assumption-survives-an-invisible-merge
  (tu/with-terms [Clark12 Superman12 AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'sameAs Clark12 Superman12) AContext)
    (is (seq (v/ask kb (list 'different Clark12 Superman12) BContext))
        "B has been told nothing, so the two names still denote two things there")
    (is (empty? (v/ask kb (list 'different Clark12 Superman12) AContext))
        "A has been told")))

;; ---- equality down a chain: the reader is not the fact's own context ----
;;
;; The sibling lattice above is the case migration *declines*: nothing sees both the
;; fact and the merge, so there is no reader to serve.  A **chain** is the case it has
;; to serve, and it is the one where "check visibility per sentex" stops being enough —
;; because the party whose spelling is at stake is whoever reads the fact, and that is
;; any context below it, each electing over a different set of visible edges.

(defn- nested!
  "Wire `inner` under `outer` under UniverseContext: a strict chain, so `inner` sees
  everything `outer` does and `outer` sees none of `inner`'s."
  [kb outer inner]
  (v/assert kb (list 'genlContext outer 'UniverseContext) 'UniverseContext)
  (v/assert kb (list 'genlContext inner outer) 'UniverseContext))

(tu/deftest-kb a-reader-below-the-fact-retrieves-it-under-the-name-it-elects
  ;; The fact is MidContext's; the merge is LeafContext's alone.  Leaf sees both, so
  ;; Leaf elects Alpha — and a reader that can see a fact must be able to ask for it.
  (tu/with-terms [likes15 Tom15 Alpha15 Bravo15 MidContext LeafContext]
    (nested! kb MidContext LeafContext)
    (v/assert kb (list likes15 Tom15 Bravo15) MidContext)
    (v/assert kb (list 'rewriteOf Alpha15 Bravo15) LeafContext)
    (testing "Mid is told nothing and keeps its fact under its own spelling"
      (is (v/ask? kb (list likes15 Tom15 Bravo15) MidContext))
      (is (not (v/ask? kb (list likes15 Tom15 Alpha15) MidContext))
          "and does not acquire a name only Leaf can justify"))
    (testing "Leaf sees the fact and sees the merge, so it can ask under either name"
      (is (v/ask? kb (list likes15 Tom15 Alpha15) LeafContext)
          "the spelling Leaf elects")
      (is (v/ask? kb (list likes15 Tom15 Bravo15) LeafContext)
          "and the retired one, which is rewritten to it"))
    (testing "the twin is placed in the context whose view elected it"
      (is (= [LeafContext] (vec (v/contexts-of kb (list likes15 Tom15 Alpha15))))))
    (testing "and each reader gets the one fact once, under the name it elects"
      ;; Mid's spelling is believed where it lives and Leaf inherits it, so without a
      ;; reader-scoped staleness filter Leaf reports one fact twice under two names it
      ;; knows denote one thing — and every count over the answer set doubles
      (is (= [{'?x Alpha15}] (v/query kb (list likes15 Tom15 '?x) LeafContext)))
      (is (= [{'?x Bravo15}] (v/query kb (list likes15 Tom15 '?x) MidContext))))))

(tu/deftest-kb a-merge-a-context-cannot-see-does-not-choose-its-spelling
  ;; A class split across the chain: Mid sees only Bravo~Charlie and elects Bravo;
  ;; Leaf sees Alpha~Bravo too and elects Alpha.  One fact, two readers, two normal
  ;; forms — and neither reader may be handed the other's.
  (tu/with-terms [likes16 Tom16 Alpha16 Bravo16 Charlie16 MidContext LeafContext]
    (nested! kb MidContext LeafContext)
    (v/assert kb (list 'rewriteOf Bravo16 Charlie16) MidContext)
    (v/assert kb (list 'rewriteOf Alpha16 Bravo16) LeafContext)
    (v/assert kb (list likes16 Tom16 Charlie16) MidContext)
    (testing "each context elects over the edges it can see"
      (is (= Bravo16 (v/representative kb Charlie16 MidContext)))
      (is (= Alpha16 (v/representative kb Charlie16 LeafContext))))
    (testing "Mid can still retrieve the fact it asserted"
      (is (v/ask? kb (list likes16 Tom16 Charlie16) MidContext)
          "under the retired spelling, which Mid's own election rewrites")
      (is (v/ask? kb (list likes16 Tom16 Bravo16) MidContext)
          "and under the one Mid elects"))
    (testing "Mid is not handed the spelling only Leaf's edge produces"
      (is (not (v/ask? kb (list likes16 Tom16 Alpha16) MidContext))))
    (testing "Leaf, which sees both edges, retrieves it under all three"
      (is (v/ask? kb (list likes16 Tom16 Alpha16) LeafContext))
      (is (v/ask? kb (list likes16 Tom16 Bravo16) LeafContext))
      (is (v/ask? kb (list likes16 Tom16 Charlie16) LeafContext)))))

(tu/deftest-kb deprecated-scopes-like-the-three-class-reads-beside-it
  ;; `representative` / `same-class?` / `equiv-class` each take a context; without one
  ;; `deprecated?` reports a retirement no reader outside the merge's cone can see, and
  ;; the four reads of one partition disagree about one context.
  (tu/with-terms [Alpha17 Bravo17 MidContext LeafContext]
    (nested! kb MidContext LeafContext)
    (v/assert kb (list 'rewriteOf Alpha17 Bravo17) LeafContext)
    (testing "the merge's own cone sees the retirement"
      (is (v/deprecated? kb Bravo17 LeafContext))
      (is (= Alpha17 (v/representative kb Bravo17 LeafContext))))
    (testing "a context above it does not"
      (is (not (v/deprecated? kb Bravo17 MidContext)))
      (is (= Bravo17 (v/representative kb Bravo17 MidContext))
          "the control: Mid elects Bravo itself, so calling it deprecated contradicts"))
    (testing "the unscoped arity still answers globally"
      (is (v/deprecated? kb Bravo17)))))

;; ---- predicate metadata: declared in a theory, not published -----------

(tu/deftest-kb a-metadata-declaration-concludes-where-it-was-made
  (tu/with-terms [palOf13 AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'binaryPredicate palOf13) AContext)
    (v/assert kb (list 'symmetric palOf13) AContext)
    (testing "the derived predicate-type membership is the declaring context's"
      (is (seq (v/sentexes-matching kb (list 'symmetricPredicate palOf13) AContext)))
      (is (empty? (v/sentexes-matching kb (list 'symmetricPredicate palOf13) 'CoreContext))))
    (testing "the two ways of asking give one answer, from either vantage"
      (is (= (v/has-prop? kb :symmetric palOf13 AContext)
             (v/isa? kb palOf13 'symmetricPredicate AContext)))
      (is (= (v/has-prop? kb :symmetric palOf13 BContext)
             (v/isa? kb palOf13 'symmetricPredicate BContext))))))

(tu/deftest-kb a-derived-declaration-installs-live-not-only-on-recover
  ;; `recover` replays every stored sentex of the functor, so a declaration that
  ;; reaches the cache only there makes a restart change the answer
  (tu/with-terms [needsSep14 q1_t q2_t]
    (v/assert kb (list 'genl q1_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl q2_t 'thing) 'UniverseContext)
    (v/assert kb (list 'implies (list needsSep14 '?x) (list 'disjoint q1_t q2_t))
              'UniverseContext)
    (v/assert kb (list needsSep14 'Go) 'UniverseContext)
    (is (v/disjoint? kb q1_t q2_t 'UniverseContext)
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
  (tu/with-terms [a15_t b15_t AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'genl a15_t b15_t) AContext)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'genl b15_t a15_t) BContext))
        "refused although B cannot see the edge it closes a cycle with")))

(tu/deftest-kb a-cycle-belief-assembles-is-answered-alike-by-every-reader-of-it
  ;; The check above reads the **active** adjacency, so belief walks around it: defeat an
  ;; edge, assert its reverse — nothing is cyclic while the first is out — then retract
  ;; the defeater and both stand.  Nothing refuses the result, so the reads owe it an
  ;; answer rather than an assumption, and the three readers of one question owe the
  ;; *same* answer.  The potential ranks the condensation, so the two types are level
  ;; rather than ordered, and a scoped walk pruned on a strict descent alone denies the
  ;; edge its own closure returns.
  (tu/with-terms [c18_t d18_t e18_t AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'genl c18_t d18_t) AContext)
    (let [h (v/assert kb (list 'not (list 'genl c18_t d18_t)) AContext {:strength :monotonic})]
      (v/assert kb (list 'genl d18_t c18_t) AContext)    ; admitted: the first edge is out
      (v/retract! kb h))                                 ; and now both of them stand
    (v/assert kb (list 'genl e18_t 'thing) BContext)     ; a second asserting context
    (testing "A sees both edges, and every read of them agrees"
      (is (contains? (v/genls kb c18_t AContext) d18_t))
      (is (v/genl? kb c18_t d18_t AContext))
      (is (contains? (v/genls kb d18_t AContext) c18_t))
      (is (v/genl? kb d18_t c18_t AContext))
      (is (contains? (v/specs kb d18_t AContext) c18_t)))
    (testing "B sees neither, and every read of them agrees about that too"
      (is (not (contains? (v/genls kb c18_t BContext) d18_t)))
      (is (not (v/genl? kb c18_t d18_t BContext)))
      (is (not (v/genl? kb d18_t c18_t BContext))))))

(tu/deftest-kb the-genlContext-closure-is-global-on-purpose
  ;; visibility scoped by visibility is circular, and every genlContext edge is forced
  ;; into UniverseContext anyway (`forcedDecontextualizedPredicate`)
  (tu/with-terms [AContext BContext]
    (siblings! kb AContext BContext)
    (is (= ['UniverseContext] (vec (v/contexts-of kb (list 'genlContext AContext 'UniverseContext))))
        "the topology has one canonical home, whoever asserted the edge")))

(tu/deftest-kb argument-sorting-is-a-storage-key-and-so-is-global
  ;; a sentex has one key: if whether a predicate sorts its arguments varied by reader,
  ;; one literal would store under two keys and dedup, retraction and the mirror probe
  ;; would all break at once
  (tu/with-terms [palOf16 Bob Ann AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list 'binaryPredicate palOf16) 'UniverseContext)
    (v/assert kb (list 'symmetric palOf16) AContext)
    (v/assert kb (list palOf16 Bob Ann) BContext)
    (is (seq (v/sentexes-matching kb (list palOf16 Ann Bob) BContext))
        "B retrieves the mirror, because storage sorted the arguments and storage
         does not vary by reader")))

(tu/deftest-kb an-open-context-query-joins-across-incomparable-contexts
  ;; Pinned, not endorsed.  `?ctx` is a question about the KB rather than from a
  ;; vantage, so a conjunctive `prove` joins literals no single context sees together.
  ;; ../vaelii drops such an answer for want of a common floor and offers `CxAll` /
  ;; `CxInference` for the union; here the union is what `?ctx` means, and a caller
  ;; wanting the floor names a context.
  (tu/with-terms [leftP17 rightP17 Item AContext BContext]
    (siblings! kb AContext BContext)
    (v/assert kb (list leftP17 Item) AContext)
    (v/assert kb (list rightP17 Item) BContext)
    (is (seq (v/prove kb [(list leftP17 '?x) (list rightP17 '?x)] '?ctx))
        "the open question unions the two contexts")
    (is (empty? (v/prove kb [(list leftP17 '?x) (list rightP17 '?x)] AContext))
        "asked from a context, it answers only what that context holds")
    (is (empty? (v/prove kb [(list leftP17 '?x) (list rightP17 '?x)] BContext)))))
