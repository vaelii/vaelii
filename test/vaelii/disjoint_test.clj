;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjoint-test
  "disjoint and disjoint_metatype, and the contradiction detection they drive."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb disjoint-blocks-conflicting-membership
  (let [dog (tu/tmp-type) cat (tu/tmp-type)
        muffet (tu/tmp-ind) whiskers (tu/tmp-ind)]
    ;; the declaration constrains where it is visible, so the asserting context is
    ;; wired below it — the same wiring the starter's spindle gives every real one
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (testing "the same individual can't take a disjoint type"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat muffet) 'CxNaturalWorld))))
    (testing "a compatible individual is unaffected"
      (is (v/assert kb (list cat whiskers) 'CxNaturalWorld)))))

(tu/deftest-kb disjointness-inherited-through-genl
  (let [dog (tu/tmp-type) mammal (tu/tmp-type)
        trout (tu/tmp-type) fish (tu/tmp-type) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl dog mammal) 'CxUniverse)
    (v/assert kb (list 'genl trout fish) 'CxUniverse)
    (v/assert kb (list 'disjoint mammal fish) 'CxUniverse)
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (testing "subtypes of disjoint types are disjoint"
      (is (v/disjoint? kb dog trout))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list trout muffet) 'CxNaturalWorld))))))

(tu/deftest-kb disjoint-type-makes-members-disjoint
  (let [animal_species (tu/tmp-pred)
        dog (tu/tmp-type) cat (tu/tmp-type) fish (tu/tmp-type) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list animal_species dog) 'CxUniverse)
    (v/assert kb (list animal_species cat) 'CxUniverse)
    (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)   ; members become pairwise disjoint
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (testing "members of a disjoint metatype are disjoint"
      (is (v/disjoint? kb dog cat))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat muffet) 'CxNaturalWorld))))
    (testing "a member added after the declaration is also disjoint"
      (v/assert kb (list animal_species fish) 'CxUniverse)
      (is (v/disjoint? kb dog fish)))))

(tu/deftest-kb a-membership-is-recorded-on-the-marks-storage-not-its-belief
  ;; `(M T)` is a *supporter* of T's membership, so the member arm records it whenever
  ;; the mark is stored, whatever the mark's label; belief follows through the flat-cache
  ;; reconcile.  Gated on belief instead, the same four facts would separate the pair in
  ;; one arrival order and not the other.
  (let [species (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type)
        t (reasoning/taxonomy kb)]
    (v/assert kb (list 'disjoint_metatype species) 'CxUniverse)
    (v/assert kb (list species dog) 'CxUniverse)
    (let [neg (v/assert kb (list 'not (list 'disjoint_metatype species)) 'CxUniverse
                        {:strength :monotonic})]
      (is (not (tax/disjoint-metatype? t species)) "the mark is defeated")
      (is (tax/stored-disjoint-metatype? t species) "but it is still stored")
      (v/assert kb (list species cat) 'CxUniverse)
      (is (= #{dog cat} (tax/metatype-members t species))
          "a member stated while the mark is OUT is recorded")
      (is (not (v/disjoint? kb dog cat)) "and separates nothing while the mark is OUT")
      (v/retract! kb neg)
      (is (tax/disjoint-metatype? t species) "the mark revives")
      (is (v/disjoint? kb dog cat)
          "and separates the member stated during the defeat — the same answer the
           member-before-defeat order gives"))))

(tu/deftest-kb a-member-retracted-while-the-mark-is-defeated-leaves-no-support
  (let [species (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type)
        t (reasoning/taxonomy kb)]
    (v/assert kb (list 'disjoint_metatype species) 'CxUniverse)
    (v/assert kb (list species dog) 'CxUniverse)
    (let [hcat (v/assert kb (list species cat) 'CxUniverse)
          neg  (v/assert kb (list 'not (list 'disjoint_metatype species)) 'CxUniverse
                         {:strength :monotonic})]
      (v/retract! kb hcat)
      (is (nil? (get-in @t [:cache-support [:member species cat]]))
          "the membership's support entry goes with the sentex")
      (is (nil? (get-in @t [:cache-handle-keys hcat]))
          "and the handle leaves the reverse index")
      (v/retract! kb neg)
      (is (= #{dog} (tax/metatype-members t species)))
      (is (not (v/disjoint? kb dog cat))
          "a retracted membership separates nothing once the mark revives"))))

(tu/deftest-kb a-rebuild-records-the-members-the-live-kb-records
  ;; `rebuild-taxonomy`'s member pass walks every stored mark, so a restart yields the
  ;; members the live arm recorded — including one stated while the mark was defeated.
  (let [species (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type)
        t (reasoning/taxonomy kb)]
    (v/assert kb (list 'disjoint_metatype species) 'CxUniverse)
    (v/assert kb (list species dog) 'CxUniverse)
    (let [neg (v/assert kb (list 'not (list 'disjoint_metatype species)) 'CxUniverse
                        {:strength :monotonic})]
      (v/assert kb (list species cat) 'CxUniverse)
      (let [live (tax/metatype-members t species)]
        (v/recover kb)
        (is (= live (tax/metatype-members t species)) "same members after recover")
        (is (not (tax/disjoint-metatype? t species)) "the defeat survives recover"))
      (v/retract! kb neg)
      (is (v/disjoint? kb dog cat)))))

(tu/deftest-kb a-rule-concluded-membership-is-recorded-where-an-asserted-one-is
  ;; The member arm keys on nothing a table can name — the functor *is* the metatype —
  ;; so it is one of the structural integrate arms, and the derivation path has to reach
  ;; it.  `rebuild-taxonomy`'s member pass walks every stored `(M T)` whatever put it
  ;; there, so an arm the derivation path skipped would separate the pair only once a
  ;; restart had replayed it: the running KB and the recovered one disagreeing about one
  ;; store, which is the one thing a derivation-path integration exists to prevent.
  (let [species (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type) seed (tu/tmp-pred)
        Kim (tu/tmp-ind) t (reasoning/taxonomy kb)]
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint_metatype species) 'CxUniverse)
    (v/assert kb (list species dog) 'CxUniverse)
    ;; `cat` joins the metatype only by inference — nothing states `(species cat)`
    (v/assert kb (list 'implies (list seed '?x) (list species '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list seed cat) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list species cat) '?c)) "the membership is derived")
    (let [live (tax/metatype-members t species)]
      (is (= #{dog cat} live) "and recorded, as a stated membership is")
      (is (v/disjoint? kb dog cat) "so the two are separated at once")
      (v/assert kb (list dog Kim) 'CxNaturalWorld)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat Kim) 'CxNaturalWorld))
          "and the separation constrains, having reached the same cache")
      (testing "the restarted KB records exactly the same members"
        (v/recover kb)
        (is (= live (tax/metatype-members t species)))
        (is (v/disjoint? kb dog cat))))))

(tu/deftest-kb a-metatype-separates-predicates-not-only-individuals
  ;; the definitional checks admit any term, so the predicate meta-ontology is
  ;; enforced the way the domain is — this is what makes relation_kind bite
  (let [kind (tu/tmp-pred) instanceKind (tu/tmp-type) typeKind (tu/tmp-type)
        rel (tu/tmp-pred) other (tu/tmp-pred)]
    (v/assert kb (list 'genl instanceKind 'predicate) 'CxUniverse)
    (v/assert kb (list 'genl typeKind 'predicate) 'CxUniverse)
    (v/assert kb (list kind instanceKind) 'CxUniverse)
    (v/assert kb (list kind typeKind) 'CxUniverse)
    (v/assert kb (list 'disjoint_metatype kind) 'CxUniverse)
    (v/assert kb (list instanceKind rel) 'CxUniverse)
    (testing "one predicate cannot take both kinds"
      (is (v/disjoint? kb instanceKind typeKind))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list typeKind rel) 'CxUniverse))))
    (testing "a different predicate is unaffected"
      (is (v/assert kb (list typeKind other) 'CxUniverse)))))

(tu/deftest-kb argisa-constrains-a-predicate-valued-position
  ;; (arg typeToInstancePred 1 type_relation_predicate) is only enforceable because
  ;; the argument check reaches past CapitalCamelCase individuals
  ;; Pinned to the constraint reading: the position holds a symbol, so with the entailment
  ;; on the declaration mints the metatype rather than convicting the predicate that lacks
  ;; it (docs/argtypes.md).
  (tu/without-entailing
   (let [typeKind (tu/tmp-type) otherKind (tu/tmp-type) link (tu/tmp-pred)
         typeLevel (tu/tmp-pred) instanceLevel (tu/tmp-pred) unclassified (tu/tmp-pred)]
     (v/assert kb (list 'genl typeKind 'thing) 'CxUniverse)
     (v/assert kb (list 'genl otherKind 'thing) 'CxUniverse)
     (v/assert kb (list 'arg link 1 typeKind) 'CxUniverse)
     (v/assert kb (list typeKind typeLevel) 'CxUniverse)
     (v/assert kb (list otherKind unclassified) 'CxUniverse)
     (testing "a correctly classified predicate satisfies the constraint"
       (is (v/assert kb (list link typeLevel instanceLevel) 'CxUniverse)))
     (testing "a predicate typed as something else violates it"
       (is (thrown? clojure.lang.ExceptionInfo
                    (v/assert kb (list link unclassified instanceLevel) 'CxUniverse))))
     (testing "open-world survives: a predicate with no type at all cannot violate"
       (is (v/assert kb (list link (tu/tmp-pred) instanceLevel) 'CxUniverse))))))

;;; ── the reach of a disjointness: exactly its declaration's visibility ──

(tu/deftest-kb a-disjointness-counts-only-where-its-declaration-is-visible
  ;; The OpenCyc shape, now answered the way Cyc answers it: the context ancestor set is
  ;; applied at lookup, so a `(disjoint …)` stated in one context separates the
  ;; pair exactly where that statement is visible.  Cyc states `(disjointWith
  ;; #$Place #$Agent-Generic)` in PhysicalGeographyMt alone, and separately makes a
  ;; city both a place and (via GeopoliticalEntity, an Organization) an agent — and
  ;; stays consistent, because the disjointness and the full subsumption path never
  ;; coexist in any one context's ancestor set.  A sibling context that cannot see the
  ;; declaration is not constrained by it; the unscoped read still reports every
  ;; declaration in the KB, which is what a global auditor wants.
  (tu/with-terms [a_place an_agent a_city CxPhysicalGeography CxGeography
                  Delhi Cairo Rome]
    (v/assert kb (list 'genl a_place 'thing) 'CxUniverse)
    (v/assert kb (list 'genl an_agent 'thing) 'CxUniverse)
    (v/assert kb (list 'genl a_city a_place) 'CxUniverse)

    ;; two contexts that cannot see each other
    (v/assert kb (list 'genlCx CxPhysicalGeography 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxGeography 'CxUniverse) 'CxUniverse)
    (is (not (v/sees? kb CxGeography CxPhysicalGeography)))

    ;; the disjointness is stated in one of them only
    (v/assert kb (list 'disjoint a_place an_agent) CxPhysicalGeography)

    (testing "it holds where its declaration is visible"
      (is (v/disjoint? kb a_place an_agent CxPhysicalGeography)))
    (testing "and not in the sibling, which never said it and cannot see it"
      (is (not (v/disjoint? kb a_place an_agent CxGeography))))
    (testing "the unscoped read still sees every declaration in the KB"
      (is (v/disjoint? kb a_place an_agent)))

    (testing "so the membership admissible where it is stated is admitted"
      (v/assert kb (list a_city Delhi) CxGeography)
      (is (v/assert kb (list an_agent Delhi) CxGeography)
          "Delhi is a city here; the separation was stated elsewhere, out of sight"))

    (testing "while the declaring context still refuses its own"
      (v/assert kb (list a_city Cairo) CxPhysicalGeography)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list an_agent Cairo) CxPhysicalGeography))))

    (testing "retracting the one supporter releases the declaring context too"
      ;; refcounting is orthogonal to scoping: one supporter, so retraction tears
      ;; the cache entry down and the declaring context stops refusing
      (v/retract! kb (v/handle-of kb (list 'disjoint a_place an_agent) CxPhysicalGeography))
      (is (not (v/disjoint? kb a_place an_agent)))
      (v/assert kb (list a_city Rome) CxPhysicalGeography)
      (is (v/assert kb (list an_agent Rome) CxPhysicalGeography)))))

;;; ── which context may hold the conflicting membership ────────────────

;; The check has two halves, both context-scoped, and a three-context lattice is what
;; pins each.  Two incomparable specifics under one general:
;;
;;      CxUniverse
;;            │
;;         CxC
;;         ╱      ╲
;;   CxA    CxB
;;
;; `(disjoint t1 t2)` in A alone; the two halves are then
;;   - **is the pair disjoint?** — the declaration (and any genl edge the
;;     disjointness closes under) must be visible from the asserting context;
;;   - **does X already hold the other type?** — `types-of`, filtered by the same
;;     genlCx up-closure.
;; So the declaration's context and the membership's context are both decisive: a
;; context is only ever refused on grounds it can see.

(defn- assert-outcome
  "`:ok`, or the `:type` of the refusal — so a case is indistinguishable from a value rather than as
  the presence or absence of a throw."
  [kb sentence context]
  (try (v/assert kb sentence context) :ok
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb which-of-three-contexts-admits-the-conflicting-membership
  (tu/with-terms [CxA CxB CxC t1 t2 Pip Quo]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB CxC) 'CxUniverse)
    (v/assert kb (list 'disjoint t1 t2) CxA)

    (testing "the lattice: siblings see neither each other nor themselves from above"
      (is (not (v/sees? kb CxA CxB)))
      (is (not (v/sees? kb CxB CxA)))
      (is (not (v/sees? kb CxC CxA)))
      (is (v/sees? kb CxA CxC))
      (is (v/sees? kb CxC 'CxUniverse)))

    (testing "the membership up in CxUniverse: only A refuses"
      ;; every context in the lattice sees CxUniverse, so every one of them reads
      ;; the (t1 Pip) that could make (t2 Pip) a violation — but only A can see the
      ;; disjointness, stated in A itself, so B and C are no longer refused on a
      ;; declaration made below C in a sibling of B
      (v/assert kb (list t1 Pip) 'CxUniverse)
      (is (= {CxA :disjoint, CxB :ok, CxC :ok}
             (into {} (for [c [CxA CxB CxC]]
                        [c (assert-outcome kb (list t2 Pip) c)])))))

    (testing "the membership down in A: only A is refused"
      ;; the same disjointness, the same three contexts — only the membership moved,
      ;; and it moved out of B's and C's sight
      (v/assert kb (list t1 Quo) CxA)
      (is (= {CxA :disjoint, CxB :ok, CxC :ok}
             (into {} (for [c [CxA CxB CxC]]
                        [c (assert-outcome kb (list t2 Quo) c)])))))))

(tu/deftest-kb a-general-context-may-be-given-what-a-specific-one-forbids
  ;; The corollary, and the sharp edge: the check runs once, where the sentence is
  ;; written, against what *that* context can see.  Writing the conflicting
  ;; membership into the more general context is admitted — C cannot see A — and the
  ;; clash that creates *for A* is a real contradiction A can see whole.  Seeing a
  ;; clash and being blamed for one are different questions: the writer is refused
  ;; only on grounds it can see, and the joint question is answered by `settle`'s
  ;; exposure pass, as a `:disjoint` ledger entry naming where the clash is visible
  ;; from.  This test is the acceptance criterion for that split.
  (tu/with-terms [CxA CxC t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
    (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
    (v/assert kb (list t1 Pip) CxA)

    (testing "admitted in the general context, which cannot see the specific one"
      (is (= :ok (assert-outcome kb (list t2 Pip) CxC))))

    (testing "and A now reads both halves of a pair it is the only context to refuse"
      (is (= #{t1 t2} (set (v/types-of kb Pip CxA))))
      (is (= :disjoint (assert-outcome kb (list t2 Pip) CxA))
          "stating it in A directly is still refused — only the route through C is open"))

    (testing "the ledger reports the clash, naming the context that sees it"
      (let [vs (v/violations kb)]
        (is (= [:disjoint] (mapv :violation vs)))
        (let [d (:detail (first vs))]
          (is (= Pip (:term d)))
          (is (= #{CxA} (:visible-from d)))
          (is (= #{t1 t2} (into #{} (map first) (:held d)))))))

    (testing "exposure is a report, not an arbitration: belief is untouched"
      (is (empty? (v/conflicts kb)))
      (is (empty? (v/contradictions kb))))))

(tu/deftest-kb a-disjoint-metatype-does-not-separate-genl-related-members
  ;; Two members of a disjoint metatype separate only when neither generalizes the
  ;; other: `(genl bb aa)` says every `bb` is an `aa`, so they overlap and cannot be
  ;; disjoint — the same rule the explicit-`disjoint` entry point applies.  Without the guard a
  ;; type came out disjoint from its own supertype, and from itself.
  (let [mkind (tu/tmp-pred)
        aa (tu/tmp-type) bb (tu/tmp-type) x (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list mkind aa) 'CxUniverse)
    (v/assert kb (list mkind bb) 'CxUniverse)
    (v/assert kb (list 'genl bb aa) 'CxUniverse)          ; bb is a kind of aa
    (v/assert kb (list 'disjoint_metatype mkind) 'CxUniverse)
    (testing "a type is not disjoint from itself"
      (is (not (v/disjoint? kb bb bb)))
      (is (not (v/disjoint? kb aa aa))))
    (testing "nor from its own supertype it shares the metatype with"
      (is (not (v/disjoint? kb bb aa)))
      (is (not (v/disjoint? kb aa bb))))
    (testing "and the entailed membership is admitted, not refused as a clash"
      (v/assert kb (list bb x) 'CxNaturalWorld)
      (is (v/isa? kb x aa 'CxNaturalWorld) "every bb is an aa, so x is an aa"))))
