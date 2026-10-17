;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.exposure-test
  "Two memberships each admissible where stated, whose types some context can jointly
  see as disjoint, are a real contradiction.  Every reader that sees the pair whole
  decides it, and no writer is refused on grounds it cannot see.

  Three routes bring one clash into joint sight — the membership arriving last, the
  separating declaration arriving last, the `genlCx` edge arriving last — and the answer
  is route-agnostic.  Each route gets a test; the shared lattice is two siblings under
  CxUniverse, with the joint viewer (when one exists) below both.  The membership-last
  route's acceptance test is
  `disjoint_test/a-general-context-may-be-given-what-a-specific-one-forbids`.

  **A separation derivable only below the members' maximal common descendant is decided
  too**: the context under it that reads the whole clash decides it
  (`chain/place-memberships!`), so `deep-separation!`'s lattice is decided where the separation
  comes into view.  The settle files no `:disjoint` ledger entry, and `exposed-clashes`
  answers the standing question of every jointly-visible pair, decided or not."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- siblings!
  "Two sibling contexts under CxUniverse, two root types, one term holding one
  type in each sibling — admissible everywhere, since neither sibling sees the
  other."
  [kb {:keys [a b t1 t2 x]}]
  (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
  (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse)
  (v/assert kb (list t1 x) a)
  (v/assert kb (list t2 x) b))

(defn- deep-separation!
  "`siblings!`'s two memberships, a joint viewer `w` below both, and the separation
  written in `decl` — a context `w` cannot see.

  `w` is the maximal common descendant of the two memberships' contexts and derives no
  separation, so it convicts nothing.  A context below both `w` and `decl` sees the whole
  clash, and is the vantage that decides it."
  [kb {:keys [a b w decl t1 t2] :as spec}]
  (v/assert kb (list 'genlCx decl 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'disjoint t1 t2) decl)
  (siblings! kb spec)
  (v/assert kb (list 'genlCx w a) 'CxUniverse)
  (v/assert kb (list 'genlCx w b) 'CxUniverse))

(defn- deep-viewer!
  "A context below `w` and `decl`: the one that reads the separation and both
  memberships, and so the vantage that decides the pair.  The `decl` edge arrives last,
  so the settle that decides it is that edge's."
  [kb v w decl]
  (v/assert kb (list 'genlCx v w) 'CxUniverse)
  (v/assert kb (list 'genlCx v decl) 'CxUniverse))

(tu/deftest-kb siblings-with-no-joint-viewer-expose-nothing
  ;; the pin for the ∃-descendant reading: the memberships coexist, the declaration
  ;; is visible to both writers, and still no single context sees the whole clash —
  ;; so there is nothing to report and nobody to report it to.
  (tu/with-terms [CxA CxB left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'CxUniverse)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (is (empty? (v/violations kb)))
    (is (seq (v/sentexes-matching kb (list left_t Pip) CxA)))
    (is (seq (v/sentexes-matching kb (list right_t Pip) CxB)))))

(tu/deftest-kb a-genlCx-edge-arriving-last-decides-the-clash
  ;; the visibility route: everything else stands, and wiring a joint viewer below
  ;; both siblings is what makes the clash visible — the edge's own settle weighs it.
  ;; CxW is the vantage, and it sees the separation in CxUniverse, so the pair is
  ;; decided rather than reported.  Both memberships are `:default`, so CxW cannot rank
  ;; them and the answer is a dilemma.
  (tu/with-terms [CxA CxB CxW left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'CxUniverse)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (is (empty? (v/contradictions kb)) "seeing one side is not seeing the clash")
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs)))
      (is (= #{(list left_t Pip) (list right_t Pip)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb))
        "decided is not exposed: the ledger does not also claim the pair")))

(tu/deftest-kb a-rebuild-decides-a-deep-separation-as-the-live-settle-did
  ;; The pass reports what a *change* newly made jointly visible, so a `recover` — which
  ;; changes nothing — files nothing; the pair it holds is decided by the rebuild's settle
  ;; exactly as the live settle decided it.
  ;;
  ;;   CxUniverse
  ;;     ├─ CxA CxB          one membership each
  ;;     └─ CxDecl           (disjoint left_t right_t)
  ;;   CxW sees CxA and CxB  — reads no separation
  ;;     └─ CxV sees CxW and CxDecl   — where the clash is visible whole: the vantage
  (tu/with-terms [CxA CxB CxW CxDecl CxV left_t right_t Pip]
    (deep-separation! kb {:a CxA :b CxB :w CxW :decl CxDecl
                          :t1 left_t :t2 right_t :x Pip})
    (deep-viewer! kb CxV CxW CxDecl)
    (let [read (fn [] {:w  [(v/ask? kb (list left_t Pip) CxW) (v/ask? kb (list right_t Pip) CxW)]
                       :at-v (mapv :kind (v/contradictions kb CxV))
                       :at-w (mapv :kind (v/contradictions kb CxW))
                       :vs (mapv :violation (v/violations kb))})
          live (read)]
      (is (= {:w [true true] :at-v [:disjoint] :at-w [] :vs []} live)
          "two defaults: a dilemma at CxV, nothing at CxW, which reads no separation, and
           nothing reported")
      (v/recover kb)
      (is (= live (read)) "and the rebuild reaches the same reading, filing nothing"))))

(tu/deftest-kb the-standing-question-is-answerable-on-demand
  ;; `settle` decides what a change newly put in joint sight; this reports what the KB
  ;; holds now, decided or not.  It is the whole-KB question, asked by a caller who chose
  ;; to — and it is what an imported KB has instead of a settle that ran while the content
  ;; was arriving.
  (tu/with-terms [CxA CxB CxW CxDecl CxV left_t right_t Pip]
    (v/assert kb (list 'genlCx CxDecl 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint left_t right_t) CxDecl)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (testing "before a joint viewer of the separation exists there is nothing to see"
      (is (empty? (v/violations kb)))
      (is (empty? (v/exposed-clashes kb))))
    (deep-viewer! kb CxV CxW CxDecl)
    (let [asked (v/exposed-clashes kb)]
      (is (= [:disjoint] (mapv :violation asked)))
      (is (= #{CxV} (set (get-in (first asked) [:detail :visible-from])))
          "visible from the context the settle decided it at")
      (is (empty? (v/violations kb)) "decided, so the settle filed nothing")
      (testing "and asking does not file, store, or move belief"
        (let [before (tu/content-count kb)]
          (is (seq (v/exposed-clashes kb)))
          (is (empty? (v/violations kb)))
          (is (= before (tu/content-count kb))))))
    (testing "it survives the rebuild"
      (v/recover kb)
      (is (empty? (v/violations kb)) "the rebuild filed nothing")
      (is (= [:disjoint] (mapv :violation (v/exposed-clashes kb)))
          "and the clash is still there to be asked about"))
    (testing "and it goes when the clash does"
      (v/retract! kb (v/handle-of kb (list 'disjoint left_t right_t) CxDecl))
      (is (empty? (v/exposed-clashes kb))))))

(tu/deftest-kb a-declaration-arriving-last-decides-a-clash-only-a-descendant-sees
  ;; the separation route: two memberships in sibling contexts, jointly visible only from
  ;; a context below both, and the disjointness arriving is what makes them a clash.
  ;; Neither member's own context sees the pair; CxD does, so CxD is the vantage and
  ;; weighs it.  Two defaults are a dilemma.
  (tu/with-terms [CxA CxB CxD t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list t1 Pip) CxA)
    (v/assert kb (list t2 Pip) CxB)
    (is (empty? (v/contradictions kb)) "compatible until somebody separates them")
    (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs)))
      (is (= #{(list t1 Pip) (list t2 Pip)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb)) "decided at CxD, not reported")))

(tu/deftest-kb a-genl-edge-arriving-last-decides-a-clash-only-a-descendant-sees
  ;; the closure route: the held types are not themselves separated — a subtype edge
  ;; arriving puts one of them under a separated type, and the instances below its sub
  ;; side are re-examined.  The two memberships sit in sibling contexts, so CxD is the
  ;; only context that sees the pair and the only one that weighs it.
  (tu/with-terms [CxA CxB CxD dog_t canine_t cat_t Rex]
    (v/assert kb (list 'genl canine_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint canine_t cat_t) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list dog_t Rex) CxA)
    (v/assert kb (list cat_t Rex) CxB)
    (is (empty? (v/contradictions kb)) "a dog-cat is odd but nothing separates them yet")
    (v/assert kb (list 'genl dog_t canine_t) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs)))
      (is (= #{(list dog_t Rex) (list cat_t Rex)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb)) "decided at CxD, not reported")))

(tu/deftest-kb a-deep-separation-is-decided-again-when-its-member-returns
  ;; The separation sits below the members' maximal common descendant
  ;; (`deep-separation!`), so the pair is CxV's to decide.  Retracting a member ends the
  ;; clash, and writing it again brings the decision back, with nothing filed either way.
  (tu/with-terms [CxA CxB CxW CxDecl CxV t1 t2 Pip]
    (v/assert kb (list 'genlCx CxDecl 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint t1 t2) CxDecl)
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (deep-viewer! kb CxV CxW CxDecl)
    (v/assert kb (list t1 Pip) CxA {:strength :monotonic})
    (let [decided? (fn [] (and (v/ask? kb (list t1 Pip) CxV)
                               (not (v/ask? kb (list t2 Pip) CxV))
                               (v/ask? kb (list t2 Pip) CxW)))
          h (v/assert kb (list t2 Pip) CxB)]
      (is (decided?) "CxV defeats the default member; CxW, which reads no separation, keeps it")
      (v/retract! kb h)
      (is (empty? (v/contradictions kb)) "the clash goes with its member")
      (v/assert kb (list t2 Pip) CxB)
      (is (decided?) "and comes back with it")
      (is (empty? (v/violations kb)) "decided each time, reported never"))))

(tu/deftest-kb an-unrelated-settle-leaves-a-deep-separation-decided
  ;; locality: a write touching neither member nor the separation leaves the decision
  ;; where it was.
  (tu/with-terms [CxA CxB CxW CxDecl CxV t1 t2 other Pip Quo]
    (deep-separation! kb {:a CxA :b CxB :w CxW :decl CxDecl :t1 t1 :t2 t2 :x Pip})
    (deep-viewer! kb CxV CxW CxDecl)
    (let [before (v/contradictions kb)]
      (is (= 1 (count before)))
      (v/assert kb (list other Quo) CxB)
      (v/assert kb (list other Pip) CxB)
      (is (= before (v/contradictions kb))
          "an unrelated membership — even of the clash's own term — moves nothing: the
           pair it forms with the standing types is not disjoint")
      (is (empty? (v/violations kb))))))

;;; ── a declaration arriving over many memberships ───────────────────────
;;
;; A reader finds a membership clash from the term its memberships name
;; (`membership/term-nogoods`), so the terms holding one side only are no candidates and a
;; declaration arriving reads none of them.

(tu/deftest-kb a-separation-decides-the-one-term-holding-both-sides
  ;; Forty terms sit below t1 alone and one below both.  The two memberships sit in
  ;; sibling contexts, so only the context below both sees the pair and decides it.
  (tu/with-terms [CxA CxB CxD t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (dotimes [_ 40]
      (v/assert kb (list t1 (tu/tmp-ind "Filler")) CxA))
    (v/assert kb (list t1 Pip) CxA)
    (v/assert kb (list t2 Pip) CxB)
    (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
    (is (= #{(list t1 Pip) (list t2 Pip)}
           (into #{} (mapcat #(map :sentence (:sides %))) (v/contradictions kb)))
        "the one term holding both is decided")))

(tu/deftest-kb a-metatype-declaration-arriving-last-decides-the-clash
  ;; `(disjoint_metatype M)` is a *unary* sentence whose argument is a symbol — the
  ;; same shape as a type membership — so the membership arm claims it unless the
  ;; declarations are matched first, and the metatype gets swept as a term holding a
  ;; type while the clash its arrival creates goes unreached.  The memberships sit in
  ;; sibling contexts, so CxD is the only context that sees the pair and the vantage
  ;; that weighs it.
  (tu/with-terms [CxA CxB CxD animal_species dog_t cat_t Rex]
    (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list animal_species dog_t) 'CxUniverse)
    (v/assert kb (list animal_species cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) CxA)
    (v/assert kb (list cat_t Rex) CxB)
    (is (empty? (v/contradictions kb)) "the metatype separates nothing yet")
    (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs))
          "the members become pairwise disjoint, and the term holding two of them clashes")
      (is (= #{(list dog_t Rex) (list cat_t Rex)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb)) "decided at CxD, not reported")))

(tu/deftest-kb the-decided-pairs-are-the-jointly-visible-pairs
  ;; `exposed-clashes` walks every stored sentex and names each term holding two
  ;; believed memberships a context sees as separated, so it is an independent oracle for
  ;; the candidate index, and the two must agree clash for clash.  Three separated pairs
  ;; over terms that mostly hold one side only.  The memberships sit in sibling contexts,
  ;; so only the context below both sees a pair and decides it.
  (tu/with-terms [CxA CxB CxD a1_t a2_t b1_t b2_t Pip Quo]
    (doseq [t [a1_t a2_t b1_t b2_t]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (dotimes [_ 12] (v/assert kb (list a1_t (tu/tmp-ind "Filler")) CxA))
    (dotimes [_ 12] (v/assert kb (list b2_t (tu/tmp-ind "Filler")) CxA))
    (v/assert kb (list a1_t Pip) CxA)
    (v/assert kb (list b1_t Pip) CxB)
    (v/assert kb (list a2_t Quo) CxA)
    (v/assert kb (list b2_t Quo) CxB)
    (v/clear-violations! kb)
    (v/assert kb (list 'disjoint a1_t b1_t) 'CxUniverse)
    (v/assert kb (list 'disjoint a2_t b2_t) 'CxUniverse)
    (v/assert kb (list 'disjoint a1_t b2_t) 'CxUniverse)
    (let [decided (into #{} (map (fn [c] (into #{} (map (juxt :sentence :context))
                                               (:sides c))))
                        (v/contradictions kb))
          truth   (into #{} (map (fn [d] (into #{} (map (fn [[ty cx]] [(list ty (:term d)) cx]))
                                               (:held d))))
                        (map :detail (v/exposed-clashes kb)))]
      (is (= #{Pip Quo} (into #{} (map (comp :term :detail)) (v/exposed-clashes kb)))
          "two terms hold a separated pair; the 24 fillers hold one side only")
      (is (= truth decided)
          "and the readers decide exactly what the complete question finds")
      (is (empty? (v/violations kb))
          "every pair the oracle names has a vantage, so none is left to report"))))

(tu/deftest-kb a-separation-naming-a-non-symbol-convicts-nobody
  ;; A reified NAT argument — OpenCyc declares thousands of separations against terms like
  ;; `(AbnormalFn chromosome)` — has an empty spec closure, so no membership sits below
  ;; it and no clash sits above it.
  (tu/with-terms [CxC real_t Pip]
    (v/assert kb (list 'genl real_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
    (dotimes [_ 20] (v/assert kb (list real_t (tu/tmp-ind "Filler")) CxC))
    (v/assert kb (list real_t Pip) CxC)
    (v/assert kb (list 'disjoint (list 'SomeFn real_t) real_t) 'CxUniverse)
    (is (empty? (v/contradictions kb))
        "a compound can head no stored membership, so it is nobody's clash")))

(tu/deftest-kb a-metatype-member-arriving-last-decides-the-holder-of-two-members
  ;; The member route, `(M T)` arriving: T's instances can now clash with instances of
  ;; M's *other* members, and twenty terms below dog_t hold nothing else of M.
  (tu/with-terms [CxA CxB CxD animal_species dog_t cat_t Rex]
    (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
    (v/assert kb (list animal_species cat_t) 'CxUniverse)
    (dotimes [_ 20] (v/assert kb (list dog_t (tu/tmp-ind "Pup")) CxA))
    (v/assert kb (list dog_t Rex) CxA)
    (v/assert kb (list cat_t Rex) CxB)
    (v/assert kb (list animal_species dog_t) 'CxUniverse)
    (is (= #{(list dog_t Rex) (list cat_t Rex)}
           (into #{} (mapcat #(map :sentence (:sides %))) (v/contradictions kb)))
        "only the term that also holds a second member clashes")))

(tu/deftest-kb a-functional-declaration-arriving-last-decides-its-pair-among-many-tuples
  ;; A tuple mark offers its predicate's stored tuples to the candidates a reader decides
  ;; (`special/offer-marked-existing`), so the pair written after twenty unrelated tuples
  ;; is decided.
  (tu/with-terms [ownerOf Last]
    (v/assert kb (list 'binary_predicate ownerOf) 'CxUniverse)
    (dotimes [_ 20]
      (v/assert kb (list ownerOf (tu/tmp-ind "Thing") (tu/tmp-ind "Who")) 'CxUniverse))
    (v/assert kb (list ownerOf Last 1) 'CxUniverse)
    (v/assert kb (list ownerOf Last 2) 'CxUniverse)
    (v/assert kb (list 'functional ownerOf) 'CxUniverse)
    (is (= [:functional] (mapv :kind (v/contradictions kb))))))

(deftest a-declaration-first-or-last-leaves-the-same-belief-under-retraction
  ;; Six terms with a known-true and a default membership each.  Declared first, each
  ;; membership's arrival meets the separation; declared last, the separation meets the
  ;; six terms.  In the second row two terms' known-true membership is retracted after,
  ;; which gives their default membership back.
  (let [run (fn [order retract]
              (tu/with-kb [k]
                (tu/with-terms [one_t two_t A0 A1 A2 A3 A4 A5]
                  (let [xs     [A0 A1 A2 A3 A4 A5]
                        ts     {1 one_t 2 two_t}
                        handle #(v/handle-of k (list (ts %2) (xs %1)) 'CxUniverse)]
                    (v/assert k (list 'genl one_t 'thing) 'CxUniverse)
                    (v/assert k (list 'genl two_t 'thing) 'CxUniverse)
                    (when (= :declaration-first order)
                      (v/assert k (list 'disjoint one_t two_t) 'CxUniverse))
                    (doseq [x xs]
                      (v/assert k (list one_t x) 'CxUniverse {:strength :monotonic})
                      (v/assert k (list two_t x) 'CxUniverse))
                    (when (= :declaration-last order)
                      (v/assert k (list 'disjoint one_t two_t) 'CxUniverse))
                    (doseq [i retract] (v/retract! k (handle i 1)))
                    (into (sorted-set)
                          (for [[n t] ts
                                {[_ x] :sentence} (v/sentexes-matching
                                                   k (list t '?x) 'CxUniverse)]
                            [(.indexOf ^java.util.List xs x) n]))))))]
    (doseq [retract [[] [1 4]]]
      (testing (str "retracting " retract)
        (is (= (run :declaration-first retract) (run :declaration-last retract)))))))

(deftest a-cover-declared-first-or-last-refutes-every-term
  ;; Four terms each hold the whole and deny both parts.
  (let [run (fn [order]
              (tu/with-kb [k]
                (tu/with-terms [animal dog cat R0 R1 R2 R3]
                  (let [decl #(v/assert k (list 'covering animal dog cat) 'CxUniverse)]
                    (when (= :declaration-first order) (decl))
                    (doseq [r [R0 R1 R2 R3]]
                      (v/assert k (list animal r) 'CxUniverse)
                      (v/assert k (list 'not (list dog r)) 'CxUniverse)
                      (v/assert k (list 'not (list cat r)) 'CxUniverse))
                    (when (= :declaration-last order) (decl))
                    (dotimes [_ 4] (v/assert k (list 'thing (tu/tmp-ind "Unrelated")) 'CxUniverse))
                    (count (filter #(and (= :cover (:kind %))
                                         (some #{animal} (flatten (:sentence %))))
                                   (v/contradictions k)))))))]
    (is (= 4 (run :declaration-first) (run :declaration-last)))))

;; ---- the other two kinds, across the same edge ---------------------------
;;
;; A `functional` slot filled either side of a `genlCx` edge, and an `asymmetric` claim
;; written across one, are weighed at the vantage exactly as a disjointness clash is.
;; Same lattice as the disjointness cases above: two
;; siblings neither of which sees the other, and a joint viewer below both that sees the
;; whole pair and decides it.
;;
;; Every pair below is two `:default` claims, so the vantage cannot rank them and the
;; answer is a dilemma: both claims stand and `contradictions` names the pair.

(defn- decided-pairs
  "The settle's dilemmas as `#{[sentence context] …}` sets — a reading that survives the
  arrival order the handles record."
  [kb]
  (into #{} (map (fn [c] (into #{} (map (juxt :sentence :context)) (:sides c))))
        (v/contradictions kb)))

(defn- split-lattice!
  "The declaration and the two siblings with a joint viewer below both — everything but
  the two clashing claims, so a test can choose the order those arrive in."
  [kb {:keys [a b w decl pred]}]
  (v/assert kb (list decl pred) 'CxUniverse)
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx w a) 'CxUniverse)
  (v/assert kb (list 'genlCx w b) 'CxUniverse))

(defn- split-pair!
  "Two claims of one predicate, one in each sibling, with a joint viewer below both —
  admissible to both writers, since neither sibling sees the other."
  [kb {:keys [a b one two] :as spec}]
  (split-lattice! kb spec)
  (v/assert kb one a)
  (v/assert kb two b))

(tu/deftest-kb a-functional-slot-filled-across-an-edge-is-decided-at-the-viewer
  ;; The hole this closes.  Neither writer can see the other's filler, so neither is
  ;; refused; the joint viewer CxW sees both, and CxW is the vantage that weighs them.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (split-pair! kb {:a CxA :b CxB :w CxW :decl 'functional
                       :pred birthYear :one one :two two})
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs)) "one dilemma for the pair, not one per side")
        (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb))))
      (testing "two defaults cannot be ranked, so both claims stand"
        (is (seq (v/sentexes-matching kb one CxA)))
        (is (seq (v/sentexes-matching kb two CxB)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
            "decided is not exposed")))))

(tu/deftest-kb an-asymmetric-claim-written-across-an-edge-is-decided-at-the-viewer
  (tu/with-terms [CxA CxB CxW typeLargerThan Rex Pip]
    (let [one (list typeLargerThan Rex Pip)
          two (list typeLargerThan Pip Rex)]
      (split-pair! kb {:a CxA :b CxB :w CxW :decl 'asymmetric
                       :pred typeLargerThan :one one :two two})
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb))))
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (testing "two defaults cannot be ranked, so both claims stand"
        (is (seq (v/sentexes-matching kb one CxA)))
        (is (seq (v/sentexes-matching kb two CxB)))
        (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb))))))))

(deftest the-decision-is-the-same-in-either-arrival-order
  ;; Both halves can sit in one settle's region and each convicts the other, so a pair
  ;; keyed on the walked side would be weighed twice — or read differently — depending on
  ;; which arrived last.  **The two arms share one term set and run over two cleared
  ;; KBs**, so the dilemmas are comparable as values: an arm-local `with-terms` would
  ;; make them differ for a reason that has nothing to do with order.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)
          spec {:a CxA :b CxB :w CxW :decl 'functional :pred birthYear}
          run  (fn [first-half second-half]
                 (tu/with-cleared-kb [k tu/fresh]
                   (split-lattice! k spec)
                   (v/assert k first-half (if (= first-half one) CxA CxB))
                   (v/assert k second-half (if (= second-half one) CxA CxB))
                   [(mapv :kind (v/contradictions k)) (decided-pairs k)]))
          a (run one two)
          b (run two one)]
      (is (= [[:functional] #{#{[one CxA] [two CxB]}}] a)
          "one dilemma for the pair, whichever half arrived last")
      (is (= a b) "and the identical reading, contexts included"))))

(tu/deftest-kb every-context-that-sees-the-pair-decides-it-not-just-the-convicting-one
  ;; A pair's vantages are a property of the pair, so a second joint viewer is one too.
  ;; Keeping only the vantage that happened to convict would make belief a function of
  ;; which half the region held — the defeat would reach one viewer and not the other.
  ;; The monotonic half is what makes the verdict observable: two defaults tie.
  (tu/with-terms [CxA CxB CxW CxV birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (split-lattice! kb {:a CxA :b CxB :w CxW
                          :decl 'functional :pred birthYear})
      ;; a second, incomparable viewer of both siblings, in place before the facts
      (v/assert kb (list 'genlCx CxV CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxV CxB) 'CxUniverse)
      (v/assert kb one CxA {:strength :monotonic})
      (v/assert kb two CxB)
      (testing "the loser is defeated at both joint viewers"
        (is (not (v/ask? kb two CxW)))
        (is (not (v/ask? kb two CxV)))
        (is (v/ask? kb one CxW))
        (is (v/ask? kb one CxV)))
      (testing "and stands in its own context, which sees no pair"
        (is (v/ask? kb two CxB))))))

(tu/deftest-kb the-vantage-weighs-the-pair-and-the-ledger-does-not-file-it
  ;; No pass may add a ledger entry for a pair a vantage decides, or the ledger and
  ;; `contradictions` both claim one clash.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (split-pair! kb {:a CxA :b CxB :w CxW :decl 'functional
                     :pred birthYear
                     :one (list birthYear Tom 1970) :two (list birthYear Tom 1980)})
    (is (= [:functional] (mapv :kind (v/contradictions kb))) "the vantage decides it")
    (is (empty? (filter (comp #{:functional :asymmetric} :violation) (v/violations kb)))
        "and the ledger does not also claim it")))

(tu/deftest-kb a-pair-both-writers-could-see-is-stored-and-weighed-not-filed
  ;; Written in one context, the entry point stores the second fact and the settle weighs
  ;; the pair where it was written — nothing reaches the ledger.
  (tu/with-terms [birthYear Tom]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)
    (v/assert kb (list birthYear Tom 1970) 'CxUniverse)
    (is (some? (v/assert kb (list birthYear Tom 1980) 'CxUniverse)))
    (is (= [:functional] (mapv :kind (v/contradictions kb))))
    (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))

(deftest a-self-tuple-in-two-contexts-forms-no-pair-in-either-arrival-order
  ;; The converse of `(P a a)` is itself, so the two copies state one sentence, and an
  ;; `asymmetric` mark convicts no self tuple (docs/reference.md, the `asymmetric`
  ;; family).  Two cleared KBs over one term set, so the readings compare as values.
  (tu/with-terms [CxA CxB CxW beats Rex]
    (let [claim (list beats Rex Rex)
          run   (fn [c1 c2]
                  (tu/with-cleared-kb [k tu/fresh]
                    (split-lattice! k {:a CxA :b CxB :w CxW
                                       :decl 'asymmetric :pred beats})
                    (v/assert k claim c1)
                    (v/assert k claim c2)
                    [(mapv :kind (v/contradictions k)) (decided-pairs k)]))]
      (is (= [[] #{}] (run CxA CxB)))
      (is (= (run CxA CxB) (run CxB CxA))))))

(tu/deftest-kb a-predicate-carrying-both-properties-reads-both-postings
  ;; A functional partner shares argument 1 and an asymmetric one holds it in argument 2,
  ;; so a predicate declared both keeps a determinant and a converse candidate, and
  ;; dropping either loses a pair.
  (tu/with-terms [CxA CxB CxW ranks Tom Pip Vic]
    (split-lattice! kb {:a CxA :b CxB :w CxW
                        :decl 'functional :pred ranks})
    (v/assert kb (list 'asymmetric ranks) 'CxUniverse)
    (testing "the functional partner, which shares argument 1"
      (v/assert kb (list ranks Tom 1) CxA)
      (v/assert kb (list ranks Tom 2) CxB)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))
    (testing "and the asymmetric partner, whose argument 1 is the other side's argument 2"
      ;; fresh subjects: a converse pair on Tom would also be a second filler of Tom's
      ;; functional slot, and the entry point would refuse it before any of this ran
      (v/assert kb (list ranks Pip Vic) CxA)
      (v/assert kb (list ranks Vic Pip) CxB)
      (is (contains? (set (map :kind (v/contradictions kb))) :asymmetric)))))

(tu/deftest-kb an-edge-arriving-after-both-facts-still-decides-the-pair
  ;; The arrival order the region alone cannot see: visibility itself moves, so a pair
  ;; whose halves are already stored and already believed becomes jointly visible without
  ;; either half being relabelled. Neither is in the moved region, so the `genlCx`
  ;; edge moves the reader's view, and the reader reads the pair off the candidate index
  ;; (`chain/place-memberships!`).
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (v/assert kb (list 'functional birthYear) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (is (empty? (v/contradictions kb)) "nothing sees the pair yet")
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "seeing one side is not seeing the clash")
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))
          "the edge that completes the view weighs the pair")
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
          "decided is not exposed"))))

(deftest the-edges-may-arrive-in-either-position-and-the-decision-is-the-same
  ;; The whole point of the trigger: facts-then-edges and edges-then-facts are the same
  ;; knowledge, so they are one dilemma either way. Two cleared KBs over one term set, so
  ;; the readings compare as values.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one   (list birthYear Tom 1970)
          two   (list birthYear Tom 1980)
          decl! (fn [k]
                  (v/assert k (list 'functional birthYear) 'CxUniverse)
                  (v/assert k (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                  (v/assert k (list 'genlCx CxB 'CxUniverse) 'CxUniverse))
          edges! (fn [k]
                   (v/assert k (list 'genlCx CxW CxA) 'CxUniverse)
                   (v/assert k (list 'genlCx CxW CxB) 'CxUniverse))
          facts! (fn [k] (v/assert k one CxA) (v/assert k two CxB))
          run   (fn [first! second!]
                  (tu/with-cleared-kb [k tu/fresh]
                    (decl! k) (first! k) (second! k)
                    [(mapv :kind (v/contradictions k)) (decided-pairs k)]))
          edges-last  (run facts! edges!)
          edges-first (run edges! facts!)]
      (is (= [[:functional] #{#{[one CxA] [two CxB]}}] edges-first))
      (is (= edges-first edges-last)
          "the identical reading whichever half of the setup arrived last"))))

;; ---- the edge reveals the MARK, not a second fact -----------------------
;;
;; The cases above split the clashing pair across two siblings and bring the two halves
;; into one sight.  The other shape is a pair already **together** in one context `w` and
;; a `(genlCx w c)` edge that reveals the tuple mark standing in `c`: `w` gains sight of
;; the declaration, not of a second fact.  The candidate index holds the tuples whatever
;; their contexts, so the reader `w` decides the pair once it reads the mark.  Each of
;; the four tuple marks has a witness of this shape below: `functional` and `asymmetric`
;; at arity 2, `anti_transitive` as a three-member triple, and `functionalInArg` at the
;; final position of a ternary.

(tu/deftest-kb a-genlCx-edge-revealing-a-functional-mark-decides-a-co-located-pair
  (tu/with-terms [CxU CxD birthYear Tom]
    (let [one (list birthYear Tom 1970) two (list birthYear Tom 1980)]
      (v/assert kb (list 'functional birthYear) CxD)      ; the mark, invisible to CxU
      (v/assert kb one CxU)
      (v/assert kb two CxU)
      (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
          "CxU cannot see the mark yet, so nothing clashes")
      (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)    ; the edge, arriving last
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs)) "the edge reveals the mark and the co-located pair is weighed")
        (is (= #{one two} (set (map :sentence (:sides (first cs)))))))
      (testing "an equal-strength pair is a dilemma: both stand, and nothing is filed as exposed"
        (is (seq (v/sentexes-matching kb one CxU)))
        (is (seq (v/sentexes-matching kb two CxU)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))))

(tu/deftest-kb a-genlCx-edge-revealing-an-anti-transitive-mark-decides-a-co-located-triple
  ;; the three-member nogood, the candidate shape the pairwise reach would miss
  (tu/with-terms [CxU CxD directParentOf Aa Bb Cc]
    (v/assert kb (list directParentOf Aa Bb) CxU)
    (v/assert kb (list directParentOf Bb Cc) CxU)
    (v/assert kb (list directParentOf Aa Cc) CxU)          ; the closing step, beside the chain
    (v/assert kb (list 'anti_transitive directParentOf) CxD)
    (is (empty? (filter (comp #{:anti-transitive} :violation) (v/violations kb)))
        "CxU cannot see the mark yet")
    (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:anti-transitive] (mapv :kind cs))
          "the edge reveals the mark and the chain-plus-step triple is weighed")
      (is (= 3 (count (:sides (first cs))))))
    (testing "an equal-strength triple is a dilemma: all three stand, nothing filed as exposed"
      (is (every? #(seq (v/sentexes-matching kb % CxU))
                  [(list directParentOf Aa Bb) (list directParentOf Bb Cc)
                   (list directParentOf Aa Cc)]))
      (is (empty? (filter (comp #{:anti-transitive} :violation) (v/violations kb)))))))

(tu/deftest-kb a-genlCx-edge-revealing-an-asymmetric-mark-decides-a-co-located-pair
  ;; the second arity-2 tuple mark, beside `functional`: the reversed-argument
  ;; clash, both halves together in CxU, the mark in CxD, the edge last
  (tu/with-terms [CxU CxD beats Ann Bob]
    (let [one (list beats Ann Bob) two (list beats Bob Ann)]
      (v/assert kb (list 'asymmetric beats) CxD)          ; the mark, invisible to CxU
      (v/assert kb one CxU)
      (v/assert kb two CxU)
      (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb)))
          "CxU cannot see the mark yet, so nothing clashes")
      (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)    ; the edge, arriving last
      (let [cs (v/contradictions kb)]
        (is (= [:asymmetric] (mapv :kind cs)) "the edge reveals the mark and the co-located pair is weighed")
        (is (= #{one two} (set (map :sentence (:sides (first cs)))))))
      (testing "an equal-strength pair is a dilemma: both stand, and nothing is filed as exposed"
        (is (seq (v/sentexes-matching kb one CxU)))
        (is (seq (v/sentexes-matching kb two CxU)))
        (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb))))))))

(tu/deftest-kb a-genlCx-edge-revealing-a-functional-in-arg-mark-decides-a-co-located-composite
  ;; `functionalInArg` at its final position: `(functionalInArg P 3)` on a ternary, two rows sharing the (arg1,arg2) determinant with unmergeable
  ;; fillers at the constrained position, together in CxU with the mark in CxD.  An
  ;; unmergeable pair at the determined slot reports a `:functional` clash instead of
  ;; merging, so this reads the same violation `functional` does.
  (tu/with-terms [CxU CxD pScore TeamA Y2020]
    (let [one (list pScore TeamA Y2020 10) two (list pScore TeamA Y2020 20)]
      (v/assert kb (list 'functionalInArg pScore 3) CxD)  ; the mark, invisible to CxU
      (v/assert kb one CxU)
      (v/assert kb two CxU)
      (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
          "CxU cannot see the mark yet, so nothing clashes")
      (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)    ; the edge, arriving last
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs))
            "the edge reveals the mark and the co-located composite pair is weighed")
        (is (= #{one two} (set (map :sentence (:sides (first cs)))))))
      (testing "an equal-strength pair is a dilemma: both stand, and nothing is filed as exposed"
        (is (seq (v/sentexes-matching kb one CxU)))
        (is (seq (v/sentexes-matching kb two CxU)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))))

(deftest a-revealed-mark-defeats-the-co-located-loser-in-every-order
  ;; The belief witness: the deciding path weighs the pair, so the revealed mark must
  ;; defeat the :default loser against a :monotonic rival — and the answer may not turn on
  ;; which of {mark, facts, edge} arrived last.
  ;; `functional` and `asymmetric` both decide the clash by defeat and run here together;
  ;; `functionalInArg` decides by merging the fillers, a different outcome, so it is pinned
  ;; by its own witness above rather than folded into this defeat test.
  (tu/with-terms [CxU CxD birthYear Tom beats Ann Bob]
    (doseq [[mark mono loser]
            [[(list 'functional birthYear) (list birthYear Tom 1970) (list birthYear Tom 1980)]
             [(list 'asymmetric beats)     (list beats Ann Bob)      (list beats Bob Ann)]]]
      (let [mark! #(v/assert % mark CxD)
            edge! #(v/assert % (list 'genlCx CxU CxD) 'CxUniverse)
            m!    #(v/assert % mono CxU {:strength :monotonic})  ; known-true, stands
            l!    #(v/assert % loser CxU {:strength :default})   ; defeasible, must lose
            ;; the loser is stored in every order and defeated by the settle
            belief (fn [order]
                     (tu/with-neutral-kb [k #(v/open-kb (tu/scratch-space))]
                       (doseq [step order] (step k))
                       [(boolean (seq (v/sentexes-matching k mono CxU)))
                        (boolean (seq (v/sentexes-matching k loser CxU)))]))]
        (doseq [[label order] [[:edge-last  [mark! m! l! edge!]]
                               [:mark-last  [edge! m! l! mark!]]
                               [:facts-last [mark! edge! m! l!]]]]
          (is (= [true false] (belief order))
              (str mark " / " (name label)
                   ": the monotonic fact stands and the default loser does not")))))))

(tu/deftest-kb siblings-with-no-joint-viewer-report-nothing
  ;; The ∃-vantage reading, for these two kinds: the claims coexist and no single
  ;; context sees both, so there is nobody the pair is a clash for.
  (tu/with-terms [CxA CxB birthYear Tom]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list birthYear Tom 1970) CxA)
    (v/assert kb (list birthYear Tom 1980) CxB)
    (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))

;; ---- and the edge that carries the mark rather than the view -------------
;;
;; A mark is read up the predicate hierarchy (`tax/props-over`), so a pair of `fatherOf`
;; facts either side of a visibility edge is a `(functional parentOf)` clash — and the
;; region walk finds it by itself, because `declared?` asks the same descending question.
;; What the region cannot supply is the pair whose `(genl fatherOf parentOf)` edge arrives
;; **last**: a predicate edge relabels neither half, so neither half is in the region, and
;; the edge is a binary sentence whose own functor carries no mark, so it is a candidate
;; for nothing.  Only naming it a trigger reaches them.  Same shape as the `genlCx` case
;; above and the same answer — the disjointness pass has the analogous arm, over the
;; memberships an edge newly separates.

(tu/deftest-kb a-genl-edge-arriving-after-both-facts-carries-the-mark-down
  (tu/with-terms [CxA CxB CxW birthYear measureOf Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (is (empty? (v/contradictions kb))
          "nothing marked sits above birthYear yet, so the two are unrelated fillers")
      (v/assert kb (list 'genl birthYear measureOf) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))
          "the edge that carries the mark down brings the pair to its vantage")
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (testing "two defaults cannot be ranked, so both claims stand"
        (is (seq (v/sentexes-matching kb one CxA)))
        (is (seq (v/sentexes-matching kb two CxB)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))))

(tu/deftest-kb an-asymmetric-mark-descends-to-a-claim-written-across-an-edge
  (tu/with-terms [CxA CxB CxW muchLargerThan typeLargerThan Rex Pip]
    (let [one (list muchLargerThan Rex Pip)
          two (list muchLargerThan Pip Rex)]
      (v/assert kb (list 'asymmetric typeLargerThan) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (is (empty? (v/contradictions kb)))
      (v/assert kb (list 'genl muchLargerThan typeLargerThan) 'CxUniverse)
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb))))
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb)))))))

(deftest the-mark-may-descend-before-or-after-the-facts-and-the-decision-is-the-same
  ;; The control beside the case that was silent, and the reason it is worth pinning: with
  ;; the edge already in place the region walk found the pair by itself, since `declared?`
  ;; reads the mark up the hierarchy — so that arm passed throughout and the asymmetry
  ;; between the two was invisible from either side alone.  Two cleared KBs over one term
  ;; set, so the entries compare as values.
  (tu/with-terms [CxA CxB CxW birthYear measureOf Tom]
    (let [one    (list birthYear Tom 1970)
          two    (list birthYear Tom 1980)
          decl!  (fn [k]
                   (v/assert k (list 'functional measureOf) 'CxUniverse)
                   (v/assert k (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                   (v/assert k (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
                   (v/assert k (list 'genlCx CxW CxA) 'CxUniverse)
                   (v/assert k (list 'genlCx CxW CxB) 'CxUniverse))
          edge!  (fn [k] (v/assert k (list 'genl birthYear measureOf) 'CxUniverse))
          facts! (fn [k] (v/assert k one CxA) (v/assert k two CxB))
          run    (fn [first! second!]
                   (tu/with-cleared-kb [k tu/fresh]
                     (decl! k) (first! k) (second! k)
                     [(mapv :kind (v/contradictions k)) (decided-pairs k)]))
          edge-last  (run facts! edge!)
          edge-first (run edge! facts!)]
      (is (= [[:functional] #{#{[one CxA] [two CxB]}}] edge-first))
      (is (= edge-first edge-last)
          "the identical reading whichever of the mark's descent and the facts came last"))))

(tu/deftest-kb a-genl-edge-under-no-marked-predicate-is-not-a-trigger
  ;; `genl` is the commonest edge in an ontology, so an edge with no mark above it must
  ;; cost the pass a `props-over` read and no sweep at all.  Read off the budget, which is
  ;; the one observable: an edge that swept would spend it on the six facts below it and
  ;; file a cut notice saying so.
  (tu/with-terms [CxSrc birthYear plainOf otherOf]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)   ; so the pass runs at all
    (v/assert kb (list 'genlCx CxSrc 'CxUniverse) 'CxUniverse)
    (doseq [i (range 6)]
      (v/assert kb (list plainOf (tu/tmp-ind "Subj") (+ 1900 i)) CxSrc))
    (v/clear-violations! kb)
    (binding [tax/*exposure-instance-budget* 2]
      (v/assert kb (list 'genl plainOf otherOf) 'CxUniverse))
    (is (empty? (v/violations kb))
        "nothing marked above either end, so nothing was enumerated and nothing was cut")))

(defn- orderings
  "Every arrival order of `xs`.  The case below runs over all of them rather than over a
  hand-picked few: which sentence is last is exactly what decides whether this policy
  reports, so a subset would be choosing the answer."
  [xs]
  (if (< (count xs) 2)
    [(vec xs)]
    (for [x xs, tail (orderings (remove #{x} xs))]
      (into [x] tail))))

(deftest every-arrival-order-of-a-cross-context-clash-decides-it-once
  ;; **All three ingredients are triggers, so all six orders decide.**  A pair split
  ;; across a visibility edge needs the mark, the `genl` edge that carries it down to the
  ;; predicate the facts are written under, and the two claims themselves — and whichever
  ;; of the three lands last is what the sweep has to reach back from.  The mark's own
  ;; sentence is a trigger for exactly that reason: the two facts it convicts move nothing
  ;; when it arrives, so a pass reading only the region would weigh this in five orders
  ;; out of six and let the mark decide the sixth.
  ;;
  ;; **Once**, not once per member and not once per route.  Both facts and the edge can
  ;; be reached in one settle, and the nogood is keyed on the handle set to collapse them,
  ;; so a count above one is a reading that depends on how the
  ;; clash was found rather than on what it is.
  (tu/with-terms [CxA CxB CxW birthYear measureOf Tom]
    (doseq [order (orderings [:declaration :edge :facts])]
      (tu/with-cleared-kb [k tu/fresh]
        (v/assert k (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert k (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
        (v/assert k (list 'genlCx CxW CxA) 'CxUniverse)
        (v/assert k (list 'genlCx CxW CxB) 'CxUniverse)
        (let [step {:declaration #(v/assert k (list 'functional measureOf) 'CxUniverse)
                    :edge        #(v/assert k (list 'genl birthYear measureOf) 'CxUniverse)
                    :facts       #(do (v/assert k (list birthYear Tom 1970) CxA)
                                      (v/assert k (list birthYear Tom 1980) CxB))}]
          (doseq [s order] ((step s)))
          (is (= [:functional] (mapv :kind (v/contradictions k)))
              (str "decided once under " (pr-str order)))
          (is (empty? (filter (comp #{:functional} :violation) (v/violations k)))
              (str "and not also reported under " (pr-str order))))))))

(tu/deftest-kb a-negative-exposure-budget-is-a-cut-not-a-crash
  ;; `*exposure-instance-budget*` is a public dynamic var; a negative value means
  ;; "nothing more", which is a cut of everything — not a `(subvec … 0 -1)` thrown out
  ;; of the merge sweep a `genlCx` edge runs.
  (tu/with-terms [CxA CxB CxW left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'CxUniverse)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (let [h (binding [tax/*exposure-instance-budget* -1]
              (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse))]
      (is (nat-int? h)
          "the settle reading a negative budget completes and the edge gets a handle"))))

