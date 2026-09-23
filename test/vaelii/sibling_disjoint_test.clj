;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sibling-disjoint-test
  "sibling_disjoint — a collection's genl-specializations are pairwise disjoint unless
  one is a genl of the other — and the contradiction detection it drives, through the
  same JTMS/ASP path as disjoint."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- assert-outcome
  "`:ok`, or the `:type` of the refusal — so a case is indistinguishable from a value rather than the
  presence or absence of a throw."
  [kb sentence context]
  (try (v/assert kb sentence context) :ok
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb siblings-under-a-marked-parent-become-disjoint
  (let [collection (tu/tmp-type) dog (tu/tmp-type) cat (tu/tmp-type)
        muffet (tu/tmp-ind) whiskers (tu/tmp-ind)]
    (v/assert kb (list 'genl dog collection) 'CxUniverse)
    (v/assert kb (list 'genl cat collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list dog muffet) 'CxUniverse)
    (testing "two specializations of the marked parent are disjoint, no pair asserted"
      (is (v/disjoint? kb dog cat)))
    (testing "a membership that violates it is refused where written"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat muffet) 'CxUniverse))))
    (testing "an individual holding only one is unaffected"
      (is (v/assert kb (list cat whiskers) 'CxUniverse)))))

(tu/deftest-kb a-specialization-is-not-disjoint-from-its-supertype
  ;; the genl-relatedness exception: breed and sub_breed are both specializations of the
  ;; marked collection, but sub_breed is a subtype of breed, so the mark must not separate
  ;; them — a poodle is not disjoint from dog
  (let [collection (tu/tmp-type) breed (tu/tmp-type) sub_breed (tu/tmp-type)
        rex (tu/tmp-ind)]
    (v/assert kb (list 'genl breed collection) 'CxUniverse)
    (v/assert kb (list 'genl sub_breed breed) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (testing "a subtype is not disjoint from its own supertype"
      (is (not (v/disjoint? kb sub_breed breed)))
      (is (not (v/disjoint? kb breed sub_breed))))
    (testing "so one term can hold both — the mark refuses nothing here"
      (v/assert kb (list breed rex) 'CxUniverse)
      (is (v/assert kb (list sub_breed rex) 'CxUniverse)))))

(tu/deftest-kb sibling-disjointness-is-inherited-through-genl
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type)
        sub_a (tu/tmp-type) sub_b (tu/tmp-type) x (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'genl sub_a a) 'CxUniverse)
    (v/assert kb (list 'genl sub_b b) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (testing "subtypes of separated siblings are themselves disjoint"
      (is (v/disjoint? kb sub_a sub_b)))
    (testing "and a conflicting membership among the subtypes is refused"
      (v/assert kb (list sub_a x) 'CxUniverse)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list sub_b x) 'CxUniverse))))))

(deftest the-mark-reaches-back-over-memberships-stored-before-it
  ;; Order independence, under the arbitrating policy (the one that lets a declaration
  ;; reach back — the refusing default handles the reverse order at the entry point instead).
  ;; With the mark asserted last, both memberships are stored and believed before
  ;; anything separates them, so the settle's retroactive sweep — not the entry point — is what
  ;; must convict the pair the mark newly separates.  A default/default clash is a
  ;; represented dilemma.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [collection a b Muffet]
        (v/assert kb (list 'genl a collection) 'CxUniverse)
        (v/assert kb (list 'genl b collection) 'CxUniverse)
        (v/assert kb (list a Muffet) 'CxUniverse)
        (v/assert kb (list b Muffet) 'CxUniverse)
        (testing "before the mark, nothing separates them and nothing is wrong"
          (is (not (v/disjoint? kb a b)))
          (is (empty? (v/contradictions kb))))
        (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
        (testing "the mark arriving last separates the pair"
          (is (v/disjoint? kb a b)))
        (testing "and the retroactive sweep convicts the pre-existing pair as a dilemma"
          (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))))))

(tu/deftest-kb retracting-the-mark-releases-every-pair-it-separated
  ;; belief-following: the mark is one supporter of the whole induced clique, so dropping
  ;; it stops constraining exactly as a defeated (disjoint a b) would
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type) x (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list a x) 'CxUniverse)
    (is (v/disjoint? kb a b))
    (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list b x) 'CxUniverse)))
    (testing "retracting the one mark releases the separation and admits the membership"
      (v/retract! kb (v/handle-of kb (list 'sibling_disjoint collection) 'CxUniverse))
      (is (not (v/disjoint? kb a b)))
      (is (v/assert kb (list b x) 'CxUniverse)))))

(tu/deftest-kb the-mark-is-ill-formed-over-an-individual
  (let [fido (tu/tmp-ind)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'sibling_disjoint fido) 'CxUniverse)))))

;;; ── context scoping: a general context may hold what a specific one forbids ──

(tu/deftest-kb a-general-context-may-hold-what-a-specific-siblingdisjoint-forbids
  ;; the mark lives in a specific context; a sibling above it that cannot see the mark is
  ;; not constrained, and the clash a general write creates for the specific context is
  ;; weighed at CxA — the only context that sees the mark and both memberships — rather
  ;; than refused at the general entry point
  ;;
  ;;   CxUniverse
  ;;     └─ CxC        (t2 Pip) default, written second
  ;;          └─ CxA   (sibling_disjoint col), (t1 Pip) default   — the deciding vantage
  (tu/with-terms [CxA CxC col t1 t2 Pip]
    (v/assert kb (list 'genl t1 col) 'CxUniverse)
    (v/assert kb (list 'genl t2 col) 'CxUniverse)
    (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint col) CxA)      ; the mark in the specific context only
    (v/assert kb (list t1 Pip) CxA)

    (testing "the context that can see the mark separates the pair"
      (is (v/disjoint? kb t1 t2 CxA)))
    (testing "the general context cannot see the mark, so it does not"
      (is (not (v/disjoint? kb t1 t2 CxC)))
      (is (not (v/sees? kb CxC CxA))))
    (testing "the unscoped read still reports the separation the KB holds somewhere"
      (is (v/disjoint? kb t1 t2)))

    (testing "so the general context, blind to the mark, admits the conflicting membership"
      (is (= :ok (assert-outcome kb (list t2 Pip) CxC))))

    (testing "while the context that wrote the mark refuses its own"
      (is (= #{t1 t2} (set (v/types-of kb Pip CxA))))
      (is (= :disjoint (assert-outcome kb (list t2 Pip) CxA))))

    (testing "the vantage decides the cross-context clash, so nothing reaches the ledger"
      (is (empty? (v/violations kb)))
      (let [cs (v/contradictions kb)]
        (is (= [:disjoint] (mapv :kind cs)))
        (is (= #{(list t1 Pip) (list t2 Pip)}
               (into #{} (map :sentence) (:sides (first cs)))))))

    (testing "two defaults are a dilemma, so belief is untouched"
      (is (empty? (v/conflicts kb)))
      (is (= #{t1 t2} (set (v/types-of kb Pip CxA)))))))

;;; ── siblingDisjointException: an escape hatch exempting one pair ──

(tu/deftest-kb an-exception-exempts-one-pair-and-only-that-pair
  ;; the exemption spares x,y while the mark still separates every other sibling —
  ;; pair-locality — and is symmetric in its two arguments
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type)
        pip (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'genl c collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (testing "before the exception every pair of specializations is disjoint"
      (is (v/disjoint? kb a b))
      (is (v/disjoint? kb a c)))
    (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
    (testing "the exempted pair no longer separates — symmetric in either order"
      (is (not (v/disjoint? kb a b)))
      (is (not (v/disjoint? kb b a))))
    (testing "pair-locality: the mark still separates the pairs it was not excused"
      (is (v/disjoint? kb a c))
      (is (v/disjoint? kb b c)))
    (testing "so one term may hold both exempted types"
      (v/assert kb (list a pip) 'CxUniverse)
      (is (v/assert kb (list b pip) 'CxUniverse)))
    (testing "but still not a non-exempted sibling"
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list c pip) 'CxUniverse))))))

(tu/deftest-kb the-exception-canonicalizes-both-orders-to-one-handle
  ;; symmetric — as CxCore declares it — so (siblingDisjointException a b) and (… b a)
  ;; sort to one canonical sentence and share a handle (the bare test KB has no CxCore, so
  ;; the mark is asserted here to stand in for it)
  (let [a (tu/tmp-type) b (tu/tmp-type)]
    (v/assert kb (list 'symmetric 'siblingDisjointException) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
    (is (= (v/handle-of kb (list 'siblingDisjointException a b) 'CxUniverse)
           (v/handle-of kb (list 'siblingDisjointException b a) 'CxUniverse)))))

(tu/deftest-kb an-exemption-does-not-leak-to-a-subtype
  ;; an exception on (a, b) must leave (sub_a, b) disjoint: each read tests the exact pair
  ;; drawn from the two genl closures, so nothing wider than the declared pair is spared
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type) sub_a (tu/tmp-type)
        x (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'genl sub_a a) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
    (testing "the declared pair overlaps"
      (is (not (v/disjoint? kb a b))))
    (testing "a subtype of one side is still disjoint from the other"
      (is (v/disjoint? kb sub_a b))
      (is (v/disjoint? kb b sub_a)))
    (testing "and a term holding sub_a cannot also hold b"
      (v/assert kb (list sub_a x) 'CxUniverse)
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list b x) 'CxUniverse))))))

(tu/deftest-kb an-exception-admits-a-membership-the-mark-would-refuse
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type) x (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list a x) 'CxUniverse)
    (testing "without the exception the second membership is refused"
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list b x) 'CxUniverse))))
    (testing "with the exception standing it is admitted"
      (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
      (is (v/assert kb (list b x) 'CxUniverse))
      (is (empty? (v/violations kb))))))

(tu/deftest-kb retracting-an-ab-initio-exception-re-arms-the-clash
  ;; the exception is present before the memberships, so both are admitted and the pair
  ;; never enters the clash set — there is no stored clash to carry forward.  Retracting
  ;; the exception must still re-arm the pair, which is the settle's :sib-exc-dirty sweep.
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type) x (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
    (v/assert kb (list a x) 'CxUniverse)
    (testing "with the exception standing both memberships coexist, nothing exposed"
      (is (v/assert kb (list b x) 'CxUniverse))
      (is (empty? (v/violations kb))))
    (v/retract! kb (v/handle-of kb (list 'siblingDisjointException a b) 'CxUniverse))
    (testing "retracting it re-separates the pair"
      (is (v/disjoint? kb a b)))
    (testing "and the re-arm sweep decides the clash the ab-initio pair now forms"
      (is (= [:disjoint] (mapv :kind (v/contradictions kb))))
      (is (empty? (v/violations kb)) "decided, so not also filed as exposed"))
    (testing "a fresh term can no longer hold both"
      (let [y (tu/tmp-ind)]
        (v/assert kb (list a y) 'CxUniverse)
        (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list b y) 'CxUniverse)))))))

(tu/deftest-kb retracting-an-exception-over-a-nat-term-does-not-wedge-writes
  ;; An exception may name a compound/NAT term — `(SomeFn someType)`, a PersistentList and
  ;; not a symbol — on either side.  Retracting it posts the departed pair to
  ;; `:sib-exc-dirty` for settle's re-arm sweep, which must order the pair by content
  ;; (`nm/compare-form`) rather than by `compare`: a list is not `Comparable`, so a bare
  ;; `sort` threw, and — escaping before the queue was cleared — every later write re-ran
  ;; the sweep off the same queue and re-threw, wedging the KB for writes until restart.
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type)
        fn-name (tu/tmp-type) nat (list fn-name a) x (tu/tmp-ind)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException nat b) 'CxUniverse)
    (testing "retracting an exception whose argument is a NAT does not throw"
      (let [h (v/handle-of kb (list 'siblingDisjointException nat b) 'CxUniverse)]
        (is (v/retract! kb h))))
    (testing "and the KB is not wedged — an unrelated later write still settles"
      (is (v/assert kb (list a x) 'CxUniverse)))))

;; Order independence under the arbitrating policy, where the pair is weighed rather than
;; refused at the entry point and a default/default clash is a represented dilemma.  Both
;; directions must land on the same belief.  Two `deftest`s, not two `with-kb` arms of one:
;; the arms share the fixture KB, so the second would read the first's contradictions.

(deftest an-exception-retracted-after-standing-ab-initio-re-arms-the-dilemma
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [collection a b Muffet]
        (v/assert kb (list 'genl a collection) 'CxUniverse)
        (v/assert kb (list 'genl b collection) 'CxUniverse)
        (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
        (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
        (v/assert kb (list a Muffet) 'CxUniverse)
        (v/assert kb (list b Muffet) 'CxUniverse)
        (testing "the exception spares the pair — no contradiction"
          (is (not (v/disjoint? kb a b)))
          (is (empty? (v/contradictions kb))))
        (v/retract! kb (v/handle-of kb (list 'siblingDisjointException a b) 'CxUniverse))
        (testing "retracting it re-arms the ab-initio pair as a dilemma"
          (is (v/disjoint? kb a b))
          (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))))))

(deftest an-exception-asserted-last-releases-a-standing-dilemma
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [collection a b Muffet]
        (v/assert kb (list 'genl a collection) 'CxUniverse)
        (v/assert kb (list 'genl b collection) 'CxUniverse)
        (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
        (v/assert kb (list a Muffet) 'CxUniverse)
        (v/assert kb (list b Muffet) 'CxUniverse)
        (testing "the mark makes the pre-existing pair a standing dilemma"
          (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))
        (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
        (testing "the exception releases it"
          (is (not (v/disjoint? kb a b)))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb the-exception-is-well-formedness-checked
  (let [a (tu/tmp-type) Fido (tu/tmp-ind)]
    (testing "an individual argument is refused on either side"
      (is (= :not-well-formed (assert-outcome kb (list 'siblingDisjointException Fido a) 'CxUniverse)))
      (is (= :not-well-formed (assert-outcome kb (list 'siblingDisjointException a Fido) 'CxUniverse))))
    (testing "the wrong arity is refused"
      ;; :naming rather than :not-well-formed — a camelCase functor at arity 1 is a unary
      ;; predicate wearing a relation's spelling, and the naming check is upstream of `wff`
      (is (= :naming (assert-outcome kb (list 'siblingDisjointException a) 'CxUniverse))))
    (testing "a self-pair is refused"
      (is (= :not-well-formed (assert-outcome kb (list 'siblingDisjointException a a) 'CxUniverse))))))
