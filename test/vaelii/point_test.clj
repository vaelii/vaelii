;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.point-test
  "The point algebra over instants (`vaelii.impl.point`): three base relations and three
  derived ones, answered by entailment over the path-consistent constraint network of
  everything asserted in a context.

  Two halves, the same shape `interval_test` uses.  The first tests the **algebra alone** —
  no KB, no context, no belief — and derives the whole composition table a second time,
  from numeric instants: lay out three points every way three points can be laid out, read
  off the three relations, and record what the outer pair may be.  The transcribed table
  and the derivation share nothing, so they can only agree by both being right.  The second
  half tests the prover over a KB, where what is really being checked is that a relation
  nobody stored comes out."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.point :as pt]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxTime vocabulary that states
;; instant relations in it, and the prover registered.  The vocabulary is an upper context;
;; the prover is opt-in, so registering it is what turns stored instant facts into a
;; network.  The algebra tests below need none of it.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxTime "upper"]])
                        (v/add-prover (pt/point-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the algebra, derived from numeric instants -------------------------

(def ^:private by-value
  "Each base relation as the comparison over two numeric instants that *defines* it.  This
  is the independent second statement of the algebra: everything below is derived from here
  and compared against the transcribed table."
  {:before (fn [a b] (< a b))
   :equal  (fn [a b] (= a b))
   :after  (fn [a b] (> a b))})

(def ^:private points
  "Enough distinct instants to realize any layout of three: a layout is a weak ordering of
  three values, so three distinct values suffice."
  [0 1 2])

(defn- holding [a b]
  (into #{} (keep (fn [[rel pred]] (when (pred a b) rel))) by-value))

(defn- relation-of [a b] (first (holding a b)))

(def ^:private derived-composition
  "The composition table computed from `by-value`: lay out three instants every way they can
  be laid out, read off the three relations, and record that r1 ∘ r2 admits r3."
  (delay
    (reduce (fn [tbl [a b c]]
              (update-in tbl [(relation-of a b) (relation-of b c)]
                         (fnil conj #{}) (relation-of a c)))
            {}
            (for [a points b points c points] [a b c]))))

(deftest the-three-relations-are-jointly-exhaustive-and-pairwise-disjoint
  (is (= 3 (count pt/all-relations)))
  (is (= pt/all-relations (set (keys by-value)))
      "the transcribed universe and the numeric definitions name the same relations")
  (testing "exactly one holds of any two instants — that is what makes a network of them a
            constraint network at all"
    (doseq [a points b points]
      (is (= 1 (count (holding a b))) (str a " and " b " stand in " (holding a b)))))
  (testing "and every one of the three is realized, so none is vacuous"
    (is (= pt/all-relations (set (for [a points b points] (relation-of a b)))))))

(deftest the-composition-table-matches-the-numeric-definitions
  (let [derived @derived-composition]
    (testing "every pair of relations composes to something, and to the same something"
      (doseq [r1 pt/all-relations r2 pt/all-relations]
        (is (= (get-in derived [r1 r2]) (get-in pt/point-composition [r1 r2]))
            (str r1 " ∘ " r2))))
    (testing "and the table has no entry the derivation does not"
      (is (= pt/all-relations (set (keys pt/point-composition))))
      (doseq [[_ row] pt/point-composition]
        (is (= pt/all-relations (set (keys row)))))))
  (testing "the two unconstrained entries are the ones where the middle instant pins nothing"
    (is (= #{[:before :after] [:after :before]}
           (set (for [[r1 row] pt/point-composition
                      [r2 rels] row
                      :when (= rels pt/all-relations)]
                  [r1 r2]))))))

(deftest coincidence-is-the-identity-element
  (doseq [r pt/all-relations]
    (is (= #{r} (pt/compose #{:equal} #{r})))
    (is (= #{r} (pt/compose #{r} #{:equal})))))

(deftest the-converse-pairs-off-and-reverses-composition
  (is (= #{:after} (pt/converse-set #{:before})))
  (is (= #{:before} (pt/converse-set #{:after})))
  (is (= #{:equal} (pt/converse-set #{:equal})) "coincidence is its own converse")
  (testing "it is an involution over the whole universe"
    (is (= pt/all-relations (pt/converse-set (pt/converse-set pt/all-relations))))
    (doseq [r pt/all-relations]
      (is (= #{r} (pt/converse-set (pt/converse-set #{r}))))))
  (testing "and it reverses composition, as a relation algebra requires"
    (doseq [a pt/all-relations b pt/all-relations]
      (is (= (pt/converse-set (pt/compose #{a} #{b}))
             (pt/compose (pt/converse-set #{b}) (pt/converse-set #{a})))
          (str "converse(" a " ∘ " b ")")))))

(deftest composition-of-sets-is-the-union-over-their-members
  (is (= (set/union (pt/compose #{:before} #{:after}) (pt/compose #{:equal} #{:after}))
         (pt/compose #{:before :equal} #{:after}))
      "a disjunction on either side admits every combination"))

(deftest the-derived-predicates-are-the-complements-of-the-base-ones
  (doseq [[derived base] '{instantNotBefore instantBefore
                           instantNotAfter  instantAfter
                           instantNotEqual  instantEqual}]
    (is (= pt/all-relations
           (set/union (pt/instant-denotation derived) (pt/instant-denotation base)))
        (str derived " and " base " cover the universe"))
    (is (empty? (set/intersection (pt/instant-denotation derived)
                                  (pt/instant-denotation base)))
        (str derived " and " base " share nothing"))))

(deftest the-algebra-drives-the-engine-with-no-kb-in-sight
  (let [net '{[A B] #{:before} [B A] #{:after}
              [B D] #{:before} [D B] #{:after}}
        pc  (qcn/path-consistent net '#{A B D} pt/point-algebra)]
    (testing "path consistency composes the chain into the pair nobody recorded"
      (is (= #{:before} (qcn/constraint pc pt/point-algebra 'A 'D)))
      (is (= #{:after} (qcn/constraint pc pt/point-algebra 'D 'A))))
    (testing "and the diagonal is the algebra's identity"
      (is (= #{:equal} (qcn/constraint pc pt/point-algebra 'A 'A)))))
  (testing "a cycle of strict orderings empties a constraint"
    (is (= :inconsistent
           (qcn/path-consistent '{[A B] #{:before} [B A] #{:after}
                                  [B D] #{:before} [D B] #{:after}
                                  [D A] #{:before} [A D] #{:after}}
                                '#{A B D} pt/point-algebra)))))

;; ---- entailment over a KB -----------------------------------------------

(tu/deftest-kb composition-derives-an-unasserted-ordering
  (tu/with-terms [P Q R]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantBefore Q R) C)
    (testing "before∘before = before, so P precedes R though nobody said so"
      (is (v/ask? kb (list 'instantBefore P R) C))
      (is (= #{:before} (pt/possible-point-relations kb C P R)))
      (is (= :before (pt/definite-point-relation kb C P R))))
    (testing "so a relation the network excludes is not answered"
      (is (not (v/ask? kb (list 'instantAfter P R) C)))
      (is (not (v/ask? kb (list 'instantEqual P R) C))))
    (testing "and the converse is read off the same constraint"
      (is (v/ask? kb (list 'instantAfter R P) C)))))

(tu/deftest-kb a-long-chain-stays-strict
  (tu/with-terms [P Q R S]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantBefore Q R) C)
    (v/assert kb (list 'instantBefore R S) C)
    (testing "strictness survives any number of links — every entry but the two loose ones
              is a singleton"
      (is (= #{:before} (pt/possible-point-relations kb C P S)))
      (is (v/ask? kb (list 'instantBefore P S) C)))))

(tu/deftest-kb coincidence-transports-an-ordering
  (tu/with-terms [P Q R]
    (v/assert kb (list 'instantEqual P Q) C)
    (v/assert kb (list 'instantBefore Q R) C)
    (testing "P and Q are one moment, so what holds of Q holds of P"
      (is (v/ask? kb (list 'instantBefore P R) C))
      (is (v/ask? kb (list 'instantEqual Q P) C) "coincidence is its own converse"))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [P Q R]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantBefore Q R) C)
    (testing "#{:before} sits inside every denotation that contains it"
      (is (v/ask? kb (list 'instantNotAfter P R) C))
      (is (v/ask? kb (list 'instantNotEqual P R) C)))
    (testing "and outside the ones that do not"
      (is (not (v/ask? kb (list 'instantNotBefore P R) C))))
    (testing "the converse derived predicate holds the other way round"
      (is (v/ask? kb (list 'instantNotBefore R P) C)))))

(tu/deftest-kb a-derived-assertion-constrains-without-pinning
  (tu/with-terms [P Q]
    (v/assert kb (list 'instantNotAfter P Q) C)
    (is (= #{:before :equal} (pt/possible-point-relations kb C P Q)))
    (testing "the predicate asserted is entailed, and its converse"
      (is (v/ask? kb (list 'instantNotAfter P Q) C))
      (is (v/ask? kb (list 'instantNotBefore Q P) C)))
    (testing "but neither of the two base relations it leaves open is"
      (is (not (v/ask? kb (list 'instantBefore P Q) C)))
      (is (not (v/ask? kb (list 'instantEqual P Q) C))))
    (testing "and a second fact intersects it down to one"
      (v/assert kb (list 'instantNotEqual P Q) C)
      (is (= #{:before} (pt/possible-point-relations kb C P Q)))
      (is (v/ask? kb (list 'instantBefore P Q) C)))))

(tu/deftest-kb a-pair-nothing-reaches-is-unconstrained
  (tu/with-terms [P Q]
    (is (= pt/all-relations (pt/possible-point-relations kb C P Q)))
    (is (= :unknown (pt/definite-point-relation kb C P Q)))
    (testing "and the two loose composition entries leave a real pair open too"
      (tu/with-terms [R]
        (v/assert kb (list 'instantBefore P Q) C)   ; P < Q
        (v/assert kb (list 'instantBefore R Q) C)   ; R < Q
        (is (= pt/all-relations (pt/possible-point-relations kb C P R))
            "both sit before Q, in either order")
        (is (not (v/ask? kb (list 'instantNotAfter P R) C)))))))

;; ---- inconsistency -------------------------------------------------------

(tu/deftest-kb a-cycle-of-strict-orderings-is-unsatisfiable
  (tu/with-terms [P Q R]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantBefore Q R) C)
    (v/assert kb (list 'instantBefore R P) C)
    (testing "no assignment of moments makes all three hold, and the pass proves it"
      (is (pt/inconsistent? kb C))
      (is (= #{} (pt/possible-point-relations kb C P R)))
      (is (= :inconsistent (pt/definite-point-relation kb C P R))))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'instantBefore P Q) C)))
      (is (empty? (v/ask kb (list 'instantBefore P '?y) C))))
    (testing "retracting one of the three gives the others their answers back"
      (v/retract! kb (v/handle-of kb (list 'instantBefore R P) C))
      (is (not (pt/inconsistent? kb C)))
      (is (v/ask? kb (list 'instantBefore P R) C)))))

(tu/deftest-kb two-facts-about-one-pair-can-contradict-outright
  (tu/with-terms [P Q]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantAfter P Q) C)
    (is (= #{} (pt/possible-point-relations kb C P Q)))
    (is (pt/inconsistent? kb C))))

;; ---- open enumeration ----------------------------------------------------

(tu/deftest-kb an-open-argument-enumerates-the-entailed-instants
  (tu/with-terms [P Q R]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantBefore Q R) C)
    (testing "(instantBefore P ?y) — every instant P is entailed to precede"
      (is (= #{Q R} (set (map #(get % '?y) (v/ask kb (list 'instantBefore P '?y) C))))))
    (testing "(instantNotAfter ?x R) — every instant entailed to fall no later than R,
              R included: its denotation holds :equal, and the diagonal is :equal"
      (is (= #{P Q R} (set (map #(get % '?x) (v/ask kb (list 'instantNotAfter '?x R) C))))))
    (testing "while the strict form leaves R out"
      (is (= #{P Q} (set (map #(get % '?x) (v/ask kb (list 'instantBefore '?x R) C))))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (is (= #{[P Q] [P R] [Q R]}
             (set (map (juxt #(get % '?x) #(get % '?y))
                       (v/ask kb (list 'instantBefore '?x '?y) C))))))
    (testing "one variable twice is the diagonal, where only coincidence holds"
      (is (= #{P Q R}
             (set (map #(get % '?x) (v/ask kb (list 'instantNotAfter '?x '?x) C)))))
      (is (empty? (v/ask kb (list 'instantBefore '?x '?x) C)))
      (is (empty? (v/ask kb (list 'instantNotEqual '?x '?x) C))))))

;; ---- context and belief --------------------------------------------------

(tu/deftest-kb the-network-follows-belief-and-visibility
  (tu/with-terms [P Q R CxInner CxOuter]
    (v/assert kb (list 'genlCx CxInner CxOuter) C)
    (v/assert kb (list 'instantBefore P Q) CxOuter)
    (v/assert kb (list 'instantBefore Q R) CxInner)
    (testing "the inner context sees both facts, so it composes the chain"
      (is (v/ask? kb (list 'instantBefore P R) CxInner)))
    (testing "the outer sees only its own, so it composes nothing"
      (is (not (v/ask? kb (list 'instantBefore P R) CxOuter))))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'instantBefore Q R) CxInner))
      (is (not (v/ask? kb (list 'instantBefore P R) CxInner))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (is (not-any? #(qkb/prover-for? :point %) provers/default-provers)
      "nothing about instants is in the default registry, so a KB pays for the network
       only once it asks for it"))

(tu/deftest-kb without-the-prover-only-the-declared-transitivity-answers
  ;; CxTime declares `(transitive instantBefore)`, so the default registry composes a
  ;; chain of strict orderings by walking it.  What the network adds is everything the
  ;; walk cannot reach: an ordering through an *equality*, and the derived relations that
  ;; name a disjunction of the base ones.
  (tu/with-terms [P Q R S]
    (v/assert kb (list 'instantBefore P Q) C)
    (v/assert kb (list 'instantBefore Q S) C)
    (v/assert kb (list 'instantEqual Q R) C)
    (let [without (fn [g] (provers/solve-goal-with kb provers/default-provers g C))]
      (testing "an asserted relation is retrievable as an ordinary fact"
        (is (seq (without (list 'instantBefore P Q)))))
      (testing "and a chain of strict orderings composes, the declaration being a walk"
        (is (seq (without (list 'instantBefore P S)))))
      (testing "but a chain through an equality is not a chain of edges"
        (is (empty? (without (list 'instantBefore P R)))))
      (testing "nor is a derived relation, which names a disjunction rather than an edge"
        (is (empty? (without (list 'instantNotAfter P Q)))))
      (testing "the registered prover on the very same facts answers both"
        (is (v/ask? kb (list 'instantBefore P R) C))
        (is (v/ask? kb (list 'instantNotAfter P Q) C))))))
