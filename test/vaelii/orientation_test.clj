;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.orientation-test
  "Cardinal-direction reasoning (`vaelii.impl.orientation`): the nine base compass
  relations and the four derived ones, answered by entailment over the path-consistent
  constraint network of everything asserted in a context.

  Two halves.  The first tests the **algebra alone** — no KB, no context, no belief —
  because the composition table is *computed* from two independent axis projections
  rather than transcribed, and that computation is what a wrong answer here would be
  blamed on.  The second tests the prover over a KB, where what is really being checked
  is that a direction nobody stored comes out."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.projection :as proj]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxSpace vocabulary that states
;; direction relations in it, and the prover registered.  The vocabulary is an upper
;; context (it is *about* space, so it is nobody else's business); the prover is opt-in,
;; so registering it is what turns stored direction facts into a network.  The algebra
;; tests below need none of it.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (core-context/load-into)
                        (seed/load-context 'CxSpace "upper")
                        (v/add-prover (dir/orientation-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the independent second statement of the algebra --------------------

(def ^:private by-axes
  "Each base direction as the inequalities over two places that *define* it, a place being
  `[ew ns]` — the east-west coordinate growing eastward, the north-south one growing
  northward.  This is the independent second statement of the algebra: everything below is
  derived from here and compared against what `orientation/compose` computes from the
  projections, so the two can only agree by both being right."
  {:n  (fn [aew ans bew bns] (and (= aew bew) (> ans bns)))
   :s  (fn [aew ans bew bns] (and (= aew bew) (< ans bns)))
   :e  (fn [aew ans bew bns] (and (> aew bew) (= ans bns)))
   :w  (fn [aew ans bew bns] (and (< aew bew) (= ans bns)))
   :ne (fn [aew ans bew bns] (and (> aew bew) (> ans bns)))
   :nw (fn [aew ans bew bns] (and (< aew bew) (> ans bns)))
   :se (fn [aew ans bew bns] (and (> aew bew) (< ans bns)))
   :sw (fn [aew ans bew bns] (and (< aew bew) (< ans bns)))
   :eq (fn [aew ans bew bns] (and (= aew bew) (= ans bns)))})

(def ^:private places
  "Every place on a 3×3 grid.  Three values per axis realize any layout of three things: a
  layout is a weak ordering of three coordinates on each axis independently, so it needs at
  most three distinct values per axis, and the two axes are free of each other."
  (vec (for [ew (range 3) ns (range 3)] [ew ns])))

(defn- holding [[aew ans] [bew bns]]
  (into #{} (keep (fn [[dir pred]] (when (pred aew ans bew bns) dir))) by-axes))

(defn- direction-of [a b] (first (holding a b)))

(def ^:private derived-composition
  "The composition table computed from `by-axes`: lay out three places every way they can
  sit on the grid, read off the three directions, and record that r1 ∘ r2 admits r3."
  (delay
    (reduce (fn [tbl [a b c]]
              (update-in tbl [(direction-of a b) (direction-of b c)]
                         (fnil conj #{}) (direction-of a c)))
            {}
            (for [a places b places c places] [a b c]))))

;; ---- the algebra, without a KB ------------------------------------------

(deftest the-nine-directions-are-exactly-the-nine-axis-pairs
  (testing "each direction projects onto one [east-west north-south] pair"
    (is (= 9 (count dir/direction->xy)))
    (is (= dir/all-directions (set (keys dir/direction->xy)))))
  (testing "and the projection is a bijection onto the whole 3×3 product"
    (is (= (set (for [x [:lt :eq :gt] y [:lt :eq :gt]] [x y]))
           (set (vals dir/direction->xy))))
    ;; the claim is *totality*, so it is composition that has to answer: reading a
    ;; composed pair back always names a direction, which is why there is no 9×9 table
    ;; here to get wrong.  `(some? (algebra …))` cannot fail — `algebra` either throws or
    ;; returns a map, and both namespaces evaluate it at load — so it asserts nothing.
    (let [{:keys [compose universe]} (proj/algebra dir/direction->xy)]
      (is (= dir/all-directions universe))
      (doseq [a universe, b universe]
        (let [r (compose #{a} #{b})]
          (is (seq r) (str "composing " a " with " b " names something"))
          (is (every? universe r)
              (str "and only directions — " a " ∘ " b " = " (pr-str r)))))))
  ;; Discriminated on `:type`, not on the message: the keyword is the contract a caller
  ;; branches on, and a message a later edit rewords would take this test with it.
  (testing "and a projection that is not one is refused where it is built, not composed"
    (testing "a repeated pair, which still covers all nine"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (proj/algebra (assoc dir/direction->xy :nowhere [:gt :gt]))))]
        (is (= :bad-algebra (:type (ex-data e))))))
    (testing "and a missing one, which covers eight"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (proj/algebra
                            (dissoc dir/direction->xy
                                    (first (sort (keys dir/direction->xy)))))))]
        (is (= :bad-algebra (:type (ex-data e))))))))

(deftest composition-is-computed-from-the-two-axis-projections
  (testing "a direction composed with itself keeps both axes"
    (is (= #{:ne} (dir/compose #{:ne} #{:ne})))
    (is (= #{:n} (dir/compose #{:n} #{:n}))))
  (testing "two perpendicular directions combine into the diagonal between them"
    (is (= #{:ne} (dir/compose #{:n} #{:e})) "north then east is northeast")
    (is (= #{:ne} (dir/compose #{:e} #{:n})) "and so is east then north")
    (is (= #{:nw} (dir/compose #{:n} #{:w}))))
  (testing "an axis the two disagree on loses all information on that axis"
    (is (= #{:n :eq :s} (dir/compose #{:n} #{:s}))
        "north then south lands somewhere on the meridian — east-west still agrees")
    (is (= dir/all-directions (dir/compose #{:ne} #{:sw}))
        "opposite diagonals disagree on both axes at once, so nothing at all is left"))
  (testing "coincidence is the identity element, on either side"
    (doseq [d dir/all-directions]
      (is (= #{d} (dir/compose #{:eq} #{d})))
      (is (= #{d} (dir/compose #{d} #{:eq}))))))

(deftest the-composition-table-matches-the-axis-definitions
  ;; The guard on the computation.  A wrong projection entry — one that still covers all
  ;; nine [x y] pairs, so the bijection check passes and no crash follows — is a wrong
  ;; entailment reported with full confidence about a pair nobody asserted anything for.
  ;; The bijection and totality tests above cannot catch a *permutation* of the projection;
  ;; only comparing every entry against the axis definitions can, which is what `relative`
  ;; does for its own computed table and this does for the cardinal one.
  (let [derived @derived-composition]
    (testing "every pair of directions composes to the same set the definitions give"
      (doseq [r1 dir/all-directions r2 dir/all-directions]
        (is (= (get-in derived [r1 r2]) (dir/compose #{r1} #{r2}))
            (str r1 " ∘ " r2))))
    (testing "and the derivation reaches all 81 pairs"
      (is (= dir/all-directions (set (keys derived))))
      (doseq [[_ row] derived]
        (is (= dir/all-directions (set (keys row))))))))

(deftest composition-of-sets-is-the-union-over-their-members
  (is (= (set/union (dir/compose #{:n} #{:ne}) (dir/compose #{:e} #{:ne}))
         (dir/compose #{:n :e} #{:ne}))
      "a disjunction on either side admits every combination"))

(deftest composition-is-total-and-never-empty
  (doseq [a dir/all-directions b dir/all-directions]
    (let [c (dir/compose #{a} #{b})]
      (is (seq c) (str a " ∘ " b " must leave something possible"))
      (is (set/subset? c dir/all-directions)
          (str a " ∘ " b " must stay inside the universe")))))

(deftest the-converse-flips-both-axes
  (is (= #{:s} (dir/converse-set #{:n})))
  (is (= #{:sw} (dir/converse-set #{:ne})))
  (is (= #{:eq} (dir/converse-set #{:eq})) "coincidence is its own converse")
  (testing "it is an involution"
    (is (= dir/all-directions (dir/converse-set (dir/converse-set dir/all-directions)))))
  (testing "and it reverses composition, as a relation algebra requires"
    (doseq [a dir/all-directions b dir/all-directions]
      (is (= (dir/converse-set (dir/compose #{a} #{b}))
             (dir/compose (dir/converse-set #{b}) (dir/converse-set #{a})))))))

(deftest the-algebra-drives-the-engine-with-no-kb-in-sight
  (let [net '{[A B] #{:ne} [B A] #{:sw}
              [B D] #{:ne} [D B] #{:sw}}
        pc  (qcn/path-consistent net '#{A B D} dir/direction-algebra)]
    (testing "path consistency composes the chain into the pair nobody recorded"
      (is (= #{:ne} (qcn/constraint pc dir/direction-algebra 'A 'D)))
      (is (= #{:sw} (qcn/constraint pc dir/direction-algebra 'D 'A))))
    (testing "and the diagonal is the algebra's identity"
      (is (= #{:eq} (qcn/constraint pc dir/direction-algebra 'A 'A)))))
  (testing "a chain contradicting itself empties a constraint"
    (is (= :inconsistent
           (qcn/path-consistent '{[A B] #{:n} [B A] #{:s}
                                  [B D] #{:n} [D B] #{:s}
                                  [A D] #{:s} [D A] #{:n}}
                                '#{A B D} dir/direction-algebra)))))

;; ---- entailment over a KB -----------------------------------------------

(tu/deftest-kb composition-derives-an-unasserted-direction
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "ne∘ne = ne, so A is northeast of D though nobody said so"
      (is (v/ask? kb (list 'northeastOf A D) C)))
    (testing "and the computed table pins it to exactly that"
      (is (= #{:ne} (dir/possible-directions kb C A D)))
      (is (= :ne (dir/definite-direction kb C A D))))
    (testing "so a direction the network excludes is not answered"
      (is (not (v/ask? kb (list 'southwestOf A D) C)))
      (is (not (v/ask? kb (list 'northOf A D) C)))
      (is (not (v/ask? kb (list 'sameLocationAs A D) C))))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "#{:ne} sits inside every denotation that contains it"
      (is (v/ask? kb (list 'northwardOf A D) C) "northwardOf ⊇ #{:n :ne :nw}")
      (is (v/ask? kb (list 'eastwardOf A D) C)  "eastwardOf  ⊇ #{:e :ne :se}"))
    (testing "and outside the two denotations that do not"
      (is (not (v/ask? kb (list 'southwardOf A D) C)))
      (is (not (v/ask? kb (list 'westwardOf A D) C))))
    (testing "the converse derived predicates hold the other way round"
      (is (v/ask? kb (list 'southwardOf D A) C))
      (is (v/ask? kb (list 'westwardOf D A) C)))))

(tu/deftest-kb the-converse-is-derived-with-the-fact
  (tu/with-terms [A B]
    (v/assert kb (list 'northOf A B) C)
    (testing "one asserted direction constrains the pair both ways round"
      (is (v/ask? kb (list 'northOf A B) C))
      (is (v/ask? kb (list 'southOf B A) C)))
    (testing "and rules the opposite readings out"
      (is (not (v/ask? kb (list 'southOf A B) C)))
      (is (not (v/ask? kb (list 'northOf B A) C)))
      (is (not (v/ask? kb (list 'eastwardOf A B) C))
          "due north is level on the east-west axis, so no easterly component"))))

(tu/deftest-kb an-axis-the-chain-disagrees-on-leaves-the-pair-open
  (tu/with-terms [A B D]
    (v/assert kb (list 'northOf A B) C)
    (v/assert kb (list 'southOf B D) C)
    (testing "north then south says only that A and D share a meridian"
      (is (= #{:n :eq :s} (dir/possible-directions kb C A D)))
      (is (= :unknown (dir/definite-direction kb C A D))))
    (testing "so no direction predicate is entailed — not even a derived one"
      (is (not (v/ask? kb (list 'northOf A D) C)))
      (is (not (v/ask? kb (list 'northwardOf A D) C)))
      (is (not (v/ask? kb (list 'sameLocationAs A D) C))))))

(tu/deftest-kb a-derived-assertion-constrains-without-pinning
  (tu/with-terms [A B]
    (v/assert kb (list 'northwardOf A B) C)
    (is (= #{:n :ne :nw} (dir/possible-directions kb C A B)))
    (testing "the predicate asserted is entailed, and its converse"
      (is (v/ask? kb (list 'northwardOf A B) C))
      (is (v/ask? kb (list 'southwardOf B A) C)))
    (testing "but none of the three base directions it leaves open is"
      (is (not (v/ask? kb (list 'northOf A B) C)))
      (is (not (v/ask? kb (list 'northeastOf A B) C)))
      (is (not (v/ask? kb (list 'northwestOf A B) C))))))

(tu/deftest-kb two-facts-about-one-pair-intersect
  (tu/with-terms [A B]
    ;; one fact per axis: each leaves the other axis open, and together they pin the
    ;; direction to the diagonal between them
    (v/assert kb (list 'northwardOf A B) C)               ; #{:n :ne :nw}
    (v/assert kb (list 'eastwardOf A B) C)                ; #{:e :ne :se}
    (is (= #{:ne} (dir/possible-directions kb C A B))
        "the constraint is the intersection, whichever order they were read in")
    (is (v/ask? kb (list 'northeastOf A B) C))
    (is (not (v/ask? kb (list 'northOf A B) C)))))

(tu/deftest-kb coincidence-carries-a-direction-across
  (tu/with-terms [A B D]
    (v/assert kb (list 'sameLocationAs A B) C)
    (v/assert kb (list 'northOf B D) C)
    (testing "eq is the identity, so A stands where B does"
      (is (= #{:n} (dir/possible-directions kb C A D)))
      (is (v/ask? kb (list 'northOf A D) C)))))

;; ---- inconsistency -------------------------------------------------------

(tu/deftest-kb a-contradictory-network-answers-nothing
  (tu/with-terms [A B D]
    (v/assert kb (list 'northOf A B) C)
    (v/assert kb (list 'southOf A B) C)
    (testing "north and south are disjoint base directions, so their pair empties"
      (is (= #{} (dir/possible-directions kb C A B)))
      (is (= :inconsistent (dir/definite-direction kb C A B))))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'northOf A B) C)))
      (is (not (v/ask? kb (list 'southOf A B) C)))
      (is (not (v/ask? kb (list 'northwardOf A B) C)))
      (is (empty? (v/ask kb (list 'northwardOf A '?y) C)))
      (is (not (v/ask? kb (list 'sameLocationAs D D) C))
          "not even the diagonal, which holds of any place in a coherent network"))
    (testing "retracting one of the two gives the other its answers back"
      (v/retract! kb (v/handle-of kb (list 'southOf A B) C))
      (is (v/ask? kb (list 'northOf A B) C))
      (is (not (v/ask? kb (list 'southOf A B) C))))))

(tu/deftest-kb an-inconsistency-derived-through-a-chain-is-caught
  (tu/with-terms [A B D]
    ;; A north of B, B north of D — so A is north of D, and cannot also be south of it
    (v/assert kb (list 'northOf A B) C)
    (v/assert kb (list 'northOf B D) C)
    (v/assert kb (list 'southOf A D) C)
    (is (= :inconsistent (dir/definite-direction kb C A D)))
    (is (not (v/ask? kb (list 'northOf A B) C))
        "the whole network is unsatisfiable, so no pair of it is answered")))

;; ---- open enumeration ----------------------------------------------------

(tu/deftest-kb an-open-argument-enumerates-the-entailed-places
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "(northeastOf A ?y) — every place A is entailed to be northeast of"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'northeastOf A '?y) C)))]
        (is (= #{B D} ys) "B by assertion and D by composition; not A itself")))
    (testing "(northwardOf ?x D) — every place entailed to lie north of D"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'northwardOf '?x D) C)))]
        (is (= #{A B} xs))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'eastwardOf '?x '?y) C)))]
        (is (= #{[A B] [A D] [B D]} pairs))))))

(tu/deftest-kb one-variable-twice-is-the-diagonal
  (tu/with-terms [A B]
    (v/assert kb (list 'northeastOf A B) C)
    (testing "(sameLocationAs ?x ?x) holds of every place — its denotation is the identity"
      (is (= #{A B} (set (map #(get % '?x) (v/ask kb (list 'sameLocationAs '?x '?x) C))))))
    (testing "and the irreflexive relations hold of none"
      (is (empty? (v/ask kb (list 'northOf '?x '?x) C)))
      (is (empty? (v/ask kb (list 'northwardOf '?x '?x) C))))))

;; ---- context and belief --------------------------------------------------

(tu/deftest-kb the-network-follows-belief-and-visibility
  (tu/with-terms [A B D CxInner CxOuter]
    (v/assert kb (list 'genlCx CxInner CxOuter) C)
    (v/assert kb (list 'northeastOf A B) CxOuter)
    (v/assert kb (list 'northeastOf B D) CxInner)
    (testing "the inner context sees both facts, so it composes the chain"
      (is (v/ask? kb (list 'northeastOf A D) CxInner)))
    (testing "the outer context sees only its own, so it composes nothing"
      (is (not (v/ask? kb (list 'northeastOf A D) CxOuter)))
      (is (v/ask? kb (list 'northeastOf A B) CxOuter)))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'northeastOf B D) CxInner))
      (is (not (v/ask? kb (list 'northeastOf A D) CxInner))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (testing "nothing directional is in the default registry, so a KB pays for the network
            only once it asks for it"
    (is (not-any? #(qkb/prover-for? :cardinal %) provers/default-provers)
        "the three calculi share one prover record, so opt-in is asked by which
         calculus a registered prover speaks for, not by its class")))

(tu/deftest-kb without-the-prover-the-facts-are-inert
  ;; the same KB, queried through the *default* registry — the extension point is the prover list,
  ;; so this isolates what registering it adds without building a second KB on the shared
  ;; scratch space (which would clear this one out from under the fixture)
  (tu/with-terms [A B D]
    (v/assert kb (list 'northeastOf A B) C)
    (v/assert kb (list 'northeastOf B D) C)
    (testing "an asserted direction is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'northeastOf A B) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'northeastOf A D) C)))
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'northwardOf A D) C))))
    (testing "the registered prover on the very same facts does"
      (is (v/ask? kb (list 'northeastOf A D) C))
      (is (v/ask? kb (list 'northwardOf A D) C)))))
