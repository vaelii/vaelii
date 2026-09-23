;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.relative-test
  "Relative direction (`vaelii.impl.relative`): the nine base relations of a frame of
  reference and the four derived ones, answered by entailment over the path-consistent
  constraint network of everything asserted in a context.

  Two halves.  The first tests the **algebra alone** — no KB, no context, no belief.  The
  composition table is *computed* from two independent axis projections rather than
  transcribed, so it is derived here a second time from the coordinate inequalities that
  define the nine relations, by laying out three things every way three things can be laid
  out on a grid; the two statements share nothing and can only agree by both being right.
  The second half tests the prover over a KB, where what is really being checked is that a
  relation nobody stored comes out — and that it comes out **in one frame only**, since
  the frame of reference here is the context."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.projection :as proj]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.relative :as rel]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxSpace vocabulary that states
;; relative directions in it, and the prover registered.  The vocabulary is an upper
;; context (it is *about* space, so it is nobody else's business); the prover is opt-in, so
;; registering it is what turns stored relative-direction facts into a network.  The
;; algebra tests below need none of it.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxSpace "upper"]])
                        (v/add-prover (rel/relative-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the algebra, derived from coordinates ------------------------------

(def ^:private by-coordinates
  "Each base relation as the inequalities over two places that *define* it, a place in a
  frame being `[lr fb]` — the left-right coordinate growing rightwards, the front-back one
  growing frontwards.  This is the independent second statement of the algebra: everything
  below is derived from here and compared against what `relative/compose` computes from
  the projections, so the two can only agree by both being right."
  {:left         (fn [alr afb blr bfb] (and (< alr blr) (= afb bfb)))
   :right        (fn [alr afb blr bfb] (and (> alr blr) (= afb bfb)))
   :front        (fn [alr afb blr bfb] (and (= alr blr) (> afb bfb)))
   :behind       (fn [alr afb blr bfb] (and (= alr blr) (< afb bfb)))
   :front-left   (fn [alr afb blr bfb] (and (< alr blr) (> afb bfb)))
   :front-right  (fn [alr afb blr bfb] (and (> alr blr) (> afb bfb)))
   :behind-left  (fn [alr afb blr bfb] (and (< alr blr) (< afb bfb)))
   :behind-right (fn [alr afb blr bfb] (and (> alr blr) (< afb bfb)))
   :eq           (fn [alr afb blr bfb] (and (= alr blr) (= afb bfb)))})

(def ^:private places
  "Every place on a 3×3 grid.  Three values per axis is enough to realize *any* layout of
  three things: a layout is a weak ordering of three coordinates on each axis
  independently, so it needs at most three distinct values per axis, and the two axes are
  free of each other."
  (vec (for [lr (range 3) fb (range 3)] [lr fb])))

(defn- holding [[alr afb] [blr bfb]]
  (into #{} (keep (fn [[rel pred]] (when (pred alr afb blr bfb) rel))) by-coordinates))

(defn- relation-of [a b] (first (holding a b)))

(def ^:private derived-composition
  "The composition table computed from `by-coordinates`: lay out three things every way
  they can be laid out on the grid, read off the three relations, and record that r1 ∘ r2
  admits r3."
  (delay
    (reduce (fn [tbl [a b c]]
              (update-in tbl [(relation-of a b) (relation-of b c)]
                         (fnil conj #{}) (relation-of a c)))
            {}
            (for [a places b places c places] [a b c]))))

(deftest the-nine-relations-are-exactly-the-nine-axis-pairs
  (testing "each relation projects onto one [left-right front-back] pair"
    (is (= 9 (count rel/relation->axes)))
    (is (= rel/all-relations (set (keys rel/relation->axes))))
    (is (= rel/all-relations (set (keys by-coordinates)))
        "the projections and the coordinate definitions name the same relations"))
  (testing "and the projection is a bijection onto the whole 3×3 product"
    (is (= (set (for [l [:lt :eq :gt] f [:lt :eq :gt]] [l f]))
           (set (vals rel/relation->axes))))
    ;; totality is a claim about composition, so composition answers it — see the same
    ;; testing block in `orientation_test` for why `(some? (algebra …))` cannot fail
    (let [{:keys [compose universe]} (proj/algebra rel/relation->axes)]
      (is (= rel/all-relations universe))
      (doseq [a universe, b universe]
        (let [r (compose #{a} #{b})]
          (is (seq r) (str "composing " a " with " b " names something"))
          (is (every? universe r)
              (str "and only relations — " a " ∘ " b " = " (pr-str r)))))))
  (testing "and a projection that is not one is refused where it is built, not composed"
    (testing "a missing pair, which covers eight"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"all nine \[x y\] pairs"
           (proj/algebra (dissoc rel/relation->axes :front)))))
    (testing "and a repeated one, which still covers all nine"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"all nine \[x y\] pairs"
           (proj/algebra (assoc rel/relation->axes :nowhere [:gt :gt])))))))

(deftest the-nine-relations-are-jointly-exhaustive-and-pairwise-disjoint
  (testing "exactly one holds of any two places — that is what makes a network of them a
            constraint network at all"
    (doseq [a places b places]
      (is (= 1 (count (holding a b)))
          (str a " and " b " stand in " (holding a b)))))
  (testing "and every one of the nine is realized by some pair, so none is vacuous"
    (is (= rel/all-relations
           (set (for [a places b places] (relation-of a b)))))))

(deftest the-composition-table-matches-the-coordinate-definitions
  ;; The guard on the computation.  A wrong projection or a wrong point-algebra entry is
  ;; not a crash and not an empty answer — it is a wrong entailment, reported with full
  ;; confidence, about a pair nobody asserted anything for.  Nothing downstream could
  ;; catch it, so it is caught here.
  (let [derived @derived-composition]
    (testing "every pair of relations composes to something, and to the same something"
      (doseq [r1 rel/all-relations r2 rel/all-relations]
        (is (= (get-in derived [r1 r2]) (rel/compose #{r1} #{r2}))
            (str r1 " ∘ " r2))))
    (testing "and the derivation reaches all 81 pairs"
      (is (= rel/all-relations (set (keys derived))))
      (doseq [[_ row] derived]
        (is (= rel/all-relations (set (keys row)))))))
  (testing "the four unconstrained entries are the opposite corners, which disagree on
            both axes at once"
    (is (= #{[:front-left :behind-right] [:behind-right :front-left]
             [:front-right :behind-left] [:behind-left :front-right]}
           (set (for [r1 rel/all-relations r2 rel/all-relations
                      :when (= rel/all-relations (rel/compose #{r1} #{r2}))]
                  [r1 r2]))))))

(deftest composition-is-computed-from-the-two-axis-projections
  (testing "a relation composed with itself keeps both axes"
    (is (= #{:left} (rel/compose #{:left} #{:left})) "left of left is left")
    (is (= #{:front-left} (rel/compose #{:front-left} #{:front-left}))))
  (testing "two perpendicular relations combine into the corner between them"
    (is (= #{:front-left} (rel/compose #{:left} #{:front})) "left then in front is front-left")
    (is (= #{:front-left} (rel/compose #{:front} #{:left})) "and so is in front then left")
    (is (= #{:behind-right} (rel/compose #{:behind} #{:right}))))
  (testing "an axis the two disagree on loses all information on that axis"
    (is (= #{:left :eq :right} (rel/compose #{:left} #{:right}))
        "left then right lands somewhere on the frame's front-back line")
    (is (= rel/all-relations (rel/compose #{:front-left} #{:behind-right}))
        "opposite corners disagree on both axes at once, so nothing at all is left")))

(deftest coincidence-is-the-identity-element
  (doseq [r rel/all-relations]
    (is (= #{r} (rel/compose #{:eq} #{r})))
    (is (= #{r} (rel/compose #{r} #{:eq})))))

(deftest composition-of-sets-is-the-union-over-their-members
  (is (= (set/union (rel/compose #{:left} #{:front-left})
                    (rel/compose #{:front} #{:front-left}))
         (rel/compose #{:left :front} #{:front-left}))
      "a disjunction on either side admits every combination"))

(deftest composition-is-total-and-never-empty
  (doseq [a rel/all-relations b rel/all-relations]
    (let [c (rel/compose #{a} #{b})]
      (is (seq c) (str a " ∘ " b " must leave something possible"))
      (is (set/subset? c rel/all-relations)
          (str a " ∘ " b " must stay inside the universe")))))

(deftest the-converse-flips-both-axes
  (is (= #{:right} (rel/converse-set #{:left})))
  (is (= #{:behind-right} (rel/converse-set #{:front-left})))
  (is (= #{:eq} (rel/converse-set #{:eq})) "coincidence is its own converse")
  (testing "it is an involution"
    (is (= rel/all-relations (rel/converse-set (rel/converse-set rel/all-relations))))
    (doseq [r rel/all-relations]
      (is (= #{r} (rel/converse-set (rel/converse-set #{r}))))))
  (testing "and it reverses composition, as a relation algebra requires"
    (doseq [a rel/all-relations b rel/all-relations]
      (is (= (rel/converse-set (rel/compose #{a} #{b}))
             (rel/compose (rel/converse-set #{b}) (rel/converse-set #{a})))
          (str "converse(" a " ∘ " b ")"))))
  (testing "and it agrees with reading the coordinates backwards"
    (doseq [a places b places]
      (is (= #{(relation-of b a)} (rel/converse-set #{(relation-of a b)}))))))

(deftest the-algebra-drives-the-engine-with-no-kb-in-sight
  (let [net '{[A B] #{:left} [B A] #{:right}
              [B D] #{:left} [D B] #{:right}}
        pc  (qcn/path-consistent net '#{A B D} rel/relative-algebra)]
    (testing "path consistency composes the chain into the pair nobody recorded"
      (is (= #{:left} (qcn/constraint pc rel/relative-algebra 'A 'D)))
      (is (= #{:right} (qcn/constraint pc rel/relative-algebra 'D 'A))))
    (testing "and the diagonal is the algebra's identity"
      (is (= #{:eq} (qcn/constraint pc rel/relative-algebra 'A 'A)))))
  (testing "a chain contradicting itself empties a constraint"
    (is (= :inconsistent
           (qcn/path-consistent '{[A B] #{:left}  [B A] #{:right}
                                  [B D] #{:left}  [D B] #{:right}
                                  [A D] #{:right} [D A] #{:left}}
                                '#{A B D} rel/relative-algebra)))))

;; ---- entailment over a KB -----------------------------------------------

(tu/deftest-kb composition-derives-an-unasserted-relation
  (tu/with-terms [Mouse Lion Rock]
    (v/assert kb (list 'leftOf Mouse Lion) C)
    (v/assert kb (list 'leftOf Lion Rock) C)
    (testing "left∘left = left, so the mouse is left of the rock though nobody said so"
      (is (v/ask? kb (list 'leftOf Mouse Rock) C)))
    (testing "and the computed table pins it to exactly that"
      (is (= #{:left} (rel/possible-relative-directions kb C Mouse Rock)))
      (is (= :left (rel/definite-relative-direction kb C Mouse Rock))))
    (testing "so a relation the network excludes is not answered"
      (is (not (v/ask? kb (list 'rightOf Mouse Rock) C)))
      (is (not (v/ask? kb (list 'inFrontOf Mouse Rock) C)))
      (is (not (v/ask? kb (list 'sameRelativePositionAs Mouse Rock) C))))))

(tu/deftest-kb two-perpendicular-facts-compose-into-a-corner
  (tu/with-terms [A B D]
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'inFrontOf B D) C)
    (is (= #{:front-left} (rel/possible-relative-directions kb C A D)))
    (is (v/ask? kb (list 'frontLeftOf A D) C))
    (testing "and the converse corner holds the other way round"
      (is (v/ask? kb (list 'behindRightOf D A) C)))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'frontLeftOf A B) C)
    (v/assert kb (list 'frontLeftOf B D) C)
    (testing "#{:front-left} sits inside every denotation that contains it"
      (is (v/ask? kb (list 'leftwardOf A D) C))
      (is (v/ask? kb (list 'frontwardOf A D) C)))
    (testing "and outside the two denotations that do not"
      (is (not (v/ask? kb (list 'rightwardOf A D) C)))
      (is (not (v/ask? kb (list 'rearwardOf A D) C))))
    (testing "the converse derived predicates hold the other way round"
      (is (v/ask? kb (list 'rightwardOf D A) C))
      (is (v/ask? kb (list 'rearwardOf D A) C)))))

(tu/deftest-kb a-derived-predicate-can-be-the-only-thing-entailed
  (tu/with-terms [A B D]
    ;; the front-back axis disagrees and the left-right axis does not, so the pair is
    ;; #{:behind-left :left :front-left} — three base relations, no one of them entailed,
    ;; and yet every one of them is leftward
    (v/assert kb (list 'frontLeftOf A B) C)
    (v/assert kb (list 'behindLeftOf B D) C)
    (is (= #{:behind-left :left :front-left} (rel/possible-relative-directions kb C A D)))
    (is (= :unknown (rel/definite-relative-direction kb C A D)))
    (testing "no base relation is entailed"
      (is (not (v/ask? kb (list 'leftOf A D) C)))
      (is (not (v/ask? kb (list 'frontLeftOf A D) C)))
      (is (not (v/ask? kb (list 'behindLeftOf A D) C))))
    (testing "but the disjunction covering all three is"
      (is (v/ask? kb (list 'leftwardOf A D) C))
      (is (not (v/ask? kb (list 'rightwardOf A D) C)))
      (is (not (v/ask? kb (list 'frontwardOf A D) C))))))

(tu/deftest-kb the-converse-is-derived-with-the-fact
  (tu/with-terms [A B]
    (v/assert kb (list 'leftOf A B) C)
    (testing "one asserted relation constrains the pair both ways round"
      (is (v/ask? kb (list 'leftOf A B) C))
      (is (v/ask? kb (list 'rightOf B A) C)))
    (testing "and rules the opposite readings out"
      (is (not (v/ask? kb (list 'rightOf A B) C)))
      (is (not (v/ask? kb (list 'leftOf B A) C)))
      (is (not (v/ask? kb (list 'frontwardOf A B) C))
          "directly left is level on the front-back axis, so no forward component"))))

(tu/deftest-kb a-derived-assertion-constrains-without-pinning
  (tu/with-terms [A B]
    (v/assert kb (list 'leftwardOf A B) C)
    (is (= #{:left :front-left :behind-left} (rel/possible-relative-directions kb C A B)))
    (testing "the predicate asserted is entailed, and its converse"
      (is (v/ask? kb (list 'leftwardOf A B) C))
      (is (v/ask? kb (list 'rightwardOf B A) C)))
    (testing "but none of the three base relations it leaves open is"
      (is (not (v/ask? kb (list 'leftOf A B) C)))
      (is (not (v/ask? kb (list 'frontLeftOf A B) C)))
      (is (not (v/ask? kb (list 'behindLeftOf A B) C))))))

(tu/deftest-kb two-facts-about-one-pair-intersect
  (tu/with-terms [A B]
    ;; one fact per axis: each leaves the other axis open, and together they pin the
    ;; relation to the corner between them
    (v/assert kb (list 'leftwardOf A B) C)                ; #{:left :front-left :behind-left}
    (v/assert kb (list 'frontwardOf A B) C)               ; #{:front :front-left :front-right}
    (is (= #{:front-left} (rel/possible-relative-directions kb C A B))
        "the constraint is the intersection, whichever order they were read in")
    (is (v/ask? kb (list 'frontLeftOf A B) C))
    (is (not (v/ask? kb (list 'leftOf A B) C)))))

(tu/deftest-kb coincidence-carries-a-relation-across
  (tu/with-terms [A B D]
    (v/assert kb (list 'sameRelativePositionAs A B) C)
    (v/assert kb (list 'leftOf B D) C)
    (testing "eq is the identity, so A stands where B does"
      (is (= #{:left} (rel/possible-relative-directions kb C A D)))
      (is (v/ask? kb (list 'leftOf A D) C)))))

;; ---- the frame of reference is the context ------------------------------

(tu/deftest-kb a-frame-of-reference-is-a-context-and-does-not-leak
  ;; The test the whole design decision rests on.  Relative direction is ternary in the
  ;; literature and the network is binary; the viewpoint is the context.  So the same
  ;; two individuals stand in opposite relations in two sibling contexts, each context's
  ;; network answers its own way, and neither is contaminated by the other.
  (tu/with-terms [Mouse Lion CxFromTheLion CxFromTheMouse]
    (v/assert kb (list 'genlCx CxFromTheLion C) C)
    (v/assert kb (list 'genlCx CxFromTheMouse C) C)
    (v/assert kb (list 'leftOf Mouse Lion) CxFromTheLion)
    (v/assert kb (list 'rightOf Mouse Lion) CxFromTheMouse)
    (testing "each frame answers its own way"
      (is (= #{:left} (rel/possible-relative-directions kb CxFromTheLion Mouse Lion)))
      (is (= #{:right} (rel/possible-relative-directions kb CxFromTheMouse Mouse Lion)))
      (is (v/ask? kb (list 'leftOf Mouse Lion) CxFromTheLion))
      (is (v/ask? kb (list 'rightOf Mouse Lion) CxFromTheMouse)))
    (testing "and refuses what the other frame says"
      (is (not (v/ask? kb (list 'rightOf Mouse Lion) CxFromTheLion)))
      (is (not (v/ask? kb (list 'leftOf Mouse Lion) CxFromTheMouse))))
    (testing "neither frame is incoherent — the two claims never meet"
      (is (not (rel/inconsistent? kb CxFromTheLion)))
      (is (not (rel/inconsistent? kb CxFromTheMouse))))
    (testing "and the context both of them see sees neither: visibility runs upwards"
      (is (= rel/all-relations (rel/possible-relative-directions kb C Mouse Lion)))
      (is (not (v/ask? kb (list 'leftOf Mouse Lion) C)))
      (is (not (v/ask? kb (list 'rightOf Mouse Lion) C))))))

(tu/deftest-kb a-context-seeing-two-frames-at-once-is-incoherent
  ;; The other side of the same decision, stated rather than hidden: merging two frames
  ;; without translating between them is an error, and a context that sees both makes it.
  (tu/with-terms [Mouse Lion CxFromTheLion CxFromTheMouse CxBothWays]
    (v/assert kb (list 'genlCx CxBothWays CxFromTheLion) C)
    (v/assert kb (list 'genlCx CxBothWays CxFromTheMouse) C)
    (v/assert kb (list 'leftOf Mouse Lion) CxFromTheLion)
    (v/assert kb (list 'rightOf Mouse Lion) CxFromTheMouse)
    (is (rel/inconsistent? kb CxBothWays))
    (is (= #{} (rel/possible-relative-directions kb CxBothWays Mouse Lion)))
    (testing "while the two frames it sees are each still coherent on their own"
      (is (not (rel/inconsistent? kb CxFromTheLion)))
      (is (not (rel/inconsistent? kb CxFromTheMouse))))))

(tu/deftest-kb the-network-follows-belief-and-visibility
  (tu/with-terms [A B D CxInner CxOuter]
    (v/assert kb (list 'genlCx CxInner CxOuter) C)
    (v/assert kb (list 'leftOf A B) CxOuter)
    (v/assert kb (list 'leftOf B D) CxInner)
    (testing "the inner context sees both facts, so it composes the chain"
      (is (v/ask? kb (list 'leftOf A D) CxInner)))
    (testing "the outer context sees only its own, so it composes nothing"
      (is (not (v/ask? kb (list 'leftOf A D) CxOuter)))
      (is (v/ask? kb (list 'leftOf A B) CxOuter)))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'leftOf B D) CxInner))
      (is (not (v/ask? kb (list 'leftOf A D) CxInner))))))

;; ---- inconsistency -------------------------------------------------------

(tu/deftest-kb a-contradictory-network-answers-nothing
  (tu/with-terms [A B D]
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'rightOf A B) C)
    (testing "left and right are disjoint base relations, so their pair empties"
      (is (= #{} (rel/possible-relative-directions kb C A B)))
      (is (= :inconsistent (rel/definite-relative-direction kb C A B))))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'leftOf A B) C)))
      (is (not (v/ask? kb (list 'rightOf A B) C)))
      (is (not (v/ask? kb (list 'leftwardOf A B) C)))
      (is (empty? (v/ask kb (list 'leftwardOf A '?y) C)))
      (is (not (v/ask? kb (list 'sameRelativePositionAs D D) C))
          "not even the diagonal, which holds of anything in a coherent network"))
    (testing "retracting one of the two gives the other its answers back"
      (v/retract! kb (v/handle-of kb (list 'rightOf A B) C))
      (is (v/ask? kb (list 'leftOf A B) C))
      (is (not (v/ask? kb (list 'rightOf A B) C))))))

(tu/deftest-kb an-inconsistency-derived-through-a-chain-is-caught
  (tu/with-terms [A B D]
    ;; A left of B, B left of D — so A is left of D, and cannot also be right of it
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'leftOf B D) C)
    (v/assert kb (list 'rightOf A D) C)
    (is (= :inconsistent (rel/definite-relative-direction kb C A D)))
    (is (not (v/ask? kb (list 'leftOf A B) C))
        "the whole network is unsatisfiable, so no pair of it is answered")))

;; ---- open enumeration ----------------------------------------------------

(tu/deftest-kb an-open-argument-enumerates-the-entailed-things
  (tu/with-terms [A B D]
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'leftOf B D) C)
    (testing "(leftOf A ?y) — everything A is entailed to be left of"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'leftOf A '?y) C)))]
        (is (= #{B D} ys) "B by assertion and D by composition; not A itself")))
    (testing "(leftwardOf ?x D) — everything entailed to lie somewhere left of D"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'leftwardOf '?x D) C)))]
        (is (= #{A B} xs))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'leftwardOf '?x '?y) C)))]
        (is (= #{[A B] [A D] [B D]} pairs))))))

(tu/deftest-kb one-variable-twice-is-the-diagonal
  (tu/with-terms [A B]
    (v/assert kb (list 'leftOf A B) C)
    (testing "(sameRelativePositionAs ?x ?x) holds of everything — its denotation is the
              identity"
      (is (= #{A B} (set (map #(get % '?x)
                              (v/ask kb (list 'sameRelativePositionAs '?x '?x) C))))))
    (testing "and the irreflexive relations hold of none"
      (is (empty? (v/ask kb (list 'leftOf '?x '?x) C)))
      (is (empty? (v/ask kb (list 'leftwardOf '?x '?x) C))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (testing "nothing about a frame of reference is in the default registry, so a KB pays
            for the network only once it asks for it"
    (is (not-any? #(qkb/prover-for? :relative %) provers/default-provers)
        "the calculi share one prover record, so opt-in is asked by which calculus a
         registered prover speaks for, not by its class")))

(tu/deftest-kb without-the-prover-the-facts-are-inert
  ;; the same KB, queried through the *default* registry — the extension point is the prover list, so
  ;; this isolates what registering it adds without building a second KB on the shared
  ;; scratch space (which would clear this one out from under the fixture)
  (tu/with-terms [A B D]
    (v/assert kb (list 'leftOf A B) C)
    (v/assert kb (list 'leftOf B D) C)
    (testing "an asserted relation is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'leftOf A B) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'leftOf A D) C)))
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'leftwardOf A D) C))))
    (testing "the registered prover on the very same facts does"
      (is (v/ask? kb (list 'leftOf A D) C))
      (is (v/ask? kb (list 'leftwardOf A D) C)))))
