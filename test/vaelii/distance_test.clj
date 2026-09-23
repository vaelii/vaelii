;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.distance-test
  "Qualitative distance (`vaelii.impl.distance`): the seven classes of the distance chain
  and the three derived ranges, answered by entailment over the path-consistent constraint
  network of everything asserted in a context.

  Two halves.  The first tests the **algebra alone** — no KB, no context, no belief.  The
  composition table is *computed* from the class bounds by the triangle inequality rather
  than transcribed, so it is checked here against real arithmetic on real numbers: sample
  actual distances out of each class, work out which third distances the triangle
  inequality actually admits, and classify them.  The table must contain every class those
  numbers produce (**soundness**) and no class they never produce (**tightness**).  The
  second half tests the prover over a KB, where — this calculus composing as weakly as it
  does — what is really being checked is that an arrangement is *ruled out*."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.distance :as dist]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxSpace vocabulary that states
;; distances in it, and the prover registered.  The vocabulary is an upper context (it is
;; *about* space, so it is nobody else's business); the prover is opt-in, so registering it
;; is what turns stored distance facts into a network.  The algebra tests below need none
;; of it.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxSpace "upper"]])
                        (v/add-prover (dist/distance-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the algebra, checked against real numbers --------------------------

(def ^:private eps
  "A step small enough to land just inside a class above its exclusive lower bound, and
  far too small to reach the next boundary."
  1.0E-6)

(defn- samples-in
  "Numeric distances drawn from class `c`: just above its exclusive lower bound, at its
  inclusive upper bound, and one in between.  The two unbounded ends are the two special
  cases — `:co` is exactly zero, and the last class has no upper bound to sample, so it is
  sampled by multiples of its lower one."
  [c]
  (let [[lo hi] (dist/class-bounds c)]
    (cond
      (= c :co)   [0.0]
      (= hi ##Inf) [(+ lo eps) (* 10.0 lo) (* 1000.0 lo)]
      :else       [(+ lo eps) (/ (+ lo hi) 2.0) (double hi)])))

(def ^:private all-samples
  "Every sampled distance, across every class — the candidate third sides of a triangle."
  (vec (mapcat samples-in dist/class-order)))

(def ^:private derived-composition
  "The composition table computed from arithmetic on real distances: for every pair of
  classes, take a distance out of each, and record the class of every sampled third
  distance the triangle inequality |d1 - d2| <= d3 <= d1 + d2 admits.  Nothing here reads
  `distance/compose`, so the two statements can only agree by both being right."
  (delay
    (into {}
          (for [c1 dist/class-order]
            [c1 (into {}
                      (for [c2 dist/class-order]
                        [c2 (into #{}
                                  (for [d1 (samples-in c1)
                                        d2 (samples-in c2)
                                        d3 all-samples
                                        :when (and (<= (Math/abs (double (- d1 d2))) d3)
                                                   (<= d3 (+ d1 d2)))]
                                    (dist/classify d3)))]))]))))

(deftest the-seven-classes-tile-the-non-negative-reals
  (is (= 7 (count dist/all-classes)))
  (is (= dist/all-classes (set dist/class-order)))
  (testing "each class starts where the one before it ends, so the chain has no gap and no
            overlap"
    (doseq [[a b] (partition 2 1 dist/class-order)]
      (is (= (second (dist/class-bounds a)) (first (dist/class-bounds b)))
          (str a " must end where " b " begins"))))
  (testing "so every distance falls in exactly one class"
    (doseq [d (concat all-samples [0.0 0.25 3.0 42.0 999.0 123456.0])]
      (is (= 1 (count (filter (fn [c]
                                (let [[lo hi] (dist/class-bounds c)]
                                  (and (< lo d) (<= d hi))))
                              dist/class-order)))
          (str d " must fall in exactly one class"))
      (is (some? (dist/classify d)))))
  (testing "and zero is the co-located class, while a negative number is no distance"
    (is (= :co (dist/classify 0)))
    (is (= :very-far (dist/classify 1.0E12)))
    (is (nil? (dist/classify -1)))))

(deftest the-composition-table-matches-the-triangle-inequality
  ;; The guard on the computation.  A wrong bound or a wrong meets-test is not a crash and
  ;; not an empty answer — it is a wrong entailment, reported with full confidence, about a
  ;; pair nobody asserted anything for.  Nothing downstream could catch it, so it is caught
  ;; here, by numbers that know nothing of the algebra.
  (let [derived @derived-composition]
    (testing "every class real arithmetic produces is in the table — soundness"
      (doseq [c1 dist/class-order c2 dist/class-order]
        (is (set/subset? (get-in derived [c1 c2]) (dist/compose #{c1} #{c2}))
            (str c1 " ∘ " c2))))
    (testing "and every class the table admits is produced by some real triangle —
              tightness, which is what stops the table drifting wider than the truth"
      (doseq [c1 dist/class-order c2 dist/class-order]
        (is (= (get-in derived [c1 c2]) (dist/compose #{c1} #{c2}))
            (str c1 " ∘ " c2))))))

(deftest composition-is-computed-from-the-bounds
  (testing "the chain composes weakly — two mid-range classes leave several open"
    (is (= #{:co :very-close :close :near} (dist/compose #{:close} #{:close})))
    (is (= #{:very-close :close :near} (dist/compose #{:very-close} #{:close}))))
  (testing "but it still rules things out, which is the point of it"
    (is (= #{:co :very-close :close} (dist/compose #{:very-close} #{:very-close}))
        "two very short legs cannot reach further than close")
    (is (not (contains? (dist/compose #{:very-close} #{:very-close}) :very-far)))
    (is (= #{:far :very-far} (dist/compose #{:very-close} #{:very-far}))
        "a short leg off a very long one lands very near the far end"))
  (testing "and only a pair of legs that can be equal reaches zero"
    (is (contains? (dist/compose #{:close} #{:close}) :co))
    (is (not (contains? (dist/compose #{:close} #{:near}) :co))
        "a close leg and a near leg are never the same length"))
  (testing "composition is total and never empty"
    (doseq [a dist/all-classes b dist/all-classes]
      (let [c (dist/compose #{a} #{b})]
        (is (seq c) (str a " ∘ " b " must leave something possible"))
        (is (set/subset? c dist/all-classes))))))

(deftest the-zero-class-is-the-identity-element
  (doseq [c dist/all-classes]
    (is (= #{c} (dist/compose #{:co} #{c})))
    (is (= #{c} (dist/compose #{c} #{:co})))))

(deftest composition-of-sets-is-the-union-over-their-members
  (is (= (set/union (dist/compose #{:close} #{:near}) (dist/compose #{:far} #{:near}))
         (dist/compose #{:close :far} #{:near}))
      "a disjunction on either side admits every combination"))

(deftest the-converse-of-a-distance-is-itself
  (testing "distance is symmetric, so the converse is the identity function — the one way
            this algebra differs structurally from the direction and interval ones"
    (doseq [c dist/all-classes]
      (is (= #{c} (dist/converse-set #{c}))))
    (is (= dist/all-classes (dist/converse-set dist/all-classes)))
    (is (= #{:far :very-far} (dist/converse-set #{:far :very-far}))))
  (testing "and it still reverses composition, as a relation algebra requires"
    (doseq [a dist/all-classes b dist/all-classes]
      (is (= (dist/converse-set (dist/compose #{a} #{b}))
             (dist/compose (dist/converse-set #{b}) (dist/converse-set #{a})))
          (str "converse(" a " ∘ " b ")")))))

(deftest the-algebra-drives-the-engine-with-no-kb-in-sight
  (let [net '{[A B] #{:co} [B A] #{:co}
              [B D] #{:close} [D B] #{:close}}
        pc  (qcn/path-consistent net '#{A B D} dist/distance-algebra)]
    (testing "path consistency composes the chain into the pair nobody recorded"
      (is (= #{:close} (qcn/constraint pc dist/distance-algebra 'A 'D))))
    (testing "and the diagonal is the algebra's identity"
      (is (= #{:co} (qcn/constraint pc dist/distance-algebra 'A 'A)))))
  (testing "a chain the triangle inequality forbids empties a constraint"
    (is (= :inconsistent
           (qcn/path-consistent '{[A B] #{:very-close} [B A] #{:very-close}
                                  [B D] #{:very-close} [D B] #{:very-close}
                                  [A D] #{:very-far}   [D A] #{:very-far}}
                                '#{A B D} dist/distance-algebra)))))

;; ---- entailment over a KB -----------------------------------------------

(tu/deftest-kb the-zero-class-carries-a-distance-across
  (tu/with-terms [A B D]
    (v/assert kb (list 'coLocatedWith A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "co-located is the identity, so A is exactly as far from D as B is"
      (is (= #{:close} (dist/possible-distances kb C A D)))
      (is (= :close (dist/definite-distance kb C A D)))
      (is (v/ask? kb (list 'closeTo A D) C)))
    (testing "so a class the network excludes is not answered"
      (is (not (v/ask? kb (list 'nearTo A D) C)))
      (is (not (v/ask? kb (list 'coLocatedWith A D) C))))))

(tu/deftest-kb the-triangle-inequality-refutes-a-distance
  (tu/with-terms [A B D]
    (v/assert kb (list 'veryCloseTo A B) C)
    (v/assert kb (list 'veryCloseTo B D) C)
    (testing "two very short legs compose to a short one, however they are laid out"
      (is (= #{:co :very-close :close} (dist/possible-distances kb C A D)))
      (is (= :unknown (dist/definite-distance kb C A D))))
    (testing "so nothing at the far end of the chain is possible, which is the refutation
              this calculus is for"
      (is (not (v/ask? kb (list 'veryFarFrom A D) C)))
      (is (not (v/ask? kb (list 'farFrom A D) C)))
      (is (not (v/ask? kb (list 'beyondFarDistanceFrom A D) C))))
    (testing "and the range that covers every survivor is entailed, though no class is"
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C))
      (is (not (v/ask? kb (list 'veryCloseTo A D) C)))
      (is (not (v/ask? kb (list 'coLocatedWith A D) C))))))

(tu/deftest-kb a-distance-the-triangle-inequality-forbids-is-an-inconsistency
  (tu/with-terms [A B D]
    (v/assert kb (list 'veryCloseTo A B) C)
    (v/assert kb (list 'veryCloseTo B D) C)
    (v/assert kb (list 'veryFarFrom A D) C)
    (is (dist/inconsistent? kb C))
    (is (= :inconsistent (dist/definite-distance kb C A D)))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'veryCloseTo A B) C)))
      (is (not (v/ask? kb (list 'coLocatedWith A A) C))))
    (testing "retracting the impossible claim gives the rest their answers back"
      (v/retract! kb (v/handle-of kb (list 'veryFarFrom A D) C))
      (is (not (dist/inconsistent? kb C)))
      (is (v/ask? kb (list 'veryCloseTo A B) C))
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C)))))

(tu/deftest-kb two-contradictory-distances-about-one-pair-empty-it
  (tu/with-terms [A B]
    (v/assert kb (list 'closeTo A B) C)
    (v/assert kb (list 'farFrom A B) C)
    (testing "close and far are disjoint classes of one chain, so their pair empties"
      (is (= #{} (dist/possible-distances kb C A B)))
      (is (= :inconsistent (dist/definite-distance kb C A B)))
      (is (dist/inconsistent? kb C)))
    (testing "retracting one of the two gives the other its answers back"
      (v/retract! kb (v/handle-of kb (list 'farFrom A B) C))
      (is (v/ask? kb (list 'closeTo A B) C))
      (is (not (v/ask? kb (list 'farFrom A B) C))))))

(tu/deftest-kb a-distance-reads-the-same-both-ways-round
  (tu/with-terms [A B]
    (v/assert kb (list 'farFrom A B) C)
    (testing "the converse of a distance is itself, so one fact answers both orders"
      (is (v/ask? kb (list 'farFrom A B) C))
      (is (v/ask? kb (list 'farFrom B A) C))
      (is (= (dist/possible-distances kb C A B) (dist/possible-distances kb C B A))))
    (testing "and the derived ranges follow, in both directions"
      (is (v/ask? kb (list 'beyondFarDistanceFrom A B) C))
      (is (v/ask? kb (list 'beyondFarDistanceFrom B A) C))
      (is (v/ask? kb (list 'atSomeDistanceFrom A B) C))
      (is (not (v/ask? kb (list 'withinNearDistanceOf A B) C))))))

(tu/deftest-kb a-derived-range-constrains-without-pinning
  (tu/with-terms [A B]
    (v/assert kb (list 'withinNearDistanceOf A B) C)
    (is (= #{:co :very-close :close :near} (dist/possible-distances kb C A B)))
    (testing "the predicate asserted is entailed"
      (is (v/ask? kb (list 'withinNearDistanceOf A B) C)))
    (testing "but none of the four classes it leaves open is, and neither is the range
              that excludes the zero class"
      (is (not (v/ask? kb (list 'coLocatedWith A B) C)))
      (is (not (v/ask? kb (list 'nearTo A B) C)))
      (is (not (v/ask? kb (list 'atSomeDistanceFrom A B) C))
          "co-located is still possible, so it cannot be ruled out"))))

(tu/deftest-kb two-facts-about-one-pair-intersect
  (tu/with-terms [A B]
    (v/assert kb (list 'withinNearDistanceOf A B) C)      ; #{:co :very-close :close :near}
    (v/assert kb (list 'atSomeDistanceFrom A B) C)        ; everything but :co
    (is (= #{:very-close :close :near} (dist/possible-distances kb C A B))
        "the constraint is the intersection, whichever order they were read in")
    (is (v/ask? kb (list 'withinNearDistanceOf A B) C))
    (is (v/ask? kb (list 'atSomeDistanceFrom A B) C))
    (is (not (v/ask? kb (list 'closeTo A B) C)))))

(tu/deftest-kb a-chain-of-short-legs-still-bounds-a-long-one
  (tu/with-terms [A B D]
    (v/assert kb (list 'closeTo A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "close∘close spans four classes — this chain composes weakly, and says so"
      (is (= #{:co :very-close :close :near} (dist/possible-distances kb C A D)))
      (is (= :unknown (dist/definite-distance kb C A D))))
    (testing "which is still enough to entail the range covering them"
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C))
      (is (not (v/ask? kb (list 'moderatelyFarFrom A D) C)))
      (is (not (v/ask? kb (list 'beyondFarDistanceFrom A D) C))))))

;; ---- open enumeration ----------------------------------------------------

(tu/deftest-kb an-open-argument-enumerates-the-entailed-things
  (tu/with-terms [A B D]
    (v/assert kb (list 'coLocatedWith A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "(closeTo A ?y) — everything A is entailed to be close to"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'closeTo A '?y) C)))]
        (is (= #{D} ys) "D by composition; B is co-located and A is not close to itself")))
    (testing "(withinNearDistanceOf ?x D) — everything entailed to be no further than near"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'withinNearDistanceOf '?x D) C)))]
        (is (= #{A B D} xs) "D included: the diagonal is the zero class, which is within")))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'closeTo '?x '?y) C)))]
        (is (= #{[A D] [D A] [B D] [D B]} pairs)
            "symmetric, so each entailed pair is answered both ways round")))))

(tu/deftest-kb one-variable-twice-is-the-diagonal
  (tu/with-terms [A B]
    (v/assert kb (list 'farFrom A B) C)
    (testing "(coLocatedWith ?x ?x) holds of everything — its denotation is the identity"
      (is (= #{A B} (set (map #(get % '?x) (v/ask kb (list 'coLocatedWith '?x '?x) C))))))
    (testing "and a range excluding the zero class holds of none"
      (is (empty? (v/ask kb (list 'atSomeDistanceFrom '?x '?x) C)))
      (is (empty? (v/ask kb (list 'farFrom '?x '?x) C))))))

;; ---- context and belief --------------------------------------------------

(tu/deftest-kb the-network-follows-belief-and-visibility
  (tu/with-terms [A B D CxInner CxOuter]
    (v/assert kb (list 'genlCx CxInner CxOuter) C)
    (v/assert kb (list 'coLocatedWith A B) CxOuter)
    (v/assert kb (list 'closeTo B D) CxInner)
    (testing "the inner context sees both facts, so it composes the chain"
      (is (v/ask? kb (list 'closeTo A D) CxInner)))
    (testing "the outer context sees only its own, so it composes nothing"
      (is (not (v/ask? kb (list 'closeTo A D) CxOuter)))
      (is (v/ask? kb (list 'coLocatedWith A B) CxOuter)))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'closeTo B D) CxInner))
      (is (not (v/ask? kb (list 'closeTo A D) CxInner))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (testing "nothing about distance is in the default registry, so a KB pays for the
            network only once it asks for it"
    (is (not-any? #(qkb/prover-for? :distance %) provers/default-provers)
        "the calculi share one prover record, so opt-in is asked by which calculus a
         registered prover speaks for, not by its class")))

(tu/deftest-kb without-the-prover-the-facts-are-inert
  ;; the same KB, queried through the *default* registry — the extension point is the prover list, so
  ;; this isolates what registering it adds without building a second KB on the shared
  ;; scratch space (which would clear this one out from under the fixture)
  (tu/with-terms [A B D]
    (v/assert kb (list 'coLocatedWith A B) C)
    (v/assert kb (list 'closeTo B D) C)
    (testing "an asserted distance is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'closeTo B D) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'closeTo A D) C)))
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'withinNearDistanceOf A D) C))))
    (testing "the registered prover on the very same facts does"
      (is (v/ask? kb (list 'closeTo A D) C))
      (is (v/ask? kb (list 'withinNearDistanceOf A D) C)))))
