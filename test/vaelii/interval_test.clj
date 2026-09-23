;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.interval-test
  "Allen's interval algebra (`vaelii.impl.interval`): the thirteen base relations and the
  seven derived ones, answered by entailment over the path-consistent constraint network
  of everything asserted in a context.

  Two halves.  The first tests the **algebra alone** — no KB, no context, no belief.  It
  is the larger half, because unlike the cardinal directions the 169-entry composition
  table is *transcribed* rather than computed, and a single mistyped entry would be a
  quietly wrong answer forever after.  So the table is derived here a second time, from
  the endpoint inequalities that *define* the relations, by enumerating every way three
  intervals can be laid out — and the two must agree entry for entry.  The second half
  tests the prover over a KB, where what is really being checked is that a relation
  nobody stored comes out."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, the CxTime vocabulary that states
;; interval relations in it, and the prover registered.  The vocabulary is an upper
;; context (it is *about* time, so it is nobody else's business); the prover is opt-in, so
;; registering it is what turns stored interval facts into a network.  The algebra tests
;; below need none of it.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxTime "upper"]])
                        (v/add-prover (iv/allen-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the algebra, derived from endpoints --------------------------------

(def ^:private by-endpoints
  "Each base relation as the inequalities over the four endpoints that *define* it, an
  interval being `[start end]` with `start < end`.  This is the independent second
  statement of the algebra: everything below is derived from here and compared against
  the transcribed table, so the two can only agree by both being right."
  {:before        (fn [_as ae bs _be] (< ae bs))
   :meets         (fn [_as ae bs _be] (= ae bs))
   :overlaps      (fn [as ae bs be] (and (< as bs) (< bs ae) (< ae be)))
   :finished-by   (fn [as ae bs be] (and (< as bs) (= ae be)))
   :contains      (fn [as ae bs be] (and (< as bs) (> ae be)))
   :starts        (fn [as ae bs be] (and (= as bs) (< ae be)))
   :equal         (fn [as ae bs be] (and (= as bs) (= ae be)))
   :started-by    (fn [as ae bs be] (and (= as bs) (> ae be)))
   :during        (fn [as ae bs be] (and (> as bs) (< ae be)))
   :finishes      (fn [as ae bs be] (and (> as bs) (= ae be)))
   :overlapped-by (fn [as ae bs be] (and (> as bs) (< as be) (> ae be)))
   :met-by        (fn [as _ae _bs be] (= as be))
   :after         (fn [as _ae _bs be] (> as be))})

(def ^:private intervals
  "Every proper interval over the six points 0..5.  Six is enough to realize *any* layout
  of three intervals: a layout is a weak ordering of six endpoints, so it needs at most
  six distinct values, and rank k maps to point k."
  (vec (for [s (range 6) e (range 6) :when (< s e)] [s e])))

(defn- holding [[as ae] [bs be]]
  (into #{} (keep (fn [[rel pred]] (when (pred as ae bs be) rel))) by-endpoints))

(defn- relation-of [a b] (first (holding a b)))

(def ^:private derived-composition
  "The composition table computed from `by-endpoints`: lay out three intervals every way
  they can be laid out, read off the three relations, and record that r1 ∘ r2 admits r3."
  (delay
    (reduce (fn [tbl [a b c]]
              (update-in tbl [(relation-of a b) (relation-of b c)]
                         (fnil conj #{}) (relation-of a c)))
            {}
            (for [a intervals b intervals c intervals] [a b c]))))

(deftest the-thirteen-relations-are-jointly-exhaustive-and-pairwise-disjoint
  (is (= 13 (count iv/all-relations)))
  (is (= iv/all-relations (set (keys by-endpoints)))
      "the transcribed universe and the endpoint definitions name the same relations")
  (testing "exactly one holds of any two intervals — that is what makes a network of them
            a constraint network at all"
    (doseq [a intervals b intervals]
      (is (= 1 (count (holding a b)))
          (str a " and " b " stand in " (holding a b)))))
  (testing "and every one of the thirteen is realized by some pair, so none is vacuous"
    (is (= iv/all-relations
           (set (for [a intervals b intervals] (relation-of a b)))))))

(deftest the-composition-table-matches-the-endpoint-definitions
  ;; The guard on the whole port.  A mis-transcribed entry is not a crash and not an empty
  ;; answer — it is a wrong entailment, reported with full confidence, about a pair nobody
  ;; asserted anything for.  Nothing downstream could catch it, so it is caught here.
  (let [derived @derived-composition]
    (testing "every pair of relations composes to something, and to the same something"
      (doseq [r1 iv/all-relations r2 iv/all-relations]
        (is (= (get-in derived [r1 r2]) (get-in iv/allen-composition [r1 r2]))
            (str r1 " ∘ " r2))))
    (testing "and the table has no entry the derivation does not"
      (is (= iv/all-relations (set (keys iv/allen-composition))))
      (doseq [[_ row] iv/allen-composition]
        (is (= iv/all-relations (set (keys row)))))))
  (testing "the three unconstrained entries are the ones where B pins nothing"
    (is (= #{[:before :after] [:after :before] [:during :contains]}
           (set (for [[r1 row] iv/allen-composition
                      [r2 rels] row
                      :when (= rels iv/all-relations)]
                  [r1 r2]))))))

(deftest coincidence-is-the-identity-element
  (doseq [r iv/all-relations]
    (is (= #{r} (iv/compose #{:equal} #{r})))
    (is (= #{r} (iv/compose #{r} #{:equal})))))

(deftest the-converse-pairs-off-and-reverses-composition
  (is (= #{:after} (iv/converse-set #{:before})))
  (is (= #{:contains} (iv/converse-set #{:during})))
  (is (= #{:equal} (iv/converse-set #{:equal})) "equality is its own converse")
  (testing "it is an involution over the whole universe"
    (is (= iv/all-relations (iv/converse-set (iv/converse-set iv/all-relations)))))
  (testing "and it reverses composition, as a relation algebra requires"
    (doseq [a iv/all-relations b iv/all-relations]
      (is (= (iv/converse-set (iv/compose #{a} #{b}))
             (iv/compose (iv/converse-set #{b}) (iv/converse-set #{a})))
          (str "converse(" a " ∘ " b ")")))))

(deftest composition-of-sets-is-the-union-over-their-members
  (is (= (set/union (iv/compose #{:before} #{:during}) (iv/compose #{:meets} #{:during}))
         (iv/compose #{:before :meets} #{:during}))
      "a disjunction on either side admits every combination"))

(deftest the-algebra-drives-the-engine-with-no-kb-in-sight
  (let [net '{[A B] #{:before} [B A] #{:after}
              [B D] #{:before} [D B] #{:after}}
        pc  (qcn/path-consistent net '#{A B D} iv/allen-algebra)]
    (testing "path consistency composes the chain into the pair nobody recorded"
      (is (= #{:before} (qcn/constraint pc iv/allen-algebra 'A 'D)))
      (is (= #{:after} (qcn/constraint pc iv/allen-algebra 'D 'A))))
    (testing "and the diagonal is the algebra's identity"
      (is (= #{:equal} (qcn/constraint pc iv/allen-algebra 'A 'A)))))
  (testing "a chain contradicting itself empties a constraint"
    (is (= :inconsistent
           (qcn/path-consistent '{[A B] #{:before} [B A] #{:after}
                                  [B D] #{:before} [D B] #{:after}
                                  [A D] #{:after}  [D A] #{:before}}
                                '#{A B D} iv/allen-algebra)))))

;; ---- entailment over a KB -----------------------------------------------

(tu/deftest-kb composition-derives-an-unasserted-relation
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (testing "before∘before = before, so A precedes D though nobody said so"
      (is (v/ask? kb (list 'before A D) C))
      (is (= #{:before} (iv/possible-allen-relations kb C A D)))
      (is (= :before (iv/definite-allen-relation kb C A D))))
    (testing "so a relation the network excludes is not answered"
      (is (not (v/ask? kb (list 'after A D) C)))
      (is (not (v/ask? kb (list 'meets A D) C)))
      (is (not (v/ask? kb (list 'intervalEqual A D) C))))))

(tu/deftest-kb containment-composes-through-the-middle-interval
  (tu/with-terms [A B D]
    (v/assert kb (list 'during A B) C)
    (v/assert kb (list 'during B D) C)
    (testing "during∘during = during"
      (is (= #{:during} (iv/possible-allen-relations kb C A D)))
      (is (v/ask? kb (list 'during A D) C)))
    (testing "and the converse reads the containment the other way"
      (is (v/ask? kb (list 'contains D A) C)))))

(tu/deftest-kb touching-intervals-compose-into-a-gap
  (tu/with-terms [A B D]
    (v/assert kb (list 'meets A B) C)
    (v/assert kb (list 'meets B D) C)
    (testing "A ends where B starts and B ends where D starts, so B lies wholly between"
      (is (= #{:before} (iv/possible-allen-relations kb C A D)))
      (is (v/ask? kb (list 'before A D) C))
      (is (not (v/ask? kb (list 'meets A D) C))))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'during A B) C)
    (v/assert kb (list 'during B D) C)
    (testing "#{:during} sits inside every denotation that contains it"
      (is (v/ask? kb (list 'subintervalOf A D) C))
      (is (v/ask? kb (list 'properSubintervalOf A D) C))
      (is (v/ask? kb (list 'sharesTimeWith A D) C)))
    (testing "and outside the ones that do not"
      (is (not (v/ask? kb (list 'temporallyDisjoint A D) C)))
      (is (not (v/ask? kb (list 'precedes A D) C)))
      (is (not (v/ask? kb (list 'hasSubinterval A D) C))))
    (testing "the converse derived predicate holds the other way round"
      (is (v/ask? kb (list 'hasSubinterval D A) C)))))

(tu/deftest-kb a-derived-predicate-can-be-the-only-thing-entailed
  (tu/with-terms [A B D]
    ;; meets∘metBy pins the two ends together and says nothing about the two starts, so
    ;; the pair is #{:finishes :finished-by :equal} — three base relations, no one of
    ;; them entailed, and yet they all share time
    (v/assert kb (list 'meets A B) C)
    (v/assert kb (list 'metBy B D) C)
    (is (= #{:finishes :finished-by :equal} (iv/possible-allen-relations kb C A D)))
    (is (= :unknown (iv/definite-allen-relation kb C A D)))
    (testing "no base relation is entailed"
      (is (not (v/ask? kb (list 'finishes A D) C)))
      (is (not (v/ask? kb (list 'finishedBy A D) C)))
      (is (not (v/ask? kb (list 'intervalEqual A D) C))))
    (testing "but the disjunction covering all three is"
      (is (v/ask? kb (list 'sharesTimeWith A D) C))
      (is (not (v/ask? kb (list 'temporallyDisjoint A D) C))))))

(tu/deftest-kb the-converse-is-derived-with-the-fact
  (tu/with-terms [A B]
    (v/assert kb (list 'before A B) C)
    (testing "one asserted relation constrains the pair both ways round"
      (is (v/ask? kb (list 'before A B) C))
      (is (v/ask? kb (list 'after B A) C)))
    (testing "and rules the opposite readings out"
      (is (not (v/ask? kb (list 'after A B) C)))
      (is (not (v/ask? kb (list 'before B A) C))))
    (testing "the derived orderings follow, in both directions"
      (is (v/ask? kb (list 'precedes A B) C))
      (is (v/ask? kb (list 'precededBy B A) C))
      (is (v/ask? kb (list 'temporallyDisjoint A B) C))
      (is (v/ask? kb (list 'temporallyDisjoint B A) C))
      (is (not (v/ask? kb (list 'sharesTimeWith A B) C))))))

(tu/deftest-kb a-derived-assertion-constrains-without-pinning
  (tu/with-terms [A B]
    (v/assert kb (list 'precedes A B) C)
    (is (= #{:before :meets} (iv/possible-allen-relations kb C A B)))
    (testing "the predicate asserted is entailed, and its converse"
      (is (v/ask? kb (list 'precedes A B) C))
      (is (v/ask? kb (list 'precededBy B A) C))
      (is (v/ask? kb (list 'temporallyDisjoint A B) C)))
    (testing "but neither of the two base relations it leaves open is"
      (is (not (v/ask? kb (list 'before A B) C)))
      (is (not (v/ask? kb (list 'meets A B) C))))))

(tu/deftest-kb two-facts-about-one-pair-intersect
  (tu/with-terms [A B]
    (v/assert kb (list 'subintervalOf A B) C)     ; #{:during :starts :finishes :equal}
    (v/assert kb (list 'sharesTimeWith A B) C)    ; the nine concurrent relations
    (v/assert kb (list 'properSubintervalOf A B) C) ; drops :equal
    (is (= #{:during :starts :finishes} (iv/possible-allen-relations kb C A B))
        "the constraint is the intersection, whichever order they were read in")
    (is (v/ask? kb (list 'properSubintervalOf A B) C))
    (is (not (v/ask? kb (list 'during A B) C)))))

;; ---- what the algebra leaves open ---------------------------------------

(tu/deftest-kb possible-relations-reports-exactly-what-is-left
  (tu/with-terms [A B D]
    (testing "a pair no fact reaches is unconstrained — all thirteen"
      (is (= iv/all-relations (iv/possible-allen-relations kb C A D)))
      (is (= :unknown (iv/definite-allen-relation kb C A D))))
    (v/assert kb (list 'overlaps A B) C)
    (v/assert kb (list 'during B D) C)
    (testing "overlaps∘during pins only that A ends somewhere strictly inside D"
      (is (= #{:overlaps :starts :during} (iv/possible-allen-relations kb C A D)))
      (is (= :unknown (iv/definite-allen-relation kb C A D)))
      (testing "so no base relation is entailed, though every survivor shares time"
        (is (not (v/ask? kb (list 'overlaps A D) C)))
        (is (not (v/ask? kb (list 'during A D) C)))
        (is (v/ask? kb (list 'sharesTimeWith A D) C)))
      (testing "while the pair a fact pins down stays pinned"
        (is (= #{:overlaps} (iv/possible-allen-relations kb C A B)))
        (is (= :overlaps (iv/definite-allen-relation kb C A B)))))))

;; ---- inconsistency -------------------------------------------------------

(tu/deftest-kb a-contradictory-network-answers-nothing
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'after A B) C)
    (testing "before and after are disjoint base relations, so their pair empties"
      (is (= #{} (iv/possible-allen-relations kb C A B)))
      (is (= :inconsistent (iv/definite-allen-relation kb C A B))))
    (testing "and an inconsistent theory is not mined for conclusions — anywhere"
      (is (not (v/ask? kb (list 'before A B) C)))
      (is (not (v/ask? kb (list 'after A B) C)))
      (is (not (v/ask? kb (list 'temporallyDisjoint A B) C)))
      (is (empty? (v/ask kb (list 'precedes A '?y) C)))
      (is (not (v/ask? kb (list 'subintervalOf D D) C))
          "not even the diagonal, which holds of any interval in a coherent network"))
    (testing "retracting one of the two gives the other its answers back"
      (v/retract! kb (v/handle-of kb (list 'after A B) C))
      (is (v/ask? kb (list 'before A B) C))
      (is (not (v/ask? kb (list 'after A B) C))))))

(tu/deftest-kb an-inconsistency-derived-through-a-chain-is-caught
  (tu/with-terms [A B D]
    ;; A before B, B before D — so A is before D, and cannot also be after it
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (v/assert kb (list 'after A D) C)
    (is (= :inconsistent (iv/definite-allen-relation kb C A D)))
    (is (not (v/ask? kb (list 'before A B) C))
        "the whole network is unsatisfiable, so no pair of it is answered")))

;; ---- open enumeration ----------------------------------------------------

(tu/deftest-kb an-open-argument-enumerates-the-entailed-intervals
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (testing "(before A ?y) — every interval A is entailed to precede"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'before A '?y) C)))]
        (is (= #{B D} ys) "B by assertion and D by composition; not A itself")))
    (testing "(precedes ?x D) — every interval entailed to end no later than D begins"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'precedes '?x D) C)))]
        (is (= #{A B} xs))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                            (v/ask kb (list 'before '?x '?y) C)))]
        (is (= #{[A B] [A D] [B D]} pairs))))))

(tu/deftest-kb one-variable-twice-is-the-diagonal
  (tu/with-terms [A B]
    (v/assert kb (list 'before A B) C)
    (testing "(subintervalOf ?x ?x) holds of every interval — its denotation has :equal"
      (is (= #{A B} (set (map #(get % '?x) (v/ask kb (list 'subintervalOf '?x '?x) C))))))
    (testing "and the irreflexive relations hold of none"
      (is (empty? (v/ask kb (list 'before '?x '?x) C)))
      (is (empty? (v/ask kb (list 'properSubintervalOf '?x '?x) C)))
      (is (empty? (v/ask kb (list 'temporallyDisjoint '?x '?x) C))))))

;; ---- context and belief --------------------------------------------------

(tu/deftest-kb the-network-follows-belief-and-visibility
  (tu/with-terms [A B D CxInner CxOuter]
    (v/assert kb (list 'genlCx CxInner CxOuter) C)
    (v/assert kb (list 'before A B) CxOuter)
    (v/assert kb (list 'before B D) CxInner)
    (testing "the inner context sees both facts, so it composes the chain"
      (is (v/ask? kb (list 'before A D) CxInner)))
    (testing "the outer context sees only its own, so it composes nothing"
      (is (not (v/ask? kb (list 'before A D) CxOuter)))
      (is (v/ask? kb (list 'before A B) CxOuter)))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'before B D) CxInner))
      (is (not (v/ask? kb (list 'before A D) CxInner))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (testing "nothing temporal is in the default registry, so a KB pays for the network
            only once it asks for it"
    (is (not-any? #(qkb/prover-for? :allen %) provers/default-provers)
        "the three calculi share one prover record, so opt-in is asked by which
         calculus a registered prover speaks for, not by its class")))

(tu/deftest-kb without-the-prover-the-facts-are-inert
  ;; the same KB, queried through the *default* registry — the extension point is the prover list, so
  ;; this isolates what registering it adds without building a second KB on the shared
  ;; scratch space (which would clear this one out from under the fixture)
  (tu/with-terms [A B D]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (testing "an asserted relation is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'before A B) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'before A D) C)))
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'precedes A D) C))))
    (testing "the registered prover on the very same facts does"
      (is (v/ask? kb (list 'before A D) C))
      (is (v/ask? kb (list 'precedes A D) C)))))
