;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.interval-test
  "Allen's interval algebra (`vaelii.impl.interval`): the algebra alone, its table and
  converse derived a second time from the endpoint inequalities, then the prover over a
  KB.  The laws every algebra holds are `qcn_algebra_test`'s (docs/time.md)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.test-util :as tu]))

;; One KB per namespace, with the opt-in prover registered; the algebra tests need none.
(use-fixtures :once (tu/loaded #(doto % (tu/load-core!)
                                      (v/add-prover (iv/allen-prover)))))
(use-fixtures :each (tu/neutral))

(def ^:private C 'CxUniverse)

;; ---- the algebra, derived from endpoints --------------------------------

(def ^:private by-endpoints
  "Each base relation as the inequalities over the four endpoints that define it, an
  interval being `[start end]` with `start < end`."
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
  (testing "exactly one holds of any two intervals"
    (doseq [a intervals b intervals]
      (is (= 1 (count (holding a b)))
          (str a " and " b " stand in " (holding a b)))))
  (testing "and every one of the thirteen is realized by some pair, so none is vacuous"
    (is (= iv/all-relations
           (set (for [a intervals b intervals] (relation-of a b)))))))

(deftest the-composition-table-matches-the-endpoint-definitions
  (let [derived @derived-composition]
    (testing "every pair of relations composes to something, and to the same something"
      (doseq [r1 iv/all-relations r2 iv/all-relations]
        (is (= (get-in derived [r1 r2]) (get-in iv/allen-composition [r1 r2]))
            (str r1 " ∘ " r2))))
    (testing "and the table has no entry the derivation does not"
      (is (= iv/all-relations (set (keys iv/allen-composition))))
      (doseq [[_ row] iv/allen-composition]
        (is (= iv/all-relations (set (keys row)))))))
  (testing "the three unconstrained entries are the ones where B constrains nothing"
    (is (= #{[:before :after] [:after :before] [:during :contains]}
           (set (for [[r1 row] iv/allen-composition
                      [r2 rels] row
                      :when (= rels iv/all-relations)]
                  [r1 r2]))))))

(deftest the-converse-matches-the-endpoint-definitions
  (is (= (into {} (for [a intervals b intervals] [(relation-of a b) (relation-of b a)]))
         (into {} (for [r iv/all-relations] [r (first (iv/converse-set #{r}))])))))

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
      (is (= :before (qkb/definite iv/allen kb C A D))))
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
    ;; meets∘metBy ties the two ends together and says nothing about the two starts, so
    ;; the pair is #{:finishes :finished-by :equal} — three base relations, no one of
    ;; them entailed, and yet they all share time
    (v/assert kb (list 'meets A B) C)
    (v/assert kb (list 'metBy B D) C)
    (is (= #{:finishes :finished-by :equal} (iv/possible-allen-relations kb C A D)))
    (is (= :unknown (qkb/definite iv/allen kb C A D)))
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

(tu/deftest-kb a-derived-assertion-constrains-without-determining
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

(defn- answers
  "The values `goal` binds `var` to in `C`."
  [kb goal var]
  (set (map #(get % var) (v/ask kb goal C))))

(tu/deftest-kb containment-is-answered-only-over-time-intervals
  ;; subintervalOf and properSubintervalOf take time intervals, and during takes any
  ;; temporal thing, so a situation is in during's domain and outside theirs
  (tu/with-terms [S1 S2 T1 T2]
    (v/assert kb (list 'situation S1) C)
    (v/assert kb (list 'situation S2) C)
    (v/assert kb (list 'during S1 S2) C)
    (v/assert kb (list 'time_interval T1) C)
    (v/assert kb (list 'time_interval T2) C)
    (v/assert kb (list 'during T1 T2) C)
    (testing "two situations: the base relation holds and the containment does not"
      (is (v/ask? kb (list 'during S1 S2) C))
      (is (v/ask? kb (list 'hasSubinterval S2 S1) C) "hasSubinterval takes temporal things")
      (is (not (v/ask? kb (list 'subintervalOf S1 S2) C)))
      (is (not (v/ask? kb (list 'properSubintervalOf S1 S2) C)))
      (is (not (contains? (answers kb (list 'subintervalOf '?x S2) '?x) S1)))
      (is (empty? (answers kb (list 'properSubintervalOf S1 '?y) '?y))))
    (testing "two time intervals: both containments hold"
      (is (v/ask? kb (list 'subintervalOf T1 T2) C))
      (is (v/ask? kb (list 'properSubintervalOf T1 T2) C))
      (is (contains? (answers kb (list 'subintervalOf '?x T2) '?x) T1))
      (is (= #{T2} (answers kb (list 'properSubintervalOf T1 '?y) '?y))))))

(tu/deftest-kb a-depth-bounded-query-reaches-forever
  ;; Forever's containment is a backward rule.  The registry alone (ask, or query with
  ;; no depth) expands no rule, so it neither lists Forever nor stores anything for it;
  ;; a query given a depth expands the rule, ground and open.
  (tu/with-terms [T1 T2]
    (v/assert kb (list 'time_interval T1) C)
    (v/assert kb (list 'time_interval T2) C)
    (v/assert kb (list 'during T1 T2) C)
    (testing "the registry alone does not expand the rule"
      (is (not (v/ask? kb (list 'subintervalOf T1 'Forever) C)))
      (is (= #{T1 T2} (answers kb (list 'subintervalOf T1 '?y) '?y))))
    (testing "a depth-bounded query reaches Forever, ground and open"
      (is (seq (v/query kb (list 'subintervalOf T1 'Forever) C {:max-depth 1})))
      (is (contains? (set (map '?y (v/query kb (list 'subintervalOf T1 '?y) C {:max-depth 1})))
                     'Forever)))))

(tu/deftest-kb a-membership-moves-a-typed-containment-for-its-readers-in-every-order
  ;; `(time_point P1)` keeps `(subintervalOf P1 P2)` from holding, and no support handle
  ;; names the membership, so its arrival and departure have to reach the forward rule
  ;; and the exception reading the containment.  Each order asserts every sentence, reads
  ;; whether `(sub P1)` is believed, retracts `gone` and reads again.
  (doseq [[label gone expected sentences]
          [["a forward rule, the membership retracted" :point [false true]
            (fn [P1 P2 sub _ _]
              {:rule   [(list 'implies (list 'subintervalOf '?x '?y) (list sub '?x)) {:direction :forward}]
               :during [(list 'during P1 P2)]
               :point  [(list 'time_point P1)]})]
           ["a forward rule, the genl edge under the membership retracted" :edge [false true]
            (fn [P1 P2 sub _ moment]
              {:rule   [(list 'implies (list 'subintervalOf '?x '?y) (list sub '?x)) {:direction :forward}]
               :during [(list 'during P1 P2)]
               :point  [(list moment P1)]
               :edge   [(list 'genl moment 'time_point)]})]
           ["an exception on the containment, the membership retracted" :point [true false]
            (fn [P1 P2 sub mark _]
              {:rule   [(list 'exceptWhen (list 'subintervalOf '?x P2)
                              (list 'set/defaultRule
                                    (list 'set/forwardRule (list 'implies (list mark '?x) (list sub '?x)))))]
               :mark   [(list mark P1)]
               :during [(list 'during P1 P2)]
               :point  [(list 'time_point P1)]})]]]
    (let [orders  (tu/orders (keys (sentences 'P1 'P2 'sub 'mark 'moment)))
          beliefs (frequencies
                   (for [order orders]
                     (tu/with-terms [P1 P2 sub mark moment]
                       (let [m    (sentences P1 P2 sub mark moment)
                             hs   (into {} (for [k order :let [[s o] (m k)]] [k (v/assert kb s C (or o {}))]))
                             read #(boolean (seq (v/sentexes-matching kb (list sub P1) C)))
                             a    (read)
                             _    (v/retract! kb (hs gone))
                             b    (read)]
                         (doseq [k (reverse order) :when (not= k gone)] (v/retract! kb (hs k)))
                         [a b]))))]
      (is (= {expected (count orders)} beliefs) label))))

(tu/deftest-kb an-entailed-containment-answers-generic-parthood
  ;; subintervalOf is below partOf and properSubintervalOf below properPartOf, so a
  ;; containment the network entails is a parthood tuple too
  (tu/with-terms [A B S1 S2]
    (v/assert kb (list 'time_interval A) C)
    (v/assert kb (list 'time_interval B) C)
    (v/assert kb (list 'during A B) C)
    (v/assert kb (list 'situation S1) C)
    (v/assert kb (list 'situation S2) C)
    (v/assert kb (list 'during S1 S2) C)
    (testing "ground"
      (is (v/ask? kb (list 'partOf A B) C))
      (is (v/ask? kb (list 'properPartOf A B) C))
      (is (not (v/ask? kb (list 'properPartOf B A) C))))
    (testing "open"
      (is (contains? (answers kb (list 'partOf '?x B) '?x) A))
      (is (= #{B} (answers kb (list 'properPartOf A '?y) '?y))))
    (testing "the parthood reading keeps the containment's domain"
      (is (not (v/ask? kb (list 'partOf S1 S2) C)))
      (is (not (v/ask? kb (list 'properPartOf S1 S2) C))))))

;; ---- what the algebra leaves open ---------------------------------------

(tu/deftest-kb possible-relations-reports-exactly-what-is-left
  (tu/with-terms [A B D]
    (testing "a pair no fact reaches is unconstrained — all thirteen"
      (is (= iv/all-relations (iv/possible-allen-relations kb C A D)))
      (is (= :unknown (qkb/definite iv/allen kb C A D))))
    (v/assert kb (list 'overlaps A B) C)
    (v/assert kb (list 'during B D) C)
    (testing "overlaps∘during determines only that A ends somewhere strictly inside D"
      (is (= #{:overlaps :starts :during} (iv/possible-allen-relations kb C A D)))
      (is (= :unknown (qkb/definite iv/allen kb C A D)))
      (testing "so no base relation is entailed, though every survivor shares time"
        (is (not (v/ask? kb (list 'overlaps A D) C)))
        (is (not (v/ask? kb (list 'during A D) C)))
        (is (v/ask? kb (list 'sharesTimeWith A D) C)))
      (testing "while the pair a fact determines stays determined"
        (is (= #{:overlaps} (iv/possible-allen-relations kb C A B)))
        (is (= :overlaps (qkb/definite iv/allen kb C A B)))))))

;; ---- inconsistency -------------------------------------------------------

(defn- reflexive-reading
  "The `:supports` of an answer resting on the shipped `(reflexive subintervalOf)` in `k`."
  [k]
  [[{:handle   (v/handle-of k '(reflexive subintervalOf) C)
     :sentence '(reflexive subintervalOf)
     :context  C}]])

(tu/deftest-kb argue-names-the-facts-an-entailed-allen-relation-rests-on
  (tu/with-terms [A B D]
    (let [ab (v/assert kb (list 'before A B) C)
          bd (v/assert kb (list 'meets B D) C)
          r  (v/argue kb (list 'before A D) C)]
      (is (= [#{ab bd}] (mapv #(set (map :handle %)) (:supports (first (:for-derivation r)))))))))

(tu/deftest-kb a-contradictory-component-answers-nothing-and-a-term-outside-it-answers
  ;; a rule concluding `subintervalOf` sends its goals down the union path, where
  ;; `ReflexiveProver` answers beside the calculus
  (doseq [rule? [false true]]
    (tu/with-terms [A B D marker]
      (v/assert kb (list 'before A B) C)
      (v/assert kb (list 'after A B) C)
      (when rule?
        (v/assert kb (list 'set/backwardRule
                           (list 'implies (list marker '?x) (list 'subintervalOf '?x '?x)))
                  C))
      (testing (if rule? "union path" "sole-prover path")
        (testing "before and after are disjoint base relations, so their pair empties"
          (is (= #{} (iv/possible-allen-relations kb C A B)))
          (is (= :inconsistent (qkb/definite iv/allen kb C A B))))
        (testing "no goal over a term of the unsatisfiable component is answered"
          (is (not (v/ask? kb (list 'before A B) C)))
          (is (not (v/ask? kb (list 'after A B) C)))
          (is (not (v/ask? kb (list 'temporallyDisjoint A B) C)))
          (is (empty? (v/ask kb (list 'precedes A '?y) C)))
          (is (not (v/ask? kb (list 'subintervalOf A A) C)))
          (is (not-any? #{{'?x A} {'?x B}} (v/ask kb (list 'subintervalOf '?x '?x) C))))
        (testing "a term outside that component answers as in a coherent network"
          (is (v/ask? kb (list 'subintervalOf D D) C))
          (is (= {:verdict :true :for [{}]
                  :for-derivation [{:goal (list 'subintervalOf D D) :via :leaf
                                    :supports (reflexive-reading kb)}]}
                 (v/argue kb (list 'subintervalOf D D) C {:max-depth 2})))
          (is (= {:verdict :unknown} (v/argue kb (list 'subintervalOf A A) C {:max-depth 2})))
          (is (= #{:equal} (iv/possible-allen-relations kb C D D))))
        (testing "retracting one of the two gives the other its answers back"
          (v/retract! kb (v/handle-of kb (list 'after A B) C))
          (is (v/ask? kb (list 'before A B) C))
          (is (not (v/ask? kb (list 'after A B) C))))))))

(tu/deftest-kb a-contradictory-component-leaves-another-component-answering
  (tu/with-terms [A B D E F]
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'after A B) C)
    (v/assert kb (list 'before D E) C)
    (v/assert kb (list 'before E F) C)
    (is (= #{:before} (iv/possible-allen-relations kb C D F)))
    (is (v/ask? kb (list 'before D F) C))
    (is (= #{{'?y E} {'?y F}} (set (v/ask kb (list 'precedes D '?y) C))))
    (is (not (v/ask? kb (list 'before A F) C)) "A lies in the unsatisfiable component")
    (is (false? (:consistent? (v/qualitative-network kb :allen C))))))

(def ^:private shipped-subinterval-rules
  "The shipped rules concluding `subintervalOf` (time.txt): Forever's containment rule and
  TimeIntersectionFn's two subinterval rules."
  ['(implies (time_interval ?interval) (subintervalOf ?interval Forever))
   '(implies (and (time_interval ?interval1) (time_interval ?interval2))
             (subintervalOf (TimeIntersectionFn ?interval1 ?interval2) ?interval1))
   '(implies (and (time_interval ?interval1) (time_interval ?interval2))
             (subintervalOf (TimeIntersectionFn ?interval1 ?interval2) ?interval2))])

(tu/deftest-kb the-diagonal-of-a-typed-allen-predicate-agrees-on-both-dispatch-routes
  ;; a rule concluding `subintervalOf` sends the goal down the union path, where
  ;; `ReflexiveProver` answers beside the calculus.  The sole-prover path runs on a KB of
  ;; its own with the shipped rules retracted: `res/concludes?` reads every stored rule, so
  ;; an `except` would leave the `:rules` channel open, and `v/fork` refuses a fork of the
  ;; overlay arm's KB (`:stacked-fork`).
  (doseq [rule? [false true]]
    (let [k (if rule?
              kb
              (let [own (doto (v/open-kb {:backend :memory :space [::sole-prover] :recover? false})
                          (tu/clear-kb!)
                          (tu/load-core!)
                          (v/add-prover (iv/allen-prover)))]
                (doseq [r shipped-subinterval-rules]
                  (v/retract! own (v/handle-of own (list 'set/backwardRule r) C)))
                own))]
      (try
        (tu/with-terms [A B E person marker]
          (v/assert k (list 'before A B) C)
          (v/assert k (list 'disjoint person 'time_interval) C)
          (v/assert k (list person E) C)
          (when rule?
            (v/assert k (list 'set/backwardRule
                              (list 'implies (list marker '?x) (list 'subintervalOf '?x '?x)))
                      C))
          (testing (if rule? "union path" "sole-prover path")
            (is (= (if rule? #{:rules} #{})
                   (provers/shadowing-channels k (list 'subintervalOf E E) C)))
            (is (v/ask? k (list 'subintervalOf A A) C))
            (is (= (reflexive-reading k)
                   (:supports (first (:for-derivation (v/argue k (list 'subintervalOf A A) C))))))
            (is (not (v/ask? k (list 'subintervalOf E E) C))
                "E holds a type disjoint from subintervalOf's declared time_interval")
            (is (empty? (v/ask k (list 'subintervalOf E '?y) C)))))
        (finally (when-not rule? (tu/drop-space! [::sole-prover])))))))

(tu/deftest-kb an-inconsistency-derived-through-a-chain-is-caught
  (tu/with-terms [A B D]
    ;; A before B, B before D — so A is before D, and cannot also be after it
    (v/assert kb (list 'before A B) C)
    (v/assert kb (list 'before B D) C)
    (v/assert kb (list 'after A D) C)
    (is (= :inconsistent (qkb/definite iv/allen kb C A D)))
    (is (not (v/ask? kb (list 'before A B) C))
        "the whole network is unsatisfiable, so no pair of it is answered")))

(tu/deftest-kb an-unsatisfiable-point-network-withdraws-the-allen-firings-it-licensed
  (tu/with-terms [A B X Y Z finishedFirst]
    (v/assert kb (list 'arg finishedFirst 1 'thing) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'instantBefore (list 'EndFn A) (list 'StartFn B)) C)
    (v/assert-rule kb [(list 'before '?x B)] (list finishedFirst '?x) C {:direction :forward})
    (testing "the rule fires on a relation only the point network entails"
      (is (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx))))
    (testing "a cycle over instants that bound no interval leaves the interval network satisfiable"
      (let [hs [(v/assert kb (list 'instantBefore Y Z) C)
                (v/assert kb (list 'instantBefore Z Y) C)]]
        (is (true? (:consistent? (v/qualitative-network kb :allen C))))
        (is (v/ask? kb (list 'before A B) C))
        (is (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx)))
        (run! #(v/retract! kb %) hs)))
    ;; the cycle runs through B's start, which A's end precedes, so one component of the
    ;; point network holds both intervals' points
    (let [h  (v/assert kb (list 'instantBefore (list 'StartFn B) X) C)
          h2 (v/assert kb (list 'instantBefore X (list 'StartFn B)) C)]
      (testing "an instant cycle makes the interval network that reads the points unsatisfiable"
        (is (false? (:consistent? (v/qualitative-network kb :allen C))))
        (is (not (v/ask? kb (list 'before A B) C))))
      (testing "the network names the point clash as its source, not the pair it emptied"
        (let [net (v/qualitative-network kb :allen C)]
          (is (empty? (:unsatisfiable net)))
          (is (= [{:source  :point
                   :pairs   (nm/by-print-key #{[(list 'StartFn B) X] [X (list 'StartFn B)]})
                   :support (vec (sort [h h2]))}]
                 (:unsatisfiable-sources net)))
          (let [entry (last (filter #(and (= :qualitative-inconsistency (:violation %))
                                          (= :allen (:calculus %))
                                          (= C (:context %)))
                                    (v/violations kb)))]
            (is (nil? (get-in entry [:detail :pairs])) "the ledger blames no interval pair")
            (is (= (:unsatisfiable-sources net) (get-in entry [:detail :sources]))))))
      (testing "so the firing is withdrawn, though the fact it listed is still believed"
        (is (empty? (v/sentexes-matching kb (list finishedFirst A) '?ctx))))
      (testing "and retracting the cycle revives it"
        (v/retract! kb h)
        (is (v/ask? kb (list 'before A B) C))
        (is (seq (v/sentexes-matching kb (list finishedFirst A) '?ctx)))))))

(tu/deftest-kb an-interval-read-by-its-stated-bounds-keeps-its-answers-beside-an-order-of-its-start-term
  ;; The order is true of the stated bounds: April starts at Apr1, which the chain places
  ;; before May1 only through April's own extent.
  (tu/with-terms [Spring April Mar1 Mar15 Apr1 May1 Jun1]
    (doseq [m [Mar1 Mar15 Apr1 May1 Jun1]] (v/assert kb (list 'time_point m) C))
    (doseq [[i s e] [[Spring Mar1 Jun1] [April Apr1 May1]]]
      (v/assert kb (list 'time_interval i) C)
      (v/assert kb (list 'startOf i s) C)
      (v/assert kb (list 'endOf i e) C))
    (doseq [[a b] [[Mar1 Mar15] [Mar15 Apr1] [May1 Jun1]]]
      (v/assert kb (list 'instantBefore a b) C))
    (let [answers #(mapv (fn [r] (v/ask? kb (list r April Spring) C)) '[subintervalOf during])]
      (is (= [true true] (answers)) "the stated bounds alone")
      (let [h (v/assert kb (list 'instantBefore (list 'StartFn April) May1) C)]
        (is (= [true true] (answers)) "beside the order of April's start term")
        (v/retract! kb h)))))

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
