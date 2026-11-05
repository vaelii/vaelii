;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.structure-test
  "The data structures of structure.txt: `ListFn`, `MultisetFn`, `SetFn` and `MapFn` terms,
  the four relations over one (`elementOf`, `cardinalityOf`, `multiplicityOf`, `valueAt`),
  and each constructor's corresponding predicate, all answered by
  `provers/StructureProver` and none of them stored (docs/nat.md, \"A data structure is a
  structural term\")."
  (:require [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(defn- answers
  "The bindings of `vars` in each answer to `goal` in `context`, as a vector in answer order."
  ([kb goal vars] (answers kb goal vars U))
  ([kb goal vars context]
   (mapv (fn [b] (mapv #(get b %) vars)) (v/ask kb goal context))))

(tu/deftest-kb an-element-is-bound-in-the-structure-s-order-and-checked-when-ground
  (testing "a list binds its items in order, each repeat once"
    (is (= '[[1] [2] [3]] (answers kb '(elementOf ?x (ListFn 1 2 3 2)) '[?x]))))
  (testing "a multiset and a set bind each element once"
    (is (= '[[1] [2]] (answers kb '(elementOf ?x (MultisetFn 2 1 2)) '[?x])))
    (is (= '[[1] [2]] (answers kb '(elementOf ?x (SetFn 2 1 2)) '[?x]))))
  (testing "a map's elements are its entries"
    (is (= '[[(EntryFn 1 "one")]] (answers kb '(elementOf ?e (MapFn (EntryFn 1 "one"))) '[?e])))
    (is (= '[["one"]] (answers kb '(elementOf (EntryFn 1 ?v) (MapFn (EntryFn 1 "one"))) '[?v]))))
  (testing "a ground element holds or does not"
    (is (v/ask? kb '(elementOf 2 (SetFn 1 2)) U))
    (is (not (v/ask? kb '(elementOf 3 (SetFn 1 2)) U))))
  (testing "the empty structure has no element"
    (is (empty? (v/ask kb '(elementOf ?x (ListFn)) U)))))

(tu/deftest-kb a-cardinality-counts-repeats-only-where-the-kind-keeps-them
  (is (= '[[4]] (answers kb '(cardinalityOf ?n (ListFn 1 2 2 3)) '[?n])))
  (is (= '[[4]] (answers kb '(cardinalityOf ?n (MultisetFn 1 2 2 3)) '[?n])))
  (is (= '[[3]] (answers kb '(cardinalityOf ?n (SetFn 1 2 2 3)) '[?n])))
  (is (= '[[2]] (answers kb '(cardinalityOf ?n (MapFn (EntryFn 1 "a") (EntryFn 2 "b"))) '[?n])))
  (is (= '[[0]] (answers kb '(cardinalityOf ?n (SetFn)) '[?n])))
  (is (v/ask? kb '(cardinalityOf 2 (SetFn 1 2)) U))
  (is (not (v/ask? kb '(cardinalityOf 3 (SetFn 1 2)) U))))

(tu/deftest-kb a-multiplicity-counts-in-a-list-or-multiset-and-is-one-or-zero-in-a-set
  (is (= '[[1 1] [2 2]] (answers kb '(multiplicityOf ?n ?x (MultisetFn 2 1 2)) '[?n ?x])))
  (is (= '[[1 1] [1 2]] (answers kb '(multiplicityOf ?n ?x (SetFn 2 1 2)) '[?n ?x])))
  (is (= '[[2]] (answers kb '(multiplicityOf ?n 2 (ListFn 2 1 2)) '[?n])))
  (is (= '[[0]] (answers kb '(multiplicityOf ?n 3 (SetFn 1 2)) '[?n]))))

(tu/deftest-kb a-value-is-read-by-key-in-a-map-and-by-position-in-a-list
  (let [m '(MapFn (EntryFn 1 "one") (EntryFn 2 "two"))]
    (is (= '[["two"]] (answers kb (list 'valueAt '?v 2 m) '[?v])))
    (is (= '[[1 "one"] [2 "two"]] (answers kb (list 'valueAt '?v '?k m) '[?k ?v])))
    (is (empty? (v/ask kb (list 'valueAt '?v 3 m) U))))
  (is (= '[["b"]] (answers kb '(valueAt ?v 2 (ListFn "a" "b")) '[?v])))
  (is (= '[[1 "a"] [2 "b"]] (answers kb '(valueAt ?v ?k (ListFn "a" "b")) '[?k ?v])))
  (is (empty? (v/ask kb '(valueAt ?v 1 (SetFn "a")) U))))

(tu/deftest-kb a-corresponding-predicate-builds-the-canonical-term-and-reads-one-back
  (testing "ground elements bind the structure as the store spells it"
    (is (= '[[(SetFn 1 2)]] (answers kb '(setOf ?s 2 1 2) '[?s])))
    (is (= '[[(MultisetFn 1 2 2)]] (answers kb '(multisetOf ?s 2 1 2) '[?s])))
    (is (= '[[(ListFn 2 1)]] (answers kb '(listOf ?s 2 1) '[?s])))
    (is (= '[[(EntryFn 1 "one")]] (answers kb '(entryOf ?e 1 "one") '[?e]))))
  (testing "a ground structure binds its elements in canonical order"
    (is (= '[[(1 2)]] (answers kb '(setOf (SetFn 2 1) . ?xs) '[?xs])))
    (is (= '[[1 "one"]] (answers kb '(entryOf (EntryFn 1 "one") ?k ?v) '[?k ?v]))))
  (testing "a rest after named elements binds what they leave"
    (is (= '[[(2 3)]] (answers kb '(listOf (ListFn 1 2 3) 1 . ?r) '[?r])))
    (is (= '[[(1 3)]] (answers kb '(setOf (SetFn 1 2 3) 2 . ?r) '[?r])))
    (is (= '[[(1 2)]] (answers kb '(multisetOf (MultisetFn 1 2 2) 2 . ?r) '[?r]))))
  (testing "a fully ground goal holds or does not"
    (is (v/ask? kb '(setOf (SetFn 1 2) 2 1) U))
    (is (not (v/ask? kb '(setOf (SetFn 1 2) 1) U)))
    (is (not (v/ask? kb '(listOf (ListFn 1 2) 2 1) U)))))

(tu/deftest-kb a-set-term-is-one-sentex-in-any-order-and-a-list-term-is-not
  (tu/with-terms [holds]
    (v/assert kb (list holds '(SetFn 2 1 1)) U)
    (v/assert kb (list holds '(SetFn 1 2)) U)
    (v/assert kb (list holds '(ListFn 2 1)) U)
    (v/assert kb (list holds '(ListFn 1 2)) U)
    (v/assert kb (list holds '(SetFn 1 (SetFn 3 2))) U)
    (is (= #{(list holds '(SetFn 1 2)) (list holds '(ListFn 1 2)) (list holds '(ListFn 2 1))
             (list holds '(SetFn 1 (SetFn 2 3)))}
           (into #{} (map :sentence) (v/sentexes-matching kb (list holds '?s) U))))))

(tu/deftest-kb a-forward-rule-joins-a-structure-relation-on-its-bound-structure
  (tu/with-terms [holds member Box]
    (v/assert kb (list 'implies (list 'and (list holds Box '?s) '(elementOf ?x ?s))
                       (list member Box '?x))
              U {:direction :forward :strength :monotonic})
    (v/assert kb (list holds Box '(SetFn 1 2)) U {:strength :monotonic})
    (is (= #{1 2} (into #{} (map '?x) (v/ask kb (list member Box '?x) U))))
    (v/retract! kb (v/handle-of kb (list holds Box '(SetFn 1 2)) U))
    (is (empty? (v/ask kb (list member Box '?x) U)))))

(tu/deftest-kb a-structure-relation-or-corresponding-predicate-is-refused-as-a-fact
  (doseq [s '[(elementOf 1 (SetFn 1)) (cardinalityOf 1 (SetFn 1)) (multiplicityOf 1 1 (SetFn 1))
              (valueAt 1 1 (ListFn 1)) (setOf (SetFn 1) 1) (listOf (ListFn 1) 1)
              (multisetOf (MultisetFn 1) 1) (mapOf (MapFn (EntryFn 1 2)) (EntryFn 1 2)) (entryOf (EntryFn 1 2) 1 2)]]
    (testing (str (first s))
      (let [e (try (v/assert kb s U) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= :not-well-formed (:type (ex-data e))))
        (is (str/includes? (str (ex-message e)) (str (first s) " is not assertible")))))))

(tu/deftest-kb a-dotted-pattern-matches-stored-facts-of-every-length
  (tu/with-terms [rel Aa Bb]
    (v/assert kb (list rel Aa 1) U)
    (v/assert kb (list rel Bb 1 2 3) U)
    (is (= #{[Aa '(1)] [Bb '(1 2 3)]}
           (into #{} (map (juxt '?c '?xs)) (v/ask kb (list rel '?c '. '?xs) U))))))

(tu/deftest-kb a-rule-over-a-spliced-rest-fires-in-either-arrival-order
  (doseq [order [[:rule :fact] [:fact :rule]]]
    (tu/with-terms [rel member Cc]
      (let [rule (list 'implies
                       (list 'and (list rel '?c '. '?xs) '(elementOf ?x (SetFn . ?xs)))
                       (list member '?c '?x))
            step {:rule #(v/assert kb rule U {:direction :forward :strength :monotonic})
                  :fact #(v/assert kb (list rel Cc 2 1 2) U {:strength :monotonic})}]
        (doseq [o order] ((step o)))
        (testing (str order)
          (is (= #{1 2} (into #{} (map '?x) (v/ask kb (list member Cc '?x) U)))))))))

(tu/deftest-kb an-intersection-of-any-arity-reaches-each-type-through-one-rule
  (tu/with-terms [whole part_a part_b part_c part_d]
    (doseq [t [whole part_a part_b part_c part_d]] (v/assert kb (list 'type t) U))
    (v/assert kb '(implies (and (intersection ?c . ?types) (elementOf ?t (SetFn . ?types)))
                           (genl ?c ?t))
              U {:direction :forward :strength :monotonic})
    (v/assert kb (list 'intersection whole part_a part_b part_c part_d) U {:strength :monotonic})
    (is (every? #(v/ask? kb (list 'genl whole %) U) [part_a part_b part_c part_d]))))

(tu/deftest-kb an-element-is-compared-in-the-asking-context-s-normal-form
  (tu/with-terms [Aa Bb CxEq]
    (v/assert kb (list 'genlCx CxEq U) U)
    (v/assert kb (list 'sameAs Aa Bb) CxEq)
    (let [s (list 'SetFn Aa Bb)]
      (testing "the context that sees the merge reads one element"
        (is (v/ask? kb (list 'elementOf Aa (list 'SetFn Bb)) CxEq))
        (is (= [[1]] (answers kb (list 'cardinalityOf '?n s) '[?n] CxEq)))
        (is (= [[2]] (answers kb (list 'multiplicityOf '?n Aa (list 'MultisetFn Aa Bb)) '[?n] CxEq)))
        (is (= #{["a"] ["b"]}
               (set (answers kb (list 'valueAt '?v Aa (list 'MapFn (list 'EntryFn Aa "a")
                                                            (list 'EntryFn Bb "b")))
                             '[?v] CxEq)))))
      (testing "a context that does not see it reads two"
        (is (not (v/ask? kb (list 'elementOf Aa (list 'SetFn Bb)) U)))
        (is (= [[2]] (answers kb (list 'cardinalityOf '?n s) '[?n])))))))

(tu/deftest-kb an-open-element-binds-one-of-each-element-the-asking-context-reads
  (tu/with-terms [Aa Bb CxEq]
    (v/assert kb (list 'genlCx CxEq U) U)
    (v/assert kb (list 'sameAs Aa Bb) CxEq)
    (let [solved #(provers/solve-goal kb % CxEq)]
      (testing "the prover answers once per element, as a forward join reads it"
        (is (= 1 (count (solved (list 'elementOf '?x (list 'SetFn Aa Bb))))))
        (is (= 1 (count (solved (list 'elementOf '?x (list 'ListFn Aa Bb))))))
        (is (= [2] (map '?n (solved (list 'multiplicityOf '?n '?x (list 'MultisetFn Aa Bb)))))))
      (testing "a map counts its entries, so a merged key with two values counts both"
        (let [clash (list 'MapFn (list 'EntryFn Aa 1) (list 'EntryFn Bb 2))
              same  (list 'MapFn (list 'EntryFn Aa 1) (list 'EntryFn Bb 1))]
          (is (= [2] (map '?n (solved (list 'cardinalityOf '?n clash)))))
          (is (= 2 (count (solved (list 'elementOf '?x clash)))))
          (is (= #{1 2} (into #{} (map '?v) (solved (list 'valueAt '?v Aa clash)))))
          (is (= [1] (map '?n (solved (list 'cardinalityOf '?n same)))))
          (is (= 1 (count (solved (list 'elementOf '?x same))))))))))

(tu/deftest-kb a-structure-term-is-found-whole-and-by-a-term-inside-it
  (tu/with-terms [holds Box Aa]
    (v/assert kb (list holds Box (list 'SetFn Aa 2)) U)
    (let [[stored] (map :sentence (v/sentexes-matching kb (list holds Box '?s) U))]
      (is (= #{stored} (into #{} (map :sentence) (v/find-sentexes kb Aa))))
      (is (= #{stored} (into #{} (map :sentence) (v/find-sentexes kb (last stored))))))))

(tu/deftest-kb a-map-giving-one-key-two-values-is-refused
  (tu/with-terms [holds Box]
    (is (= :not-well-formed
           (tu/refusal-type #(v/assert kb (list holds Box '(MapFn (EntryFn 1 "a") (EntryFn 1 "b"))) U))))
    (is (= :not-well-formed
           (tu/refusal-type #(v/assert kb (list holds Box '(SetFn (MapFn (EntryFn 1 "a") (EntryFn 1 "b")))) U))))
    (is (nil? (tu/refusal-type #(v/assert kb (list holds Box '(MapFn (EntryFn 1 "a") (EntryFn 1 "a"))) U))))
    (is (nil? (tu/refusal-type #(v/assert kb (list holds Box '(MapFn (EntryFn 1 "a") (EntryFn 2 "a"))) U))))))

(tu/deftest-kb a-map-holds-only-entries
  (tu/with-terms [holds Box]
    (is (= :arg-type (tu/refusal-type #(v/assert kb (list holds Box '(MapFn 1 2)) U))))
    (is (v/ask? kb '(map_entry (EntryFn 1 "one")) U))))

(defn- proved
  "The bindings of `vars` in each answer `prove` gives `goal` in `context`, as a set."
  ([kb goal vars] (proved kb goal vars U))
  ([kb goal vars context]
   (into #{} (map (fn [b] (mapv #(get b %) vars))) (v/prove kb goal context))))

(tu/deftest-kb a-pattern-inside-a-structure-reads-through-its-corresponding-predicate
  (tu/with-terms [holds Ax Bx Mx Mp Lx]
    (v/assert kb (list holds Ax '(SetFn 1 2)) U)
    (v/assert kb (list holds Bx '(SetFn 1 2 3)) U)
    (v/assert kb (list holds Mx '(MultisetFn 1 2 2)) U)
    (v/assert kb (list holds Mp '(MapFn (EntryFn 1 "one") (EntryFn 2 "two"))) U)
    (v/assert kb (list holds Lx '(ListFn 1 2 3)) U)
    (testing "the patterns name every element, and two of them may name one in a set"
      (is (= #{[1] [2]} (proved kb (list holds Ax '(SetFn 1 2 ?x)) '[?x])))
      (is (= #{[3]} (proved kb (list holds Bx '(SetFn 1 2 ?x)) '[?x])))
      (is (= 6 (count (proved kb (list holds Bx '(SetFn ?a ?b ?c)) '[?a ?b ?c])))))
    (testing "a rest binds the elements no pattern names"
      (is (= #{['(1 3)]} (proved kb (list holds Bx '(SetFn 2 . ?r)) '[?r])))
      (is (= #{["one" '((EntryFn 2 "two"))]}
             (proved kb (list holds Mp '(MapFn (EntryFn 1 ?v) . ?r)) '[?v ?r])))
      (is (= #{['(2 3)]} (proved kb (list holds Lx '(ListFn 1 . ?r)) '[?r]))))
    (testing "a multiset's patterns take one occurrence each"
      (is (= #{[1 2] [2 1]} (proved kb (list holds Mx '(MultisetFn 2 ?x ?y)) '[?x ?y])))
      (is (= #{} (proved kb (list holds Mx '(MultisetFn 1 ?x)) '[?x]))))))

(tu/deftest-kb a-rule-over-a-pattern-inside-a-set-reads-set-of-in-either-arrival-order
  (doseq [order [[:rule :facts] [:facts :rule]]]
    (tu/with-terms [holds outOf Ax Bx]
      (let [rule (list 'implies (list holds '?k '(SetFn 1 2 ?x)) (list outOf '?k '?x))
            step {:rule  #(v/assert kb rule U {:direction :forward :strength :monotonic})
                  :facts #(do (v/assert kb (list holds Ax '(SetFn 1 2)) U)
                              (v/assert kb (list holds Bx '(SetFn 1 2 3)) U))}]
        (doseq [o order] ((step o)))
        (testing (str order)
          (is (= #{1 2} (into #{} (map '?x) (v/ask kb (list outOf Ax '?x) U))))
          (is (= #{3} (into #{} (map '?x) (v/ask kb (list outOf Bx '?x) U))))
          (is (some #(= 'setOf (first %)) (mapcat :antecedent (v/find-sentexes kb outOf)))))))))

(tu/deftest-kb a-backward-rule-head-holding-a-set-answers-a-goal-in-any-argument-order
  (tu/with-terms [rr qq Pp Qq Bx]
    (v/assert kb (list rr Pp) U)
    (v/assert kb (list 'implies (list rr '?y) (list qq (list 'SetFn '?y Qq Bx))) U
              {:direction :backward})
    (doseq [goal [(list qq (list 'SetFn Pp '?x Bx)) (list qq (list 'SetFn Bx Pp '?x))]]
      (is (= #{[Qq]} (proved kb goal '[?x])) (pr-str goal)))))

(tu/deftest-kb a-pattern-inside-a-set-reads-equality-in-the-asking-context
  (tu/with-terms [holds Ay Aa Bb CxEq]
    (v/assert kb (list 'genlCx CxEq U) U)
    (v/assert kb (list 'sameAs Aa Bb) CxEq)
    (v/assert kb (list holds Ay (list 'SetFn Aa Bb)) U)
    (testing "the context that sees the merge reads one element, bound once"
      (is (= 1 (count (proved kb (list holds Ay '(SetFn ?x)) '[?x] CxEq))))
      (is (contains? #{[Aa] [Bb]} (first (proved kb (list holds Ay '(SetFn ?x)) '[?x] CxEq)))))
    (testing "a context that does not see it reads two, so one pattern matches nothing"
      (is (= #{} (proved kb (list holds Ay '(SetFn ?x)) '[?x]))))))

(tu/deftest-kb a-rule-reads-a-nested-pattern-outside-in-and-tests-what-it-binds
  (tu/with-terms [holds outOf small Nx Ax Bx]
    (v/assert kb (list holds Nx '(SetFn (SetFn 7) 8)) U)
    (v/assert kb (list holds Ax '(SetFn 1 2 3)) U)
    (v/assert kb (list holds Bx '(SetFn 1 2 9)) U)
    (v/assert kb (list 'implies (list holds '?k '(SetFn (SetFn ?a) ?b)) (list outOf '?k '?a '?b)) U
              {:direction :forward :strength :monotonic})
    (v/assert kb (list 'implies (list 'and (list holds '?k '(SetFn 1 2 ?x)) '(lessThan ?x 5))
                       (list small '?k '?x))
              U {:direction :forward :strength :monotonic})
    (testing "the outer set is read before the set inside it"
      (is (= #{[7 8]} (into #{} (map (juxt '?a '?b)) (v/ask kb (list outOf Nx '?a '?b) U)))))
    (testing "a computed literal tests the element the pattern bound"
      (is (= #{3} (into #{} (map '?x) (v/ask kb (list small Ax '?x) U))))
      (is (empty? (v/ask kb (list small Bx '?x) U))))))

(tu/deftest-kb a-computed-literal-keeps-an-open-structure-as-written
  (tu/with-terms [rel member]
    (let [h (v/assert kb (list 'implies (list 'and (list rel '?c '. '?xs) '(elementOf ?x (SetFn . ?xs)))
                               (list member '?c '?x))
                      U {:direction :forward :strength :monotonic})]
      (is (some #(and (= 'elementOf (first %)) (seq? (last %)) (= 'SetFn (first (last %))))
                (:antecedent (first (filter #(= h (:id %)) (v/find-sentexes kb member)))))))))
