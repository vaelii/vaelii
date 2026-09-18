;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.aggregate-test
  "Aggregation as a **query operator** — the third member of the `unknown` /
  `thereExists` family.

  `(agg/count ?n ?v Body)` and its four siblings reduce a query's solutions to one
  number: `?v` is projected out, `?n` is the only binding produced, the body runs at
  level 6, and nothing is stored.  In a rule antecedent the aggregate runs once per
  binding the generators supply, which is where GROUP BY comes from — and a firing that
  rested on a count is maintained by the same re-check machinery `unknown` uses.  See
  docs/aggregate.md."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- one
  "The single binding of `k` an aggregate answers with, or nil when it answers nothing.
  Asserts the 'exactly one answer or none' invariant on the way past."
  [kb goal k]
  (let [sols (v/ask kb goal 'CxWell)]
    (is (>= 1 (count sols)) "an aggregate yields exactly one answer or none")
    (get (first sols) k)))

;; ---- shape: free variables and projection -------------------------------

(deftest free-vars-subtracts-both-of-the-aggregate-s-own-slots
  (testing "the reduction variable is projected out, like a thereExists binder"
    (is (= #{} (sx/free-vars '(agg/count ?n ?v (ancestorOf ?v Tom))))))
  (testing "the grouping variable is what an earlier antecedent must supply"
    (is (= '#{?x} (sx/free-vars '(agg/count ?n ?v (ancestorOf ?v ?x))))))
  (testing "a bound ?n contributes nothing either — it is the operator's output"
    (is (= #{} (sx/free-vars '(agg/sum 3 ?v (mass ?v Tom)))))))

(deftest an-aggregate-is-deferred-so-it-never-outruns-its-binders
  (doseq [f (keys sx/aggregate-functors)]
    (is (sx/deferred-literal? (list f '?n '?v (list 'p '?v '?x)))
        (str f " must be held back past the literals that bind its grouping"))))

;; ---- the five operators over a hand-built extent -------------------------

(defn- extent!
  "Assert `(pred Owner v)` for each v, in `CxWell`, and hand back the sentences."
  [kb pred owner vs]
  (mapv (fn [v] (let [s (list pred owner v)] (v/assert kb s 'CxWell) s)) vs))

(tu/deftest-kb the-five-operators-reduce-the-body-s-solutions
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [3 1 4 1 5])
    (let [g (fn [op] (list op '?n '?v (list scoreOf Team '?v)))]
      (testing "distinct: the two 1s are one value"
        (is (= 4 (one kb (g 'agg/count) '?n))))
      (is (= 13 (one kb (g 'agg/sum) '?n)))
      (is (= 1 (one kb (g 'agg/min) '?n)))
      (is (= 5 (one kb (g 'agg/max) '?n)))
      (is (= 13/4 (rationalize (one kb (g 'agg/avg) '?n)))
          "the mean of the *distinct* values, not of the solutions"))))

(tu/deftest-kb the-reduction-variable-is-projected-out
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [7 8])
    (let [sols (v/ask kb (list 'agg/count '?n '?v (list scoreOf Team '?v)) 'CxWell)]
      (is (= 1 (count sols)))
      (is (= '#{?n} (set (keys (first sols))))
          "?v binds nothing outside the aggregate — it is counted, not witnessed"))))

(tu/deftest-kb a-merged-pair-counts-once
  (tu/with-terms [knows Ada Alan Turing]
    (v/assert kb (list knows Ada Alan) 'CxWell)
    (v/assert kb (list knows Ada Turing) 'CxWell)
    (let [g (list 'agg/count '?n '?v (list knows Ada '?v))]
      (is (= 2 (one kb g '?n)) "two names, two values — before the merge")
      (v/assert kb (list 'sameAs Alan Turing) 'CxWell)
      (is (= 1 (one kb g '?n))
          "one thing, one value — distinctness is by the equality closure's representative"))))

(tu/deftest-kb the-census-counts-only-the-merges-its-own-context-can-see
  ;; The same scoping `different` puts on the same partition: the unique names a
  ;; context holds are the ones *it* has not been told to merge.  Read globally, a
  ;; `sameAs` stated down here would collapse two values in the general context that was
  ;; never told — whose own solutions still name both.
  (tu/with-terms [knows Ada Alan Turing CxLow]
    (v/assert kb (list 'genlCx CxLow 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list knows Ada Alan) 'CxWell)
    (v/assert kb (list knows Ada Turing) 'CxWell)
    (v/assert kb (list 'sameAs Alan Turing) CxLow)
    (let [g (list 'agg/count '?n '?v (list knows Ada '?v))]
      (is (= 1 (get (tu/sole-answer (v/ask kb g CxLow)) '?n))
          "the context that was told of the merge counts one")
      (is (= 2 (get (tu/sole-answer (v/ask kb g 'CxWell)) '?n))
          "and the one above it still counts two"))))

(tu/deftest-kb the-check-arm-compares-instead-of-binding
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [2 4])
    (is (v/ask? kb (list 'agg/count 2 '?v (list scoreOf Team '?v)) 'CxWell))
    (is (not (v/ask? kb (list 'agg/count 3 '?v (list scoreOf Team '?v)) 'CxWell))
        "a bound ?n that does not match the computed value answers nothing")))

;; ---- the empty body: where the five differ -------------------------------

(tu/deftest-kb count-and-sum-answer-over-nothing-the-others-do-not
  (tu/with-terms [scoreOf Nobody]
    (let [g (fn [op] (list op '?n '?v (list scoreOf Nobody '?v)))]
      (is (= 0 (one kb (g 'agg/count) '?n)) "count of an empty group is 0")
      (is (= 0 (one kb (g 'agg/sum) '?n)) "sum of an empty group is 0 — the identity")
      (testing "min / max / avg over nothing have no answer — not nil, not zero"
        (doseq [op '[agg/min agg/max agg/avg]]
          (is (empty? (v/ask kb (g op) 'CxWell))
              (str op " must yield no binding at all over an empty body")))))))

;; ---- numbers, measures, and what is neither ------------------------------

(tu/deftest-kb a-non-numeric-value-is-an-error-not-a-silent-skip
  (tu/with-terms [likesThing Ann Cake Pie]
    (v/assert kb (list likesThing Ann Cake) 'CxWell)
    (v/assert kb (list likesThing Ann Pie) 'CxWell)
    (v/clear-violations! kb)
    (let [g (fn [op] (list op '?n '?v (list likesThing Ann '?v)))]
      (is (= 2 (one kb (g 'agg/count) '?n))
          "counting is the one reduction that never reads the values")
      (doseq [op '[agg/sum agg/min agg/max agg/avg]]
        (is (empty? (v/ask kb (g op) 'CxWell)) (str op " cannot reduce symbols")))
      (let [vs (filter #(= :aggregate (:violation %)) (v/violations kb))]
        (is (= 4 (count vs)) "each refusal is recorded, not swallowed")
        (is (every? #(str/includes? (:message %) "numbers or measures") vs))))))

(tu/deftest-kb a-measure-sum-is-normalized-and-rendered-in-the-base-unit
  (tu/with-terms [lengthOf Wall Metre Centimetre Length]
    ;; CxMeasure ships the vocabulary; the units themselves are an ontology's
    (v/assert kb (list 'dimensionOf Metre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list 'dimensionOf Centimetre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list 'conversionFactor Centimetre Metre 0.01) 'CxWell
              {:strength :monotonic})
    (v/assert kb (list lengthOf Wall (list 'QuantityFn 300 Centimetre)) 'CxWell)
    (v/assert kb (list lengthOf Wall (list 'QuantityFn 2 Metre)) 'CxWell)
    (is (= (list 'QuantityFn 5 Metre)
           (one kb (list 'agg/sum '?n '?v (list lengthOf Wall '?v)) '?n))
        "converted to base units, added there, and rendered back in the same unit")))

(tu/deftest-kb an-interval-measure-carries-through-sum-and-stops-min
  (tu/with-terms [spanOf Trip Metre Length]
    (v/assert kb (list 'dimensionOf Metre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list spanOf Trip (list 'QuantityIntervalFn 1 3 Metre)) 'CxWell)
    (v/assert kb (list spanOf Trip (list 'QuantityFn 10 Metre)) 'CxWell)
    (v/clear-violations! kb)
    (is (= (list 'QuantityIntervalFn 11 13 Metre)
           (one kb (list 'agg/sum '?n '?v (list spanOf Trip '?v)) '?n))
        "an over-approximation in is an over-approximation out, said out loud")
    (testing "min and max need a total order, which interval bounds do not give"
      (doseq [op '[agg/min agg/max]]
        (is (empty? (v/ask kb (list op '?n '?v (list spanOf Trip '?v)) 'CxWell))))
      (is (= 2 (count (filter #(str/includes? (str (:message %)) "partially ordered")
                              (v/violations kb))))
          "refused with the reason, not silently"))))

(tu/deftest-kb point-measures-do-order-so-min-and-max-answer
  (tu/with-terms [spanOf Trip Metre Centimetre Length]
    (v/assert kb (list 'dimensionOf Metre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list 'dimensionOf Centimetre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list 'conversionFactor Centimetre Metre 0.01) 'CxWell
              {:strength :monotonic})
    (v/assert kb (list spanOf Trip (list 'QuantityFn 250 Centimetre)) 'CxWell)
    (v/assert kb (list spanOf Trip (list 'QuantityFn 4 Metre)) 'CxWell)
    (is (= (list 'QuantityFn 2.5 Metre)
           (one kb (list 'agg/min '?n '?v (list spanOf Trip '?v)) '?n))
        "compared in base units, so the smaller is the one with the smaller magnitude *there*")
    (is (= (list 'QuantityFn 4 Metre)
           (one kb (list 'agg/max '?n '?v (list spanOf Trip '?v)) '?n)))))

(tu/deftest-kb a-measure-average-and-a-measure-checked-rather-than-bound
  (tu/with-terms [spanOf Trip Metre Length]
    (v/assert kb (list 'dimensionOf Metre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list spanOf Trip (list 'QuantityFn 2 Metre)) 'CxWell)
    (v/assert kb (list spanOf Trip (list 'QuantityFn 4 Metre)) 'CxWell)
    (is (= (list 'QuantityFn 3 Metre)
           (one kb (list 'agg/avg '?n '?v (list spanOf Trip '?v)) '?n))
        "the mean is linear in the bounds, so it renders as a point")
    (testing "check mode over a non-number compares the rendered measure"
      (is (v/ask? kb (list 'agg/avg (list 'QuantityFn 3 Metre) '?v
                           (list spanOf Trip '?v))
                  'CxWell))
      (is (not (v/ask? kb (list 'agg/avg (list 'QuantityFn 9 Metre) '?v
                                (list spanOf Trip '?v))
                       'CxWell))))))

(tu/deftest-kb the-reduction-slot-must-hold-a-variable
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [1 2])
    (is (empty? (v/ask kb (list 'agg/count '?n 7 (list scoreOf Team 7)) 'CxWell))
        "a constant reduces over nothing — there is no variable to collect")
    (testing "and in a rule it is refused, not stored as a rule that can never fire"
      (tu/with-terms [tallied]
        (let [e (try (v/assert kb (list 'implies
                                        (list 'and (list scoreOf Team '?s)
                                              (list 'agg/count '?n 7 (list scoreOf Team 7)))
                                        (list tallied Team '?n))
                               'CxWell {:direction :forward})
                     nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e) "a silently unfirable rule is the one outcome worse than an error")
          (is (= :not-well-formed (:type (ex-data e))))
          (is (str/includes? (ex-message e) "not a variable")))))))

(tu/deftest-kb a-mixed-dimension-extent-is-refused-rather-than-added
  (tu/with-terms [measureOf Thing Metre Sec Length Duration]
    (v/assert kb (list 'dimensionOf Metre Length) 'CxWell {:strength :monotonic})
    (v/assert kb (list 'dimensionOf Sec Duration) 'CxWell {:strength :monotonic})
    (v/assert kb (list measureOf Thing (list 'QuantityFn 2 Metre)) 'CxWell)
    (v/assert kb (list measureOf Thing (list 'QuantityFn 3 Sec)) 'CxWell)
    (v/clear-violations! kb)
    (is (empty? (v/ask kb (list 'agg/sum '?n '?v (list measureOf Thing '?v)) 'CxWell))
        "metres plus seconds is not a sum")
    (is (seq (filter #(= :aggregate (:violation %)) (v/violations kb))))))

;; ---- not assertible ------------------------------------------------------

(tu/deftest-kb none-of-the-five-is-assertible
  (tu/with-terms [scoreOf Team]
    (doseq [f (keys sx/aggregate-functors)]
      ;; ground, so the refusal is the wff arm's rather than the ground check's — an
      ;; aggregate written the ordinary way is refused twice over
      (let [e (try (v/assert kb (list f 1 Team (list scoreOf Team 1)) 'CxWell)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) (str f " must be refused as a stored fact"))
        (is (= :not-well-formed (:type (ex-data e))))
        (is (str/includes? (ex-message e) (str f " is not assertible"))
            "the message names the query form, as unknown's and different's do")))
    (testing "and the open form an author would actually write is refused too"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'agg/count 1 '?v (list scoreOf Team '?v))
                             'CxWell))))))

;; ---- in a rule antecedent: grouping and maintenance ----------------------

(defn- ancestor-world!
  "A DAG with `(transitive ancestorOf)` and one node per element of `edges`' union, plus
  the grouping rule.  Hands back the vocabulary the tests drive."
  [kb {:keys [node ancestorOf ancestorCount edges]}]
  (v/assert kb (list 'transitive ancestorOf) 'CxWell {:strength :monotonic})
  (doseq [n (into #{} cat edges)] (v/assert kb (list node n) 'CxWell))
  (doseq [[a b] edges] (v/assert kb (list ancestorOf a b) 'CxWell))
  (v/assert kb (list 'implies
                     (list 'and (list node '?x)
                           (list 'agg/count '?n '?a (list ancestorOf '?a '?x)))
                     (list ancestorCount '?x '?n))
            'CxWell {:direction :forward}))

(defn- counted
  "`{node -> n}` from the believed `(ancestorCount ?x ?n)` facts."
  [kb ancestorCount]
  (into {} (map (fn [sx] (let [[_ x n] (:sentence sx)] [x n])))
        (v/sentexes-matching kb (list ancestorCount '?x '?n) 'CxWell)))

(tu/deftest-kb the-wagg-shape-per-node-transitive-ancestor-count
  (tu/with-terms [node ancestorOf ancestorCount A B C D E]
    ;; A -> B -> D,  A -> C -> D,  D -> E   (a diamond with a tail)
    (let [edges [[A B] [B D] [A C] [C D] [D E]]]
      (ancestor-world! kb {:node node :ancestorOf ancestorOf
                           :ancestorCount ancestorCount :edges edges})
      ;; the ancestor sets, computed independently of the engine
      (let [parents (reduce (fn [m [a b]] (update m b (fnil conj #{}) a)) {} edges)
            ancs    (fn ancs [x] (into #{} (mapcat #(conj (ancs %) %)) (parents x)))
            want    (into {} (for [n [A B C D E]] [n (count (ancs n))]))]
        (is (= {A 0 B 1 C 1 D 3 E 4} want) "the reference counts, by hand")
        (is (= want (counted kb ancestorCount))
            "one ?n per ?x — the grouping falls out of the binding discipline")))))

(tu/deftest-kb the-count-is-maintained-when-a-counted-fact-arrives-and-leaves
  (tu/with-terms [node ancestorOf ancestorCount P Q R]
    (ancestor-world! kb {:node node :ancestorOf ancestorOf
                         :ancestorCount ancestorCount :edges [[P Q]]})
    (v/assert kb (list node R) 'CxWell)
    (is (= {P 0 Q 1 R 0} (counted kb ancestorCount)) "the starting counts")
    (testing "assert: the old conclusion goes and the new one arrives"
      (let [h (v/assert kb (list ancestorOf R P) 'CxWell)]
        (is (= {P 1 Q 2 R 0} (counted kb ancestorCount))
            "R is an ancestor of P and, transitively, of Q")
        (testing "retract: and back, in the other direction"
          (v/retract! kb h)
          (is (= {P 0 Q 1 R 0} (counted kb ancestorCount))))))
    (testing "defeat: a believed (not …) withdraws the fact, so the count follows belief"
      (let [h (v/assert kb (list ancestorOf R P) 'CxWell {:strength :default})]
        (is (= {P 1 Q 2 R 0} (counted kb ancestorCount)))
        (let [d (v/assert kb (list 'not (list ancestorOf R P)) 'CxWell
                          {:strength :monotonic})]
          (is (not (v/in? kb h)) "the stronger negation defeats the fact")
          (is (= {P 0 Q 1 R 0} (counted kb ancestorCount))
              "a defeated fact is stored but not believed, so it is not counted")
          (v/retract! kb d)
          (is (v/in? kb h) "the fact revives...")
          (is (= {P 1 Q 2 R 0} (counted kb ancestorCount)) "...and so does the count"))))))

(tu/deftest-kb an-aggregate-with-an-unbound-grouping-variable-is-refused
  (tu/with-terms [node ancestorOf ancestorCount]
    (let [e (try (v/assert kb (list 'implies
                                    (list 'and (list 'agg/count '?n '?a
                                                     (list ancestorOf '?a '?x)))
                                    (list ancestorCount '?x '?n))
                           'CxWell {:direction :forward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :naf-not-closed (:type (ex-data e)))
          "the same diagnostic an unclosed unknown gives")
      (is (str/includes? (ex-message e) "not closed")))))

(tu/deftest-kb the-reduction-variable-may-not-escape-into-the-consequent
  (tu/with-terms [node ancestorOf sawAncestor]
    (let [e (try (v/assert kb (list 'implies
                                    (list 'and (list node '?x)
                                          (list 'agg/count '?n '?a
                                                (list ancestorOf '?a '?x)))
                                    (list sawAncestor '?x '?a))
                           'CxWell {:direction :forward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :quantifier-not-local (:type (ex-data e)))
          "?a is projected out, so a consequent naming it would store a non-ground fact"))))

;; ---- the census body is joined -------------------------------------------
;; A conjunctive body is one query whose conjuncts share the reduction variable — the
;; same join `unknown` and `exceptWhen` read.  "How many of Bob's children are asleep"
;; is one witness satisfying both conjuncts, never the children counted beside the
;; sleepers.

(defn- sleepy-house!
  "Bob, three children, two of them asleep, and a sleeping stranger who is nobody's
  child.  Read conjunct by conjunct the count would be three children or three
  sleepers; joined it is two."
  [kb {:keys [person childOf asleep Bob Kid1 Kid2 Kid3 Stranger]}]
  (v/assert kb (list person Bob) 'CxWell)
  (doseq [k [Kid1 Kid2 Kid3]] (v/assert kb (list childOf Bob k) 'CxWell))
  (v/assert kb (list asleep Kid1) 'CxWell)
  (v/assert kb (list asleep Stranger) 'CxWell)
  (v/assert kb (list asleep Kid2) 'CxWell))

(defn- asleep-children
  "The census `(agg/count ?n ?c (and (childOf ?x ?c) (asleep ?c)))`, for `?x`."
  [childOf asleep x]
  (list 'agg/count '?n '?c (list 'and (list childOf x '?c) (list asleep '?c))))

(tu/deftest-kb how-many-of-bob-s-children-are-asleep
  (tu/with-terms [person childOf asleep Bob Kid1 Kid2 Kid3 Stranger]
    (sleepy-house! kb {:person person :childOf childOf :asleep asleep :Bob Bob
                       :Kid1 Kid1 :Kid2 Kid2 :Kid3 Kid3 :Stranger Stranger})
    (is (= 2 (one kb (asleep-children childOf asleep Bob) '?n))
        "two — not the three children, and not the three who are asleep")
    (testing "and the conjuncts are joined rather than read flat"
      (is (= 3 (one kb (list 'agg/count '?n '?c (list childOf Bob '?c)) '?n)))
      (is (= 3 (one kb (list 'agg/count '?n '?c (list asleep '?c)) '?n))))))

(defn- restful!
  "The rule *a parent with more than one sleeping child is restful*, over the joined
  census."
  [kb {:keys [person childOf asleep restful]}]
  (v/assert kb (list 'implies
                     (list 'and (list person '?x)
                           (asleep-children childOf asleep '?x)
                           (list 'lessThan 1 '?n))
                     (list restful '?x))
            'CxWell {:direction :forward}))

(tu/deftest-kb a-child-waking-lowers-the-joined-count-and-withdraws-the-firing
  (tu/with-terms [person childOf asleep restful Bob Kid1 Kid2 Kid3 Stranger]
    (let [world {:person person :childOf childOf :asleep asleep :Bob Bob
                 :Kid1 Kid1 :Kid2 Kid2 :Kid3 Kid3 :Stranger Stranger}]
      (restful! kb (assoc world :restful restful))
      (sleepy-house! kb world)
      (is (v/ask? kb (list restful Bob) 'CxWell)
          "two of Bob's children are asleep, so the rule fires")
      (testing "a child wakes: the count falls to one and the conclusion goes with it"
        (let [awake (v/assert kb (list 'not (list asleep Kid2)) 'CxWell
                              {:strength :monotonic})]
          (is (= 1 (one kb (asleep-children childOf asleep Bob) '?n))
              "the second conjunct's predicate is watched, so the census is re-taken")
          (is (not (v/ask? kb (list restful Bob) 'CxWell)))
          (is (nil? (v/handle-of kb (list restful Bob) 'CxWell))
              "withdrawn, not merely disbelieved")
          (testing "and retracting the waking restores both"
            (v/retract! kb awake)
            (is (= 2 (one kb (asleep-children childOf asleep Bob) '?n)))
            (is (v/ask? kb (list restful Bob) 'CxWell))))))))

(tu/deftest-kb the-joined-census-reads-the-same-in-either-arrival-order
  ;; the rule before the facts, and the facts before the rule: a joined census is
  ;; maintained by re-joining on arrival, so an order-sensitive re-check shows up here.
  ;; Each arm gets its own cast, so the second reads a baseline the first did not move.
  (doseq [[label rule-first?] [["rule first" true] ["facts first" false]]]
    (testing label
      (tu/with-terms [person childOf asleep restful Bob Kid1 Kid2 Kid3 Stranger]
        (let [world  {:person person :childOf childOf :asleep asleep :Bob Bob
                      :Kid1 Kid1 :Kid2 Kid2 :Kid3 Kid3 :Stranger Stranger}
              rule!  #(restful! kb (assoc world :restful restful))
              facts! #(sleepy-house! kb world)]
          (if rule-first? (do (rule!) (facts!)) (do (facts!) (rule!)))
          (is (= 2 (one kb (asleep-children childOf asleep Bob) '?n)))
          (is (v/ask? kb (list restful Bob) 'CxWell)))))))

(tu/deftest-kb a-sum-joins-its-census-over-a-variable-local-to-the-body
  ;; the natural shape of a summed join: `?p` is the join between the two conjuncts and
  ;; is named nowhere else, so the census binds it itself.  Distinct values, as ever —
  ;; the parcels are given different weights so the sum is of all three.
  (tu/with-terms [carries weightOf Bob Parcel1 Parcel2 Parcel3 Crate]
    (doseq [p [Parcel1 Parcel2 Parcel3]] (v/assert kb (list carries Bob p) 'CxWell))
    (doseq [[p w] [[Parcel1 2] [Parcel2 3] [Parcel3 5] [Crate 7]]]
      (v/assert kb (list weightOf p w) 'CxWell))
    (let [g (list 'agg/sum '?n '?w (list 'and (list carries Bob '?p)
                                         (list weightOf '?p '?w)))]
      (is (= 10 (one kb g '?n))
          "the parcels Bob carries — the crate he does not is not in the join"))))

(tu/deftest-kb every-conjunct-of-a-census-is-a-negative-edge-for-stratification
  ;; the single-literal body's rule, read through the join: a conclusion reached from a
  ;; count over it has no settled answer whichever conjunct mentions it.
  (tu/with-terms [node kidOf bigGroup]
    (let [e (try (v/assert kb (list 'implies
                                    (list 'and (list node '?x)
                                          (list 'agg/count '?n '?a
                                                (list 'and (list kidOf '?x '?a)
                                                      (list bigGroup '?a))))
                                    (list bigGroup '?x))
                           'CxWell {:direction :forward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :not-stratified (:type (ex-data e)))
          "the cycle runs through the census's *second* conjunct"))))

;; ---- where the census is taken -------------------------------------------
;; The aggregate is evaluated per placement context, and it contributes no handles to
;; the join — so it is counted *where the conclusion lands* and has no say in where
;; that is.  Placement is decided entirely by the rule's other antecedents.  Both
;; halves of that are surprising the first time, and both are what makes one rule give
;; each context its own count.

(defn- counts-by-context
  [kb childCount]
  (into {} (map (fn [sx] [(:context sx) (nth (:sentence sx) 2)]))
        (v/sentexes-matching kb (list childCount '?x '?n) '?ctx)))

(defn- two-contexts!
  "`Left` and `Right` under `Root`, and the counting rule in `Root`."
  [kb {:keys [person childOf childCount Root Left Right]}]
  (doseq [c [Left Right]]
    (v/assert kb (list 'genlCx c Root) 'CxUniverse {:strength :monotonic}))
  (v/assert kb (list 'implies
                     (list 'and (list person '?x)
                           (list 'agg/count '?n '?c (list childOf '?x '?c)))
                     (list childCount '?x '?n))
            Root {:direction :forward}))

(tu/deftest-kb each-context-counts-what-it-sees-and-the-aggregate-does-not-place
  (tu/with-terms [person childOf childCount Ann CxRoot CxLeft CxRight]
    (let [world {:person person :childOf childOf :childCount childCount
                 :Root CxRoot :Left CxLeft :Right CxRight}]
      (two-contexts! kb world)
      (v/assert kb (list childOf Ann 'C1) CxLeft)
      (v/assert kb (list childOf Ann 'C2) CxLeft)
      (v/assert kb (list childOf Ann 'C3) CxRight)
      (testing "grouped on a fact only the root holds, the census is the root's"
        (v/assert kb (list person Ann) CxRoot)
        (is (= {CxRoot 0} (counts-by-context kb childCount))
            (str "the counted facts live below the placement, and the aggregate names no"
                 " handle — so it cannot pull the conclusion down to them")))
      (testing "grouped in each child, one firing per context with its own count"
        (v/assert kb (list person Ann) CxLeft)
        (v/assert kb (list person Ann) CxRight)
        (is (= {CxRoot 0 CxLeft 2 CxRight 1}
               (counts-by-context kb childCount))
            "one rule, three contexts, three answers")))))

(tu/deftest-kb the-counted-facts-are-not-in-the-justification
  ;; which is the whole reason `justification-excepted?` needs an arm of its own: the
  ;; antecedents name what the join matched, and a census matches nothing.  Retraction
  ;; still reaches the conclusion, through the re-check index rather than through
  ;; dependency-directed sweep.
  (tu/with-terms [person childOf childCount Ann CxRoot CxLeft CxRight]
    (two-contexts! kb {:person person :childOf childOf :childCount childCount
                       :Root CxRoot :Left CxLeft :Right CxRight})
    (v/assert kb (list person Ann) CxLeft)
    (v/assert kb (list childOf Ann 'C1) CxLeft)
    (let [h2 (v/assert kb (list childOf Ann 'C2) CxLeft)]
      (is (= {CxLeft 2} (counts-by-context kb childCount)))
      (let [h    (v/handle-of kb (list childCount Ann 2) CxLeft)
            why  (v/why kb h)
            cited (into #{} (map :sentence)
                        (mapcat :because (:support why)))]
        (is (= #{(list person Ann) (list 'genlCx CxLeft CxRoot)} cited)
            "the grouping fact and the edge the placement saw the rule over — no child is named")
        (is (not (contains? cited (list childOf Ann 'C1)))))
      (testing "and retracting a counted fact moves the count regardless"
        (v/retract! kb h2)
        (is (= {CxLeft 1} (counts-by-context kb childCount)))))))

;; ---- what a count is *for*: comparing it ---------------------------------
;; An aggregate is evaluated per placement context, so its `?n` is unbound for the
;; whole join — and a comparison on `?n` is a computed literal, not a matched one, so
;; there is no fact for it to wait on.  Both move to the placement phase together
;; (`rules/post-join-literals`).  Without that the most obvious question anyone would
;; ask of a count cannot be written at all.

(defn- family!
  "Two people, one with three children and one with one."
  [kb {:keys [person childOf Ann Bob]}]
  (doseq [p [Ann Bob]] (v/assert kb (list person p) 'CxWell))
  (doseq [c ['C1 'C2 'C3]] (v/assert kb (list childOf Ann c) 'CxWell))
  (v/assert kb (list childOf Bob 'B1) 'CxWell))

(defn- holders
  "The individuals a unary conclusion is believed of."
  [kb pred]
  (into #{} (map (comp second :sentence)) (v/sentexes-matching kb (list pred '?x) 'CxWell)))

(tu/deftest-kb a-person-with-more-than-two-children
  (tu/with-terms [person childOf large_family Ann Bob]
    (let [world {:person person :childOf childOf :Ann Ann :Bob Bob}]
      (family! kb world)
      (v/assert kb (list 'implies
                         (list 'and (list person '?x)
                               (list 'agg/count '?n '?c (list childOf '?x '?c))
                               (list 'lessThan 2 '?n))
                         (list large_family '?x))
                'CxWell {:direction :forward})
      (is (= #{Ann} (holders kb large_family))
          "three children clears the bar and one does not")
      (testing "and the comparison is maintained against the count, both ways"
        (let [h1 (v/assert kb (list childOf Bob 'B2) 'CxWell)
              h2 (v/assert kb (list childOf Bob 'B3) 'CxWell)]
          (is (= #{Ann Bob} (holders kb large_family))
              "Bob crosses the threshold with no fact naming the conclusion")
          (v/retract! kb h2)
          (is (= #{Ann} (holders kb large_family))
              "and falls back below it — the firing rested on a count that moved")
          (v/retract! kb h1))))))

(tu/deftest-kb the-comparison-is-written-below-its-own-aggregate-or-refused
  ;; A computed literal reads what is written before it — the rule an `evaluate` chain
  ;; has always followed, since canonical order holds a deferred literal where the
  ;; author put it.  An aggregate could have been made an exception by reordering the
  ;; placement phase, and deliberately was not: the *forward* chainer can reorder that
  ;; phase and the backward one cannot, so the exception would buy one writing order at
  ;; the price of the two chainers disagreeing about one rule.
  (tu/with-terms [person childOf large_family Ann Bob]
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (let [e (try (v/assert kb (list 'implies
                                    (list 'and (list person '?x)
                                          (list 'lessThan 2 '?n)
                                          (list 'agg/count '?n '?c (list childOf '?x '?c)))
                                    (list large_family '?x))
                           'CxWell {:direction :forward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "the comparison is above the only thing that writes ?n")
      (is (= :naf-not-closed (:type (ex-data e))))
      (is (= '[?n] (:unbound (ex-data e)))))))

(tu/deftest-kb a-backward-only-rule-answers-a-compared-count-the-same-way
  ;; the parity above reads the *stored* conclusion, which forward chaining put there —
  ;; so it cannot see a backward chainer that disagrees.  A `set/backwardRule` never
  ;; fires forward, so its conclusion exists only while a backchainer is looking for it.
  (tu/with-terms [person childOf large_family Ann Bob]
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (v/assert kb (list 'set/backwardRule
                       (list 'implies
                             (list 'and (list person '?x)
                                   (list 'agg/count '?n '?c (list childOf '?x '?c))
                                   (list 'lessThan 2 '?n))
                             (list large_family '?x)))
              'CxWell)
    (is (empty? (holders kb large_family)) "nothing is stored — it never fires forward")
    (is (v/query? kb (list large_family Ann) 'CxWell {:max-depth 2}))
    (is (not (v/query? kb (list large_family Bob) 'CxWell {:max-depth 2})))))

(tu/deftest-kb forward-and-backward-agree-about-a-compared-count
  ;; the parity `provers/exception-holds?` exists to guarantee, asked of the structure that
  ;; breaks it first: a forward throw where backward answers
  (tu/with-terms [person childOf large_family Ann Bob]
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'agg/count '?n '?c (list childOf '?x '?c))
                             (list 'lessThan 2 '?n))
                       (list large_family '?x))
              'CxWell {:direction :forward})
    (is (= #{Ann} (holders kb large_family))            "forward")
    (is (v/ask? kb (list large_family Ann) 'CxWell)        "ask, yes")
    (is (not (v/ask? kb (list large_family Bob) 'CxWell))  "ask, no")
    (is (seq (v/prove kb (list large_family Ann) 'CxWell)) "prove, yes")
    (is (empty? (v/prove kb (list large_family Bob) 'CxWell)) "prove, no")))

(tu/deftest-kb a-computed-literal-carries-a-later-one-along-with-it
  ;; the chain is aggregate -> evaluate -> comparison: `?d` is written by a literal that
  ;; is itself downstream of the count, so it moves to the placement phase too
  (tu/with-terms [person childOf roomFor Ann Bob]
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'agg/count '?n '?c (list childOf '?x '?c))
                             (list 'evaluate '?d (list '+ '?n 1))
                             (list 'lessThan 3 '?d))
                       (list roomFor '?x '?d))
              'CxWell {:direction :forward})
    (is (= [(list roomFor Ann 4)]
           (map :sentence (v/sentexes-matching kb (list roomFor '?x '?d) 'CxWell)))
        "?d reaches the consequent, and the comparison on it decides the firing")))

(tu/deftest-kb an-unknown-may-read-a-count
  (tu/with-terms [person childOf banned allowed Ann Bob]
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'agg/count '?n '?c (list childOf '?x '?c))
                             (list 'unknown (list banned '?n)))
                       (list allowed '?x))
              'CxWell {:direction :forward})
    (is (= #{Ann Bob} (holders kb allowed)) "nothing is banned yet")
    (let [h (v/assert kb (list banned 3) 'CxWell)]
      (is (= #{Bob} (holders kb allowed))
          "banning the count Ann's group has withdraws her conclusion")
      (v/retract! kb h))
    (is (= #{Ann Bob} (holders kb allowed)) "and gives it back")))

(tu/deftest-kb a-computed-literal-nothing-can-bind-is-refused-before-it-is-stored
  ;; the join throws on a deferred literal with an unbound input — deliberately, since
  ;; an empty join would report a comparison that never ran as one that failed.  But a
  ;; throw *mid-fixpoint* is what the derivation path must not do: the rule is already
  ;; stored by then, so every later assert re-fires it and throws again.  Refusing at
  ;; assert time is the same diagnosis delivered where it can still be acted on.
  (tu/with-terms [person big Ann]
    (v/assert kb (list person Ann) 'CxWell)
    (let [before (v/sentex-count kb)
          e (try (v/assert kb (list 'implies
                                    (list 'and (list person '?x) (list 'lessThan 2 '?n))
                                    (list big '?x))
                           'CxWell {:direction :forward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "?n is written by nothing in the rule")
      (is (= :naf-not-closed (:type (ex-data e))))
      (is (= '[?n] (:unbound (ex-data e))))
      (testing "and the KB is untouched, so the next write still works"
        ;; the refusal is at canonicalization, so there is no sentex to look the rule
        ;; up by — `handle-of` would have to build the very form that is refused
        (is (= before (v/sentex-count kb)) "a refused rule stores nothing")
        (is (some? (v/assert kb (list person 'Zed) 'CxWell)))))))

;; ---- stratification ------------------------------------------------------

(tu/deftest-kb an-aggregate-over-what-the-rule-concludes-is-refused
  (tu/with-terms [node bigGroup]
    (let [e (try (v/assert kb (list 'implies
                                    (list 'and (list node '?x)
                                          (list 'agg/count '?n '?a
                                                (list bigGroup '?a)))
                                    (list bigGroup '?x))
                           'CxWell {:direction :forward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :not-stratified (:type (ex-data e)))
          "counting a relation the rule itself concludes has no settled answer"))))

;; ---- the cost tier is honest ---------------------------------------------

(tu/deftest-kb a-lookup-budget-drops-the-aggregate-and-compute-admits-it
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [1 2 3])
    (let [g (list 'agg/count '?n '?v (list scoreOf Team '?v))]
      (is (empty? (:results (v/ask-within kb g 'CxWell {:max-cost :lookup})))
          "a reduction must exhaust the body, which :lookup does not buy")
      (is (= 1 (count (:results (v/ask-within kb g 'CxWell {:max-cost :compute}))))
          ":compute is the tier it declares, and it runs there"))))

(tu/deftest-kb a-lookup-budget-keeps-unknown-rather-than-inverting-it
  ;; `unknown` shares the `:compute` tier with the aggregate, but unlike it, dropping its
  ;; prover does not merely under-report — it INVERTS the closed-world answer: an empty
  ;; result for `(unknown S)` reads as "S is derivable".  So it is kept past the cap, and
  ;; a `:lookup` budget answers the same as no budget, `:complete` and correct.
  (tu/with-terms [flies Tweety]
    (let [g (list 'unknown (list flies Tweety))]     ; nothing derives (flies Tweety)
      (is (v/ask? kb g 'CxWell) "S is not derivable, so (unknown S) holds")
      (let [r (v/ask-within kb g 'CxWell {:max-cost :lookup})]
        (is (seq (:results r)) "the lookup budget keeps UnknownProver, not an inverted empty")
        (is (= :complete (:status r)))))))

;; ---- nothing is stored ---------------------------------------------------

(tu/deftest-kb asking-an-aggregate-stores-nothing-and-creates-no-node
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [1 2])
    (let [sentexes (tu/sentex-ids kb)
          justs    (tu/justification-ids kb)]
      (doseq [f (keys sx/aggregate-functors)]
        (v/ask kb (list f '?n '?v (list scoreOf Team '?v)) 'CxWell))
      (is (= sentexes (tu/sentex-ids kb)) "no sentex — a count is recomputed, never cached")
      (is (= justs (tu/justification-ids kb)) "and no justification"))))

;; ---- every chainer reaches it -------------------------------------------

(tu/deftest-kb the-backward-chainers-answer-an-aggregate-too
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [4 5 6])
    (let [g (list 'agg/count '?n '?v (list scoreOf Team '?v))]
      (is (= [3] (map '?n (v/prove kb g 'CxWell))) "prove: the recur DFS")
      (is (= [3] (map '?n (v/prove kb g 'CxWell))) "prove: the recursive one")
      (is (= [3] (map '?n (v/ask kb g 'CxWell))) "ask: the prover engine"))))

(tu/deftest-kb a-backward-rule-may-join-on-a-count
  (tu/with-terms [scoreOf Team roster tallied]
    (extent! kb scoreOf Team [1 2])
    (v/assert kb (list roster Team) 'CxWell)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies
                             (list 'and (list roster '?t)
                                   (list 'agg/count '?n '?v (list scoreOf '?t '?v)))
                             (list tallied '?t '?n)))
              'CxWell)
    (is (= [2] (map '?n (v/query kb (list tallied Team '?n) 'CxWell {:max-depth 2})))
        "a rule expansion discharges the aggregate through the registry like any other literal")))

;; ---- the doc's opening example, run rather than written ------------------

(tu/deftest-kb the-docs-opening-example
  ;; run, not written: the extent and all three answers exactly as docs/aggregate.md
  ;; prints them, so the page cannot drift from what the engine says
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [3 1 4 1 5])
    (let [g (fn [op] (list op '?n '?v (list scoreOf Team '?v)))]
      (is (= '({?n 4})    (v/ask kb (g 'agg/count) 'CxWell)))
      (is (= '({?n 13})   (v/ask kb (g 'agg/sum) 'CxWell)))
      (is (= '({?n 3.25}) (v/ask kb (g 'agg/avg) 'CxWell))))))

(tu/deftest-kb one-edit-and-n-asserts-reach-the-same-counts
  ;; the benchmark's headline claim (`lein bench-aggchain`, ~10x) is only worth
  ;; anything if the batch derives the same thing — one settle, not fewer answers
  (tu/with-terms [node ancestorOf ancestorCount A B C D]
    (let [edges [[A B] [B C] [C D]]]
      (ancestor-world! kb {:node node :ancestorOf ancestorOf
                           :ancestorCount ancestorCount :edges edges})
      (let [one-at-a-time (counted kb ancestorCount)]
        (doseq [[a b] edges] (v/retract! kb (v/handle-of kb (list ancestorOf a b) 'CxWell)))
        (is (= {A 0 B 0 C 0 D 0} (counted kb ancestorCount)) "back to an empty relation")
        (v/edit! kb {:add (mapv (fn [[a b]] [(list ancestorOf a b) 'CxWell]) edges)})
        (is (= one-at-a-time (counted kb ancestorCount))
            "the batch settles once and reaches the identical counts")))))

;; ---- the index is derived, so a rebuild must restore the maintenance ----

(tu/deftest-kb reindex-rebuilds-the-re-check-posting-an-aggregate-rule-needs
  ;; `reindex` rebuilds every index entry from the records, including the re-check
  ;; posting that brings an aggregate rule back when a counted fact moves.  If that
  ;; posting were dropped the counts would look right and then silently stop tracking
  (tu/with-terms [node ancestorOf ancestorCount P Q R]
    (ancestor-world! kb {:node node :ancestorOf ancestorOf
                         :ancestorCount ancestorCount :edges [[P Q]]})
    (v/assert kb (list node R) 'CxWell)
    (v/reindex kb)
    (is (= {P 0 Q 1 R 0} (counted kb ancestorCount)) "the conclusions survive the rebuild")
    (let [h (v/assert kb (list ancestorOf R P) 'CxWell)]
      (is (= {P 1 Q 2 R 0} (counted kb ancestorCount))
          "and the count still moves — the posting came back")
      (v/retract! kb h)
      (is (= {P 0 Q 1 R 0} (counted kb ancestorCount))))))

;; ---- nesting: what falls out for free -----------------------------------

(tu/deftest-kb an-aggregate-under-unknown-works-because-both-are-level-6
  ;; not designed for, but not excluded either: `unknown` runs its argument through
  ;; the same level-6 list the aggregate is registered in
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [1 2])
    (is (v/ask? kb (list 'unknown (list 'agg/count 9 '?v (list scoreOf Team '?v)))
                'CxWell)
        "the count is not 9, so the check fails, so the unknown holds")
    (is (not (v/ask? kb (list 'unknown (list 'agg/count 2 '?v (list scoreOf Team '?v)))
                     'CxWell))
        "the count *is* 2, so the check holds, so the unknown does not")))

(tu/deftest-kb an-unknown-over-aggregate-rechecks-on-the-body-s-predicate
  ;; the rule's re-check keys are the body's functor, not `agg/count` — a functor no
  ;; fact ever carries, so a rule keyed on it would never be re-checked and the
  ;; conclusion drawn at the old census would stay believed whatever arrived
  (tu/with-terms [childOf soloChildIn Ana Bo Cy]
    (v/assert kb (list 'implies
                       (list 'and (list childOf '?c '?x)
                             (list 'unknown (list 'agg/count 2 '?v (list childOf '?v '?x))))
                       (list soloChildIn '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list childOf Bo Ana) 'CxWell)
    (is (v/ask? kb (list soloChildIn Ana) 'CxWell)
        "one child: the count is not 2, the unknown holds, the rule concludes")
    (v/assert kb (list childOf Cy Ana) 'CxWell)
    (is (not (v/ask? kb (list soloChildIn Ana) 'CxWell))
        "two children: the arriving fact re-checks the rule and the conclusion is
        withdrawn, rather than kept on the census it was drawn at")))

;; ---- what level 6 does and does not reach --------------------------------

(tu/deftest-kb a-forward-derived-fact-is-counted
  ;; level 6 is not "stored facts only": a forward conclusion is stored and believed by
  ;; the time the query runs, so it is in the census like anything else
  (tu/with-terms [raw cooked burnt]
    (v/assert kb (list 'implies (list 'and (list raw '?x)) (list cooked '?x)) 'CxWell {:direction :forward})
    (doseq [n [1 2 3]] (v/assert kb (list raw (list 'DishFn n)) 'CxWell))
    (is (= 3 (one kb (list 'agg/count '?n '?v (list cooked '?v)) '?n))
        "nobody asserted a single (cooked …) and all three are counted")
    (is (= 0 (one kb (list 'agg/count '?n '?v (list burnt '?v)) '?n))
        "and a predicate nothing derives counts nothing, rather than failing")))

(tu/deftest-kb a-backward-only-conclusion-is-not-counted
  ;; the boundary, stated as a limitation rather than discovered as a surprise: a
  ;; `set/backwardRule` derives nothing until asked, and the body cannot ask
  (tu/with-terms [raw cooked]
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list raw '?x)) (list cooked '?x)))
              'CxWell)
    (doseq [n [1 2 3]] (v/assert kb (list raw (list 'DishFn n)) 'CxWell))
    (is (v/query? kb (list cooked '(DishFn 1)) 'CxWell {:max-depth 2})
        "backward chaining answers it goal by goal...")
    (is (= 0 (one kb (list 'agg/count '?n '?v (list cooked '?v)) '?n))
        "...but an aggregate body runs the registry, which expands no rule, so the
         census is empty")))

;; ---- the aggregate cannot outrun its binders, however it is written ------

(tu/deftest-kb writing-the-aggregate-first-does-not-run-it-first
  ;; canonical antecedent order holds deferred literals back, so the rule behaves
  ;; identically to the one with the generator written first — otherwise the aggregate
  ;; would run open and count the whole relation for every node
  (tu/with-terms [node ancestorOf ancestorCount A B C]
    (v/assert kb (list 'transitive ancestorOf) 'CxWell {:strength :monotonic})
    (doseq [n [A B C]] (v/assert kb (list node n) 'CxWell))
    (v/assert kb (list ancestorOf A B) 'CxWell)
    (v/assert kb (list ancestorOf B C) 'CxWell)
    (v/assert kb (list 'implies
                       (list 'and
                             (list 'agg/count '?n '?a (list ancestorOf '?a '?x))
                             (list node '?x))
                       (list ancestorCount '?x '?n))
              'CxWell {:direction :forward})
    (is (= {A 0 B 1 C 2} (counted kb ancestorCount))
        "grouped per node, exactly as if the generator had been written first")))

;; ---- order independence --------------------------------------------------

(defn- permutations [coll]
  (if (< (count coll) 2)
    [coll]
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

(tu/deftest-kb the-counts-do-not-depend-on-the-order-the-facts-arrived
  ;; the engine's central invariant, and an aggregate is the shape most likely to
  ;; break it: a count is a function of belief and it is maintained by re-joining on
  ;; arrival, so an order-sensitive re-join would show up here and nowhere else.
  ;; Each ordering gets its own gensym'd cast, and the answer is keyed by the node's
  ;; *role* rather than by the term, so two runs are comparable at all
  (let [answers
        (for [perm (permutations [[:a :b] [:b :c] [:c :d] [:a :d]])]
          (tu/with-terms [node ancestorOf ancestorCount A B C D]
            (let [term  {:a A :b B :c C :d D}
                  role  (into {} (map (fn [[k v]] [v k])) term)
                  edges (mapv (fn [[x y]] [(term x) (term y)]) perm)]
              (ancestor-world! kb {:node node :ancestorOf ancestorOf
                                   :ancestorCount ancestorCount :edges edges})
              (into {} (map (fn [[t n]] [(role t) n])) (counted kb ancestorCount)))))]
    (is (= 24 (count answers)) "every permutation of the four edges")
    (is (= 1 (count (distinct answers)))
        (str "one answer, whatever the order — got " (pr-str (distinct answers))))
    (is (= {:a 0 :b 1 :c 2 :d 3} (first answers)))))

(defn- counting-rule!
  "`(person ?x) & count > 2 => (large_family ?x)`, in `CxWell`."
  [kb {:keys [person childOf large_family]}]
  (v/assert kb (list 'implies
                     (list 'and (list person '?x)
                           (list 'agg/count '?n '?c (list childOf '?x '?c))
                           (list 'lessThan 2 '?n))
                     (list large_family '?x))
            'CxWell {:direction :forward}))

(tu/deftest-kb a-merge-that-collapses-two-counted-values-withdraws-the-firing
  ;; The census-mover that is **not** a fact arriving or leaving.  A merge retires a
  ;; spelling rather than removing it — the sentex is still stored and still holds its
  ;; handle — so no arm reports a fact moving on the counted predicate, and yet it is
  ;; gone from the belief-filtered read the census is.  Belief must not depend on whether
  ;; the count fell by retraction or by merge.
  (tu/with-terms [person childOf large_family Ann Bob]
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (counting-rule! kb {:person person :childOf childOf :large_family large_family})
    (is (= #{Ann} (holders kb large_family)) "three children clears the bar")
    (let [h (v/assert kb '(sameAs C2 C3) 'CxWell)]
      (is (= 2 (one kb (list 'agg/count '?n '?c (list childOf Ann '?c)) '?n))
          "two of the three children are one thing now")
      (is (= #{} (holders kb large_family))
          "so the firing that rested on three is withdrawn")
      (v/retract! kb h)
      (is (= 3 (one kb (list 'agg/count '?n '?c (list childOf Ann '?c)) '?n)))
      (is (= #{Ann} (holders kb large_family))
          "and splitting the class again re-derives it — the count rose, which licenses
           a firing no block ever suppressed"))))

(tu/deftest-kb the-merge-arriving-first-reaches-the-same-belief
  ;; the oracle for the test above.  Merged first, no trigger is involved at all: the
  ;; census is 2 the first time it is ever taken and the rule simply does not fire.
  (tu/with-terms [person childOf large_family Ann Bob]
    (v/assert kb '(sameAs C2 C3) 'CxWell)
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (counting-rule! kb {:person person :childOf childOf :large_family large_family})
    (is (= #{} (holders kb large_family))
        "merged first, three children are two values and the rule never fires")))

(tu/deftest-kb an-equality-the-engine-derives-moves-a-census-the-same-way
  ;; `functional` infers an equality rather than throwing, so a merge can arrive with no
  ;; `sameAs` anywhere in the KB.  It reaches the closure through the same arm an
  ;; asserted one does, and so must reach the same re-check.
  (tu/with-terms [person childOf large_family birthOrder Ann Bob]
    (v/assert kb (list 'functional birthOrder) 'CxWell)
    (family! kb {:person person :childOf childOf :Ann Ann :Bob Bob})
    (counting-rule! kb {:person person :childOf childOf :large_family large_family})
    (is (= #{Ann} (holders kb large_family)))
    (v/assert kb (list birthOrder Ann 'C2) 'CxWell)
    (v/assert kb (list birthOrder Ann 'C3) 'CxWell)
    (is (= 2 (one kb (list 'agg/count '?n '?c (list childOf Ann '?c)) '?n))
        "a functional predicate with two values makes them one thing")
    (is (= #{} (holders kb large_family))
        "and the firing that rested on three goes with it")))

(tu/deftest-kb a-float-sum-does-not-depend-on-the-order-the-facts-arrived
  ;; counting is exact whatever the order, so the permutation test above cannot see
  ;; this: floating-point addition is not associative, and the values reach the
  ;; reduction in *solution* order, which is a function of how the facts were stored
  ;; rather than of what they say.  These six sum to three different doubles depending
  ;; on where the two large terms fall, so a reduction in arrival order reports a
  ;; different total for the same KB.
  (let [vals   [0.1 0.2 0.3 1e16 -1e16 7.7]
        totals (for [order [vals (reverse vals) [1e16 0.1 -1e16 7.7 0.3 0.2]]]
                 (tu/with-terms [reading Sensor]
                   (doseq [x order] (v/assert kb (list reading Sensor x) 'CxWell))
                   [(one kb (list 'agg/sum '?n '?v (list reading Sensor '?v)) '?n)
                    (one kb (list 'agg/avg '?n '?v (list reading Sensor '?v)) '?n)]))]
    (is (= 1 (count (distinct totals)))
        (str "one total, whatever the order — got " (pr-str (distinct totals))))
    (is (not= (reduce + vals) (reduce + (reverse vals)))
        "and the values really are order-sensitive, so the test is testing something")))

(tu/deftest-kb one-error-is-filed-once-however-often-it-is-recomputed
  ;; a count is recomputed and never cached, so a bad extent is reduced again on every
  ;; query and every settle pass.  The ledger keeps its newest 1000 entries, so filing
  ;; each one would evict the derivation-path drops it exists to report.
  (tu/with-terms [likesThing Ann Cake Pie]
    (v/assert kb (list likesThing Ann Cake) 'CxWell)
    (v/assert kb (list likesThing Ann Pie) 'CxWell)
    (v/clear-violations! kb)
    (dotimes [_ 12] (v/ask kb (list 'agg/sum '?n '?v (list likesThing Ann '?v)) 'CxWell))
    (is (= 1 (count (filter #(= :aggregate (:violation %)) (v/violations kb))))
        "twelve reductions of one bad extent are one defect")))

;; ---- a post-join literal that answers two ways answers nothing -----------
;;
;; Every output the placement phase computes reaches the conclusion — through the
;; literals still to run, through the `exceptWhen` and `unknown` checks that read these
;; bindings, and through the consequent itself.  So taking the registry's first solution
;; would place a *different fact* depending on which solution came first, and which comes
;; first is a function of how the facts were stored.  The disagreement is declined and
;; filed, exactly as `provers/table-agreed` declines a unit that declares two conversion
;; factors.
;;
;; Each built-in computation answers once or not at all, so the shape needs a registry
;; that disagrees with itself — which `core/add-prover` is the public way to build, and
;; which an application registering a computed relation can reach without meaning to.  The
;; prover below answers off *stored* facts, so its solution order really is the index's:
;; the two runs differ in nothing but which candidate was asserted first.

(def ^:private post-join-ctx 'CxPostJoinAmbiguous)
(def ^:private post-join-above 'CxPostJoinAbove)

(def ^:private ambiguity-marker
  "The constant that keeps the prover below off every other `evaluate` goal there is."
  977)

(defn- two-answer-prover
  "A prover for `(evaluate ?out (+ ?n 977))`, answering with one solution per stored
  `(pred ?v)` fact — in the order the index yields them.

  `completeness` 100 with `est-bindings` 0 wins `provers/sole-prover` against the
  built-in `EvaluateProver`, so this is the only prover that runs on the goal and its
  solutions are exactly the ones below."
  [pred]
  (reify prover-types/Prover
    (applicable? [_ _ goal _]
      (and (sequential? goal) (= 3 (count goal)) (= 'evaluate (first goal))
           (sequential? (nth goal 2)) (= ambiguity-marker (last (nth goal 2)))))
    (est-bindings [_ _ _ _] 0)
    (cost         [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 100)
    (solve [_ kb goal _]
      (let [out (nth goal 1)]
        (mapv (fn [[_ b]] {out (get b '?v)})
              (res/matches-visible kb (list pred '?v) post-join-ctx))))))

(defn- post-join-run!
  "One aggregate rule whose `evaluate` is answered by `two-answer-prover`, over
  `candidates` — `[context value]` pairs, asserted in the order given.  Answers
  `{:tallies … :entries …}`: what the rule concluded, and the `:post-join-ambiguous`
  entries the run filed.

  Its own KB on the isolated space, since it rebuilds one per call and registers a prover
  on it: a registry is KB state, and leaving one on the shared KB would answer another
  namespace's `evaluate`."
  [candidates]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (v/add-prover kb (two-answer-prover 'pj_candidate))
    (v/assert kb (list 'genlCx post-join-ctx post-join-above) 'CxUniverse)
    (doseq [[c val] candidates] (v/assert kb (list 'pj_candidate val) c))
    (v/assert kb '(pj_person PjAnn) post-join-ctx)
    (doseq [c '[PjC1 PjC2]] (v/assert kb (list 'pjChildOf 'PjAnn c) post-join-ctx))
    (v/clear-violations! kb)
    (v/assert kb (list 'implies
                       (list 'and '(pj_person ?x)
                             '(agg/count ?n ?c (pjChildOf ?x ?c))
                             (list 'evaluate '?d (list '+ '?n ambiguity-marker)))
                       '(pjTally ?x ?d))
              post-join-ctx {:direction :forward})
    {:tallies (into #{} (map :sentence) (v/sentexes-matching kb '(pjTally ?x ?d) '?ctx))
     :entries (into [] (filter #(= :post-join-ambiguous (:violation %))) (v/violations kb))}))

(deftest a-post-join-literal-with-one-solution-concludes-as-it-always-did
  (let [{:keys [tallies entries]} (post-join-run! [[post-join-ctx 'PjOnly]])]
    (is (= #{'(pjTally PjAnn PjOnly)} tallies)
        "one solution is not a disagreement — the firing places the fact it computed")
    (is (empty? entries) "and nothing is filed")))

(deftest post-join-solutions-that-agree-conclude-once
  ;; Two solutions, one value: `pj_candidate` is stated of the same term in two contexts of
  ;; one ancestor set, so the prover answers twice with the same binding.  Agreement is what is
  ;; asked for, not a solution count.
  (let [{:keys [tallies entries]} (post-join-run! [[post-join-ctx 'PjSame]
                                                   [post-join-above 'PjSame]])]
    (is (= #{'(pjTally PjAnn PjSame)} tallies)
        "two solutions agreeing on the variable the conclusion reads are one answer")
    (is (empty? entries) "so nothing is declined")))

(deftest post-join-solutions-that-disagree-conclude-nothing-in-either-order
  (let [forward  (post-join-run! [[post-join-ctx 'PjLeft] [post-join-ctx 'PjRight]])
        backward (post-join-run! [[post-join-ctx 'PjRight] [post-join-ctx 'PjLeft]])]
    (testing "the firing is declined rather than adjudicated"
      (is (empty? (:tallies forward))
          "a literal answering two ways answers nothing — neither value is concluded")
      (is (empty? (:tallies backward))))
    (testing "and the ledger names the literal"
      (is (= 1 (count (:entries forward))))
      (let [e   (first (:entries forward))
            lit (get-in e [:detail :literal])]
        ;; the literal as the placement phase solved it — the rule is stored canonically
        ;; numbered, so its output variable reads `?varN` rather than the author's `?d`
        (is (= 'evaluate (first lit)))
        (is (= '(+ 2 977) (nth lit 2))
            "the count is substituted in: this is the literal that answered twice")
        (is (= 2 (count (get-in e [:detail :solutions])))
            "with both readings it could not choose between")))
    (testing "the same outcome, entry for entry, in both assertion orders"
      (is (= (:tallies forward) (:tallies backward)))
      (is (= (mapv #(dissoc % :run) (:entries forward))
             (mapv #(dissoc % :run) (:entries backward)))
          "belief is computed from content, so an entry ordered by solution order would
           be the arrival dependence this refusal exists to remove"))))

;; ---- the plan reports it the way the prover declares it -----------------

(tu/deftest-kb query-plan-shows-the-aggregate-running-alone
  (tu/with-terms [scoreOf Team]
    (extent! kb scoreOf Team [1 2])
    (let [plan (v/query-plan kb (list 'agg/count '?n '?v (list scoreOf Team '?v))
                             'CxWell)
          agg  (first (filter :runs? plan))]
      (is (= 1 (count (filter :runs? plan)))
          "completeness 100 means the engine runs it alone — nothing is unioned in")
      (is (= 1 (:est-bindings agg)) "one answer or none")
      (is (= :compute (:cost agg)))
      (is (= 100 (:completeness agg))))))
