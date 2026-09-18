;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sign-test
  "Sign arithmetic (`vaelii.impl.sign`): a quantity is negative, nil or positive, and the
  three declared relations say which quantities add, subtract and multiply into which.

  Two halves, the split `stp_test` takes.  The first tests the **tables and the fixpoint**
  with no KB in sight — the addition table's one ambiguous entry above all, since answering
  it with a guess is the failure this whole layer exists to avoid.  The second runs over a
  KB, where belief, context and the support a firing rests on all come into it.

  What the second half keeps asking is the same three questions: does the answer *arrive*,
  does it name the facts behind it, and does it go away again when one of those is
  retracted."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sign :as sign]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu])
  (:import [vaelii.impl.sign SignProver]))

;; A fresh KB per test: the CxCore grammar, CxMeasure (which holds the sign vocabulary
;; beside the measures), and the prover registered — it is opt-in, so registering it is
;; what turns stored sign facts into arithmetic.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (core-context/load-into)
                        (seed/load-context 'CxMeasure "upper")
                        (v/add-prover (sign/sign-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the tables and the fixpoint, without a KB --------------------------

(deftest like-signs-add-and-opposite-ones-do-not
  (let [sum (fn [a b dom] (sign/combined 'qualitativeSum #{a} #{b} dom))]
    (testing "two positives, two negatives, and zero the identity"
      (is (= #{:positive} (sum :positive :positive nil)))
      (is (= #{:negative} (sum :negative :negative nil)))
      (is (= #{:positive} (sum :positive :zero nil)))
      (is (= #{:negative} (sum :zero :negative nil)))
      (is (= #{:zero}     (sum :zero :zero nil))))
    (testing "a positive and a negative is every value there is, and that is the answer —
              the total is the sign of the larger, and nothing has said which"
      (is (= sign/all-signs (sum :positive :negative nil)))
      (is (= sign/all-signs (sum :negative :positive nil))))
    (testing "until a magnitude comparison says which addend is the larger"
      (is (= #{:positive} (sum :positive :negative :left)))
      (is (= #{:negative} (sum :positive :negative :right)))
      (is (= #{:negative} (sum :negative :positive :left)))
      (is (= #{:positive} (sum :negative :positive :right))))))

(deftest a-difference-is-a-sum-with-the-second-negated
  (let [dif (fn [a b dom] (sign/combined 'qualitativeDifference #{a} #{b} dom))]
    (testing "the ambiguity moves to LIKE signs, which is what subtraction does to it"
      (is (= sign/all-signs (dif :positive :positive nil)))
      (is (= sign/all-signs (dif :negative :negative nil)))
      (is (= #{:positive}   (dif :positive :negative nil)))
      (is (= #{:negative}   (dif :negative :positive nil))))
    (testing "and the same comparison resolves it, still on the two quantities' own
              magnitudes rather than on the negation's"
      (is (= #{:positive} (dif :positive :positive :left)))
      (is (= #{:negative} (dif :positive :positive :right))))))

(deftest a-product-is-never-ambiguous
  (let [prod (fn [a b] (sign/combined 'qualitativeProduct #{a} #{b} nil))]
    (is (= #{:positive} (prod :positive :positive)))
    (is (= #{:positive} (prod :negative :negative)))
    (is (= #{:negative} (prod :positive :negative)))
    (is (= #{:negative} (prod :negative :positive)))
    (testing "and nothing times anything is nothing, whatever is known of the other side"
      (is (= #{:zero} (prod :zero :positive)))
      (is (= #{:zero} (prod :negative :zero)))
      (is (= #{:zero} (sign/combined 'qualitativeProduct #{:zero} sign/all-signs nil))))))

(deftest a-table-over-sets-is-the-union-over-the-pairs
  (testing "an input still open to two values gives an output open to what both allow"
    (is (= #{:positive :zero}
           (sign/combined 'qualitativeSum #{:positive :zero} #{:zero} nil)))
    (is (= sign/all-signs
           (sign/combined 'qualitativeProduct sign/all-signs #{:negative} nil)))))

(deftest the-fixpoint-runs-a-chain-and-stops
  ;; A + B = C and C + D = E, with nothing but the three input signs stated.
  (let [c1 {:in [[:sign 'A] [:sign 'B]] :out [:sign 'C] :support #{1}
            :derive (fn [[a b]] (sign/combined 'qualitativeSum a b nil))}
        c2 {:in [[:sign 'C] [:sign 'D]] :out [:sign 'E] :support #{2}
            :derive (fn [[a b]] (sign/combined 'qualitativeSum a b nil))}
        st (sign/resolve-state {[:sign 'A] [#{:positive} #{10}]
                                [:sign 'B] [#{:positive} #{11}]
                                [:sign 'D] [#{:positive} #{12}]}
                               [c1 c2])]
    (testing "the second step reads the first step's answer"
      (is (= #{:positive} (first (get st [:sign 'C]))))
      (is (= #{:positive} (first (get st [:sign 'E])))))
    (testing "and both steps' facts and relations are behind the far end"
      (is (= #{1 2 10 11 12} (second (get st [:sign 'E])))))
    (testing "the same constraints in the other order reach the same fixpoint"
      (is (= (dissoc st [:sign 'E]) (dissoc (sign/resolve-state
                                             {[:sign 'A] [#{:positive} #{10}]
                                              [:sign 'B] [#{:positive} #{11}]
                                              [:sign 'D] [#{:positive} #{12}]}
                                             [c2 c1])
                                            [:sign 'E])))
      (is (= #{:positive} (first (get (sign/resolve-state
                                       {[:sign 'A] [#{:positive} #{10}]
                                        [:sign 'B] [#{:positive} #{11}]
                                        [:sign 'D] [#{:positive} #{12}]}
                                       [c2 c1])
                                      [:sign 'E])))))))

(deftest a-set-narrowed-to-nothing-is-a-contradiction
  (let [c {:in [[:sign 'A] [:sign 'B]] :out [:sign 'Q] :support #{1}
           :derive (fn [[a b]] (sign/combined 'qualitativeSum a b nil))}
        st (sign/resolve-state {[:sign 'A] [#{:positive} #{10}]
                                [:sign 'B] [#{:positive} #{11}]
                                [:sign 'Q] [#{:negative} #{12}]}
                               [c])]
    (is (= #{} (first (get st [:sign 'Q]))))
    (is (sign/inconsistent-state? st))
    (is (not (sign/inconsistent-state? (dissoc st [:sign 'Q]))))))

;; ---- over a KB ----------------------------------------------------------

(defn- tub!
  "The worked example: a tap filling and a drain emptying, their net the rate at which the
  water level changes.  Returns the handles of the two flow signs and of the sum."
  [kb In Out Net Level]
  (v/assert kb (list 'qualitativeSum In Out Net) C)
  (v/assert kb (list 'derivativeOf Net Level) C)
  [(v/assert kb (list 'signOf In 'SignPositive) C)
   (v/assert kb (list 'signOf Out 'SignNegative) C)])

(tu/deftest-kb the-tub-fills-when-the-tap-beats-the-drain
  (tu/with-terms [Tap Drain NetFlow WaterLevel]
    (tub! kb Tap Drain NetFlow WaterLevel)
    (testing "with nothing said about which is faster, the net flow has no sign — the
              question has three answers and the KB declines all three"
      (is (not (v/ask? kb (list 'signOf NetFlow 'SignPositive) C)))
      (is (not (v/ask? kb (list 'signOf NetFlow 'SignNegative) C)))
      (is (not (v/ask? kb (list 'signOf NetFlow 'SignZero) C)))
      (is (empty? (v/ask kb (list 'signOf NetFlow '?s) C))))
    (testing "the tap runs faster than the drain, so the net flow is positive"
      (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
      (is (v/ask? kb (list 'signOf NetFlow 'SignPositive) C))
      (is (= 'SignPositive (get (tu/sole-answer (v/ask kb (list 'signOf NetFlow '?s) C))
                                '?s))))
    (testing "and the water level rises, which is the net flow's sign read across the
              derivativeOf edge"
      (is (v/ask? kb (list 'trendOf WaterLevel 'SignPositive) C)))
    (testing "the drain beating the tap says the other thing, and the level falls"
      (v/retract! kb (v/handle-of kb (list 'greaterInMagnitudeThan Tap Drain) C))
      (v/assert kb (list 'greaterInMagnitudeThan Drain Tap) C)
      (is (v/ask? kb (list 'signOf NetFlow 'SignNegative) C))
      (is (v/ask? kb (list 'trendOf WaterLevel 'SignNegative) C)))))

(tu/deftest-kb a-cooling-bodys-temperature-falls
  ;; The whole of the inference is one derivativeOf edge: a rate known negative makes the
  ;; quantity it is the rate of falling, with no arithmetic at all.
  (tu/with-terms [HeatLoss BodyTemperature]
    (v/assert kb (list 'derivativeOf HeatLoss BodyTemperature) C)
    (v/assert kb (list 'signOf HeatLoss 'SignNegative) C)
    (is (v/ask? kb (list 'trendOf BodyTemperature 'SignNegative) C))
    (testing "and it is not rising, which the algebra refutes rather than merely failing
              to prove — the three values are exhaustive"
      (is (v/ask? kb (list 'not (list 'trendOf BodyTemperature 'SignPositive)) C))
      (is (v/ask? kb (list 'not (list 'trendOf BodyTemperature 'SignZero)) C)))
    (testing "the edge runs the other way too: a stated trend pins the rate that made it"
      (tu/with-terms [Growth Population]
        (v/assert kb (list 'derivativeOf Growth Population) C)
        (v/assert kb (list 'trendOf Population 'SignPositive) C)
        (is (v/ask? kb (list 'signOf Growth 'SignPositive) C))))))

(tu/deftest-kb what-a-derived-sign-rests-on
  (tu/with-terms [Tap Drain NetFlow WaterLevel Unrelated]
    (let [[h-in h-out] (tub! kb Tap Drain NetFlow WaterLevel)
          h-cmp        (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
          h-other      (v/assert kb (list 'signOf Unrelated 'SignPositive) C)
          [poss sup]   (sign/possible-signs kb C :sign NetFlow)]
      (is (= #{:positive} poss))
      (testing "the two flows, and the comparison that decided between them"
        (is (contains? sup h-in))
        (is (contains? sup h-out))
        (is (contains? sup h-cmp)))
      (testing "and a sign fact about something else is not — a narrowing names what
                narrowed it"
        (is (not (contains? sup h-other))))
      (testing "retracting the comparison gives the ambiguity back"
        (v/retract! kb h-cmp)
        (is (= sign/all-signs (first (sign/possible-signs kb C :sign NetFlow))))
        (is (not (v/ask? kb (list 'signOf NetFlow 'SignPositive) C)))))))

(tu/deftest-kb a-forward-rule-resting-on-a-derived-sign-is-withdrawn-with-the-comparison
  (tu/with-terms [Tap Drain NetFlow WaterLevel overflowing]
    (v/assert kb (list 'arg overflowing 1 'thing) 'CxCore {:strength :monotonic})
    (v/assert-rule kb [(list 'trendOf '?x 'SignPositive)] (list overflowing '?x) C {:direction :forward})
    (tub! kb Tap Drain NetFlow WaterLevel)
    (testing "ambiguous, so nothing fires"
      (is (empty? (v/sentexes-matching kb (list overflowing WaterLevel) '?ctx))))
    (let [h-cmp (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
          concl (tu/sole-answer (v/sentexes-matching kb (list overflowing WaterLevel) '?ctx)
                                (list overflowing WaterLevel))]
      (testing "the comparison arrives after the rule and the facts, and the rule fires
                on it anyway — which is what naming the sources buys"
        (is (some? concl))
        (is (false? (v/premise? kb (:id concl)))))
      (testing "and the proof names the comparison"
        (is (contains? (set (tree-seq coll? seq (v/why kb (:id concl)))) h-cmp)))
      (testing "so retracting it takes the conclusion with it"
        (v/retract! kb h-cmp)
        (is (empty? (v/sentexes-matching kb (list overflowing WaterLevel) '?ctx)))))))

(def ^:private order-facts
  "The tub, said as five sentences.  Every permutation of them is the same knowledge."
  ['(signOf OrderTap SignPositive)
   '(signOf OrderDrain SignNegative)
   '(qualitativeSum OrderTap OrderDrain OrderNet)
   '(greaterInMagnitudeThan OrderTap OrderDrain)
   '(derivativeOf OrderNet OrderLevel)])

(defn- reading-of
  "Assert `order` into a KB of its own and read the net flow's sign and the level's trend
  back — each as its possible set together with the **sentences** its support names.

  The sentences and not the handles: a handle is allocated in arrival order, so two
  orderings of one knowledge cannot name the same integers and comparing them would
  compare the wrong thing.  What must not move is which facts the answer rests on."
  [order]
  (let [k (doto (tu/isolated-fresh)
            (core-context/load-into)
            (seed/load-context 'CxMeasure "upper")
            (v/add-prover (sign/sign-prover)))]
    (try
      (doseq [s order] (v/assert k s C))
      (mapv (fn [[attr q]]
              (let [[poss sup] (sign/possible-signs k C attr q)]
                [poss (into #{} (map #(:sentence (v/sentex k %))) sup)]))
            [[:sign 'OrderNet] [:trend 'OrderLevel]])
      (finally (tu/clear-kb! k)))))

(deftest the-same-knowledge-in-any-order-gives-the-same-answer
  ;; Order independence over the whole reading, including which facts the answer names:
  ;; the constraints are taken in a content order, so the witness a narrowing picks is a
  ;; function of what was said rather than of when.  Its own KB per ordering, on the
  ;; isolated space, since it rebuilds one per permutation.
  (let [base (reading-of order-facts)]
    (is (= #{:positive} (first (first base))) "the net flow is positive")
    (is (= #{:positive} (first (second base))) "and the level rises")
    (doseq [order [(reverse order-facts)
                   (concat (drop 2 order-facts) (take 2 order-facts))
                   (concat (take 1 order-facts) (reverse (rest order-facts)))]]
      (is (= base (reading-of order)) (str "reading under " (pr-str order))))))

(tu/deftest-kb contradictory-signs-are-reported-and-answer-nothing
  (tu/with-terms [Tap Drain NetFlow WaterLevel]
    (tub! kb Tap Drain NetFlow WaterLevel)
    (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
    (v/assert kb (list 'signOf NetFlow 'SignNegative) C)
    (testing "the sum says positive and the KB says negative, so the reading is
              unsatisfiable and no sign goal in the context is answered — not even the
              one stated outright"
      (is (= :inconsistent (sign/reading kb C)))
      (is (not (v/ask? kb (list 'signOf NetFlow 'SignNegative) C)))
      (is (not (v/ask? kb (list 'signOf Tap 'SignPositive) C))))
    (testing "and it is reported rather than thrown — no single fact of the set is the
              wrong one, so blaming one would make the stored KB depend on arrival order"
      (let [es (filter #(= :sign-inconsistency (:violation %)) (v/violations kb))]
        (is (seq es))
        (testing "and it names the quantities that emptied — the net flow, and the level
                  whose trend the derivativeOf edge carried the emptiness to"
          (is (= #{NetFlow WaterLevel} (set (:quantities (:detail (first es)))))))))))

(tu/deftest-kb a-stated-sign-is-answered-back-out-of-the-same-reading
  ;; Why `completeness` is 100: the prover reads the stored facts into the reading, so it
  ;; answers everything a raw fact match would, and unioning one in would add nothing.
  (tu/with-terms [Debt]
    (let [h (v/assert kb (list 'signOf Debt 'SignNegative) C)]
      (is (v/ask? kb (list 'signOf Debt 'SignNegative) C))
      (is (= #{h} (second (sign/possible-signs kb C :sign Debt))))
      (testing "an open goal enumerates it, and a quantity nothing constrains is absent"
        (is (= #{Debt} (into #{} (map #(get % '?q)) (v/ask kb '(signOf ?q ?s) C))))))))

(tu/deftest-kb a-quantity-nothing-constrains-is-answered-with-nothing
  (tu/with-terms [Tap Drain NetFlow WaterLevel Mystery]
    (v/assert kb (list 'qualitativeSum Tap Drain NetFlow) C)
    (v/assert kb (list 'derivativeOf NetFlow WaterLevel) C)
    (testing "the relation is stated and no sign is, so nothing is entailed anywhere"
      (is (empty? (v/ask kb (list 'signOf NetFlow '?s) C)))
      (is (empty? (v/ask kb (list 'trendOf WaterLevel '?s) C))))
    (testing "and a term the reading never reached is not refutable either — the three
              values are exhaustive, but only of what the reading constrains"
      (is (not (v/ask? kb (list 'not (list 'signOf Mystery 'SignPositive)) C))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (is (not-any? #(instance? SignProver %) provers/default-provers)
      "nothing about signs is in the default registry, so a KB pays for the fixpoint only
       once it asks for it"))

(tu/deftest-kb without-the-prover-the-relations-are-inert
  (tu/with-terms [Tap Drain NetFlow]
    (v/assert kb (list 'qualitativeSum Tap Drain NetFlow) C)
    (v/assert kb (list 'signOf Tap 'SignPositive) C)
    (v/assert kb (list 'signOf Drain 'SignPositive) C)
    (testing "a stated sign is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'signOf Tap 'SignPositive) C))))
    (testing "but nothing in the default registry adds two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'signOf NetFlow '?s) C))))
    (testing "the registered prover on the very same facts does"
      (is (v/ask? kb (list 'signOf NetFlow 'SignPositive) C)))))

(tu/deftest-kb the-prover-names-what-it-answers-and-what-it-reads
  (let [pr (sign/sign-prover)]
    (is (= '#{signOf trendOf} (prover-types/support-functors pr)))
    (is (= '#{signOf trendOf qualitativeSum qualitativeDifference qualitativeProduct
              derivativeOf greaterInMagnitudeThan}
           (prover-types/support-sources pr))
        "everything the reading reads, so a datum on one of them re-joins the rules
         carrying a sign antecedent rather than arriving too late to be seen")))
