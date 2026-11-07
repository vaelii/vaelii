;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sign-test
  "Sign arithmetic (`vaelii.impl.sign`, docs/sign.md): the tables and the fixpoint as
  pure data first, then the reading over a KB — whether an answer arrives, which facts it
  names, and whether it goes when one of them is retracted."
  (:require [clojure.set :as set]
            [clojure.test :refer [are deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sign :as sign]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu])
  (:import [vaelii.impl.sign SignProver]))

;; CxUniverse holds the sign vocabulary; the prover is opt-in, so each KB registers it.
;; The KB is built per test because tests count entries in the violations ledger, which
;; a KB shared across tests keeps from the tests before.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/empty-kb)
                        (tu/load-core!)
                        (v/add-prover (sign/sign-prover)))))

(def ^:private C 'CxUniverse)

;; ---- the tables and the fixpoint, without a KB --------------------------

(deftest like-signs-add-and-opposite-ones-need-a-comparison
  (are [a b dom want] (= want (sign/combined 'qualitativeSum #{a} #{b} dom))
    :positive :positive nil    #{:positive}
    :negative :negative nil    #{:negative}
    :positive :zero     nil    #{:positive}
    :zero     :negative nil    #{:negative}
    :zero     :zero     nil    #{:zero}
    :positive :negative nil    sign/all-signs
    :negative :positive nil    sign/all-signs
    :positive :negative :left  #{:positive}
    :positive :negative :right #{:negative}
    :negative :positive :left  #{:negative}
    :negative :positive :right #{:positive}))

(deftest a-difference-is-a-sum-with-the-second-negated
  ;; The ambiguity moves to like signs, and the comparison is of the two quantities.
  (are [a b dom want] (= want (sign/combined 'qualitativeDifference #{a} #{b} dom))
    :positive :positive nil    sign/all-signs
    :negative :negative nil    sign/all-signs
    :positive :negative nil    #{:positive}
    :negative :positive nil    #{:negative}
    :positive :positive :left  #{:positive}
    :positive :positive :right #{:negative}))

(deftest a-product-is-never-ambiguous
  (are [sa sb want] (= want (sign/combined 'qualitativeProduct sa sb nil))
    #{:positive} #{:positive}   #{:positive}
    #{:negative} #{:negative}   #{:positive}
    #{:positive} #{:negative}   #{:negative}
    #{:negative} #{:positive}   #{:negative}
    #{:zero}     #{:positive}   #{:zero}
    #{:negative} #{:zero}       #{:zero}
    #{:zero}     sign/all-signs #{:zero}))

(deftest a-table-over-sets-is-the-union-over-the-pairs
  (is (= #{:positive :zero} (sign/combined 'qualitativeSum #{:positive :zero} #{:zero} nil)))
  (is (= sign/all-signs (sign/combined 'qualitativeProduct sign/all-signs #{:negative} nil))))

(def ^:private sum (fn [[a b]] (sign/combined 'qualitativeSum a b nil)))

(deftest the-fixpoint-runs-a-chain-and-stops
  ;; A + B = C and C + D = E, with the three input signs stated.
  (let [c1   {:in [[:sign 'A] [:sign 'B]] :out [:sign 'C] :support #{1} :derive sum}
        c2   {:in [[:sign 'C] [:sign 'D]] :out [:sign 'E] :support #{2} :derive sum}
        init {[:sign 'A] [#{:positive} #{10}]
              [:sign 'B] [#{:positive} #{11}]
              [:sign 'D] [#{:positive} #{12}]}
        st   (sign/resolve-state init [c1 c2])]
    (testing "the second step reads the first step's answer and rests on both steps"
      (is (= [#{:positive} #{1 10 11}] (get st [:sign 'C])))
      (is (= [#{:positive} #{1 2 10 11 12}] (get st [:sign 'E]))))
    (testing "the constraints in the other order reach the same state"
      (is (= st (sign/resolve-state init [c2 c1]))))
    (testing "a constraint that agrees with a stated sign adds no support"
      (is (= [#{:positive} #{13}]
             (get (sign/resolve-state (assoc init [:sign 'C] [#{:positive} #{13}]) [c1])
                  [:sign 'C]))))))

(deftest the-fixpoint-applies-a-chain-in-work-linear-in-its-links
  ;; A chain whose constraints stand in the reverse of chain order moves one link per
  ;; pass, so a round-robin over every constraint would derive n² times; the worklist
  ;; re-applies only a constraint whose input moved.
  (let [n       40
        derives (atom 0)
        q       #(symbol (str "Q" %))
        cs      (vec (for [i (range n 0 -1)]
                       {:in [[:sign (q (dec i))] [:sign 'P]] :out [:sign (q i)] :support #{i}
                        :derive (fn [sets] (swap! derives inc) (sum sets))}))
        st      (sign/resolve-state {[:sign 'Q0] [#{:positive} #{100}]
                                     [:sign 'P]  [#{:positive} #{101}]}
                                    cs)]
    (is (= [#{:positive} (into #{100 101} (range 1 (inc n)))] (get st [:sign (q n)])))
    (is (<= @derives (* 2 n)))))

(deftest a-set-narrowed-to-nothing-is-a-contradiction
  (let [c  {:in [[:sign 'A] [:sign 'B]] :out [:sign 'Q] :support #{1} :derive sum}
        st (sign/resolve-state {[:sign 'A] [#{:positive} #{10}]
                                [:sign 'B] [#{:positive} #{11}]
                                [:sign 'Q] [#{:negative} #{12}]}
                               [c])]
    (is (= #{} (first (get st [:sign 'Q]))))
    (is (sign/inconsistent-state? st))
    (is (not (sign/inconsistent-state? (dissoc st [:sign 'Q]))))))

;; ---- over a KB ----------------------------------------------------------

(defn- tub!
  "The worked example.  Returns the handles of the two flow signs."
  [kb In Out Net Level]
  (v/assert kb (list 'qualitativeSum In Out Net) C)
  (v/assert kb (list 'derivativeOf Net Level) C)
  [(v/assert kb (list 'signOf In 'SignPositive) C)
   (v/assert kb (list 'signOf Out 'SignNegative) C)])

(tu/deftest-kb the-tub-fills-when-the-tap-beats-the-drain
  (tu/with-terms [Tap Drain NetFlow WaterLevel]
    (tub! kb Tap Drain NetFlow WaterLevel)
    (testing "with nothing said about which is faster, the net flow has no sign"
      (doseq [s '[SignPositive SignNegative SignZero]]
        (is (not (v/ask? kb (list 'signOf NetFlow s) C))))
      (is (empty? (v/ask kb (list 'signOf NetFlow '?s) C))))
    (testing "the tap runs faster than the drain, so the net flow is positive"
      (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
      (is (v/ask? kb (list 'signOf NetFlow 'SignPositive) C))
      (is (= 'SignPositive (get (tu/sole-answer (v/ask kb (list 'signOf NetFlow '?s) C))
                                '?s))))
    (testing "and the water level rises, across the derivativeOf edge"
      (is (v/ask? kb (list 'trendOf WaterLevel 'SignPositive) C)))
    (testing "the drain beating the tap makes the level fall"
      (v/retract! kb (v/handle-of kb (list 'greaterInMagnitudeThan Tap Drain) C))
      (v/assert kb (list 'greaterInMagnitudeThan Drain Tap) C)
      (is (v/ask? kb (list 'signOf NetFlow 'SignNegative) C))
      (is (v/ask? kb (list 'trendOf WaterLevel 'SignNegative) C)))))

(tu/deftest-kb a-cooling-bodys-temperature-falls
  (tu/with-terms [HeatLoss BodyTemperature]
    (v/assert kb (list 'derivativeOf HeatLoss BodyTemperature) C)
    (v/assert kb (list 'signOf HeatLoss 'SignNegative) C)
    (is (v/ask? kb (list 'trendOf BodyTemperature 'SignNegative) C))
    (testing "and it is refuted rising or steady, the three values being exhaustive"
      (is (v/ask? kb (list 'not (list 'trendOf BodyTemperature 'SignPositive)) C))
      (is (v/ask? kb (list 'not (list 'trendOf BodyTemperature 'SignZero)) C)))
    (testing "an open sign under a negation is not answered"
      (is (empty? (v/ask kb (list 'not (list 'trendOf BodyTemperature '?s)) C))))
    (testing "a second rate of the same quantity takes the same sign"
      (tu/with-terms [Radiation]
        (v/assert kb (list 'derivativeOf Radiation BodyTemperature) C)
        (is (v/ask? kb (list 'signOf Radiation 'SignNegative) C))))
    (testing "the edge runs up too: a stated trend determines the rate that made it"
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
      (testing "the two flows and the comparison, and not a sign fact about something else"
        (is (set/subset? #{h-in h-out h-cmp} sup))
        (is (not (contains? sup h-other))))
      (testing "retracting the comparison gives the ambiguity back"
        (v/retract! kb h-cmp)
        (is (= sign/all-signs (first (sign/possible-signs kb C :sign NetFlow))))
        (is (not (v/ask? kb (list 'signOf NetFlow 'SignPositive) C)))))))

(tu/deftest-kb a-comparison-the-result-does-not-depend-on-is-not-in-its-support
  (tu/with-terms [A B D Prod Sum]
    (v/assert kb (list 'signOf A 'SignPositive) C)
    (v/assert kb (list 'signOf B 'SignNegative) C)
    (v/assert kb (list 'signOf D 'SignPositive) C)
    (v/assert kb (list 'qualitativeProduct A B Prod) C)
    (v/assert kb (list 'qualitativeSum A D Sum) C)
    (let [h-ab (v/assert kb (list 'greaterInMagnitudeThan A B) C)
          h-ad (v/assert kb (list 'greaterInMagnitudeThan A D) C)]
      (doseq [[q sign h-cmp] [[Prod :negative h-ab] [Sum :positive h-ad]]
              :let [[poss sup] (sign/possible-signs kb C :sign q)]]
        (is (= #{sign} poss) (str q))
        (is (not (contains? sup h-cmp)) (str q))))))

(tu/deftest-kb a-forward-rule-resting-on-a-derived-sign-is-withdrawn-with-the-comparison
  (tu/with-terms [Tap Drain NetFlow WaterLevel overflowing]
    (v/assert kb (list 'arg overflowing 1 'thing) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(list 'trendOf '?x 'SignPositive)] (list overflowing '?x) C {:direction :forward})
    (tub! kb Tap Drain NetFlow WaterLevel)
    (testing "ambiguous, so nothing fires"
      (is (empty? (v/sentexes-matching kb (list overflowing WaterLevel) '?ctx))))
    (let [h-cmp (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
          concl (tu/sole-answer (v/sentexes-matching kb (list overflowing WaterLevel) '?ctx)
                                (list overflowing WaterLevel))]
      (testing "the comparison arrives after the rule and the facts, and the rule fires"
        (is (some? concl))
        (is (false? (v/premise? kb (:id concl)))))
      (testing "and the proof names the comparison"
        (is (contains? (set (keys (:nodes (v/why kb (:id concl))))) h-cmp)))
      (testing "so retracting it takes the conclusion with it"
        (v/retract! kb h-cmp)
        (is (empty? (v/sentexes-matching kb (list overflowing WaterLevel) '?ctx)))))))

(def ^:private order-facts
  ['(signOf OrderTap SignPositive)
   '(signOf OrderDrain SignNegative)
   '(qualitativeSum OrderTap OrderDrain OrderNet)
   '(greaterInMagnitudeThan OrderTap OrderDrain)
   '(derivativeOf OrderNet OrderLevel)])

(defn- reading-of
  "Assert `order` into a KB of its own and read back the net flow's sign and the level's
  trend, each with the **sentences** its support names: handles follow arrival order."
  [order]
  (let [k (doto (tu/isolated-fresh)
            (tu/load-core!)
            (v/add-prover (sign/sign-prover)))]
    (try
      (doseq [s order] (v/assert k s C))
      (mapv (fn [[attr q]]
              (let [[poss sup] (sign/possible-signs k C attr q)]
                [poss (into #{} (map #(:sentence (v/sentex k %))) sup)]))
            [[:sign 'OrderNet] [:trend 'OrderLevel]])
      (finally (tu/clear-kb! k)))))

(defn- reads-the-same
  "`order-facts` read in their own order and in each of `orders`, one KB per order."
  [orders]
  (let [base (reading-of order-facts)]
    (is (= #{:positive} (first (first base))) "the net flow is positive")
    (is (= #{:positive} (first (second base))) "and the level rises")
    (doseq [order orders]
      (is (= base (reading-of order)) (str "reading under " (pr-str order))))))

(deftest the-same-knowledge-in-any-order-gives-the-same-answer
  ;; On the isolated space, since it rebuilds a KB per ordering.  Each KB loads the upper
  ;; layer, so `:default` reads the reverse alone and `…-in-three-orders…` all three
  (reads-the-same [(reverse order-facts)]))

(deftest ^:slow the-same-knowledge-in-three-orders-gives-the-same-answer
  (reads-the-same [(reverse order-facts)
                   (concat (drop 2 order-facts) (take 2 order-facts))
                   (concat (take 1 order-facts) (reverse (rest order-facts)))]))

(tu/deftest-kb contradictory-signs-are-reported-and-answer-nothing
  (tu/with-terms [Tap Drain NetFlow WaterLevel]
    (tub! kb Tap Drain NetFlow WaterLevel)
    (v/assert kb (list 'greaterInMagnitudeThan Tap Drain) C)
    (v/assert kb (list 'signOf NetFlow 'SignNegative) C)
    (testing "the sum says positive and the KB says negative, so no sign goal in the
              context is answered, the stated one included"
      (is (= :inconsistent (sign/reading kb C)))
      (is (not (v/ask? kb (list 'signOf NetFlow 'SignNegative) C)))
      (is (not (v/ask? kb (list 'signOf Tap 'SignPositive) C))))
    (testing "it is reported once, naming the net flow and the level the edge reaches"
      (let [es (filter #(= :sign-inconsistency (:violation %)) (v/violations kb))]
        (is (= 1 (count es)))
        (is (= #{NetFlow WaterLevel} (set (:quantities (:detail (first es))))))))))

(tu/deftest-kb two-stated-signs-that-disagree-are-a-contradiction-not-a-merge
  (tu/with-terms [Balance]
    (v/assert kb (list 'signOf Balance 'SignPositive) C)
    (v/assert kb (list 'signOf Balance 'SignNegative) C)
    (is (= :inconsistent (sign/reading kb C)))
    (is (not (v/same-class? kb 'SignPositive 'SignNegative)))))

(tu/deftest-kb a-stated-sign-is-answered-back-out-of-the-same-reading
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
    (testing "and a term the reading never reached is not refuted either"
      (is (not (v/ask? kb (list 'not (list 'signOf Mystery 'SignPositive)) C))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb without-the-prover-the-relations-are-inert
  (is (not-any? #(instance? SignProver %) provers/default-provers))
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
    (testing "the registered prover on the same facts does"
      (is (v/ask? kb (list 'signOf NetFlow 'SignPositive) C)))))

(tu/deftest-kb the-prover-names-what-it-answers-and-what-it-reads
  (let [pr (sign/sign-prover)]
    (is (= '#{signOf trendOf} (prover-types/support-functors pr)))
    (is (= '#{signOf trendOf qualitativeSum qualitativeDifference qualitativeProduct
              derivativeOf greaterInMagnitudeThan}
           (prover-types/support-sources pr)))))
