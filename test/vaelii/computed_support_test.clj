;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.computed-support-test
  "A forward rule whose antecedent a **prover** answers out of stored facts
  (`vaelii.impl.types.prover/SupportingProver`): the metric temporal closure, the duration
  arithmetic, and the measure comparisons.

  All three answer a question whose answer is a function of what the KB holds — how far
  apart two instants are, how long two intervals last between them, whether a mass in
  grams exceeds one in kilograms — and none of those facts is named by any *other*
  antecedent of the rule.  So the firing has to name them itself, or the conclusion
  outlives its reasons: retract the conversion factor and the KB goes on believing the
  whale is heavy.

  What is pinned here, phrased as the questions a reader would ask:

    * how long between two events, when nobody stated the gap — and does the answer stop
      being believed when a leg of the chain is withdrawn?
    * how long do two meetings take together, and does that survive one of them losing
      its length?
    * is the whale heavier than a ton, when its mass is stated in kilograms and only the
      unit table connects the two?
    * does a change to any of that reach a rule that has **already** fired, whichever
      order the knowledge arrived in?
    * and does the answer stay **local** — a constraint the chain never travelled must
      not withdraw anything."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.duration :as dur]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.stp :as stp]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the CxCore grammar, CxMeasure (the measure structural NATs and the
;; unit table), CxTime (temporalDistance, length, the interval relations), and all three
;; opt-in provers registered — registering them is what turns stored facts into a
;; computation, and the quantity prover ships in the default registry either way.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (core-context/load-into)
                        (seed/load-context 'CxMeasure "upper")
                        (seed/load-context 'CxTime "upper")
                        (v/add-prover (stp/stp-prover))
                        (v/add-prover (dur/duration-prover))
                        (v/add-prover (iv/allen-prover)))))

(def ^:private C 'CxUniverse)

(defn- fwd [antes conseq] (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- believed [kb pred]
  (set (map :sentence (v/sentexes-with-functor kb pred {:believed? true}))))

(defn- handle-of [kb pred sentence]
  (:id (first (filter #(= sentence (:sentence %)) (v/sentexes-with-functor kb pred)))))

(defn- reasons
  "The sentences `why` names as supporting `sentence` — one justification's `:because`."
  [kb pred sentence]
  (set (map :sentence
            (:because (first (:support (v/why kb (handle-of kb pred sentence))))))))

;; ---- how long between two events -----------------------------------------

(tu/deftest-kb a-rule-fires-on-a-gap-nobody-stated
  (tu/with-terms [Dawn Noon Dusk longEnough]
    (v/assert kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)) C)
    (v/assert kb (fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
    (testing "the closure composes the two legs, and the rule fires on what it entails"
      (is (= #{(list longEnough Dawn Dusk)} (believed kb longEnough))))
    (testing "and the firing names the legs it was composed out of"
      (is (contains? (reasons kb longEnough (list longEnough Dawn Dusk))
                     (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour))))
      (is (contains? (reasons kb longEnough (list longEnough Dawn Dusk))
                     (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)))))))

(tu/deftest-kb withdrawing-a-leg-of-the-chain-withdraws-what-was-concluded-from-it
  (tu/with-terms [Dawn Noon Dusk longEnough]
    (v/assert kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)) C)
    (v/assert kb (fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
    (is (seq (believed kb longEnough)) "the conclusion is there to lose")
    (v/retract! kb (handle-of kb 'temporalDistance
                              (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour))))
    (testing "with the second leg gone nothing entails the gap, so nothing concluded from it stands"
      (is (empty? (believed kb longEnough))))))

(tu/deftest-kb a-constraint-the-chain-never-travelled-withdraws-nothing
  ;; Locality: the support is the shortest chain, not the whole network, so a constraint
  ;; between two other instants is not a reason for this conclusion and taking it away is
  ;; not a reason to give the conclusion up.
  (tu/with-terms [Dawn Noon Dusk Midnight Sunrise longEnough]
    (v/assert kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Midnight Sunrise '(QuantityFn 5 Hour)) C)
    (v/assert kb (fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
    (is (seq (believed kb longEnough)))
    (v/retract! kb (handle-of kb 'temporalDistance
                              (list 'temporalDistance Midnight Sunrise '(QuantityFn 5 Hour))))
    (testing "an unrelated gap is no part of why the first two compose"
      (is (= #{(list longEnough Dawn Dusk)} (believed kb longEnough))))))

(tu/deftest-kb the-rule-may-arrive-before-the-constraints
  (tu/with-terms [Dawn Noon Dusk longEnough]
    (v/assert kb (fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
    (v/assert kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)) C)
    (testing "the same knowledge in the other order believes the same thing"
      (is (= #{(list longEnough Dawn Dusk)} (believed kb longEnough))))))

;; ---- how long two things take together -----------------------------------

(tu/deftest-kb a-rule-fires-on-a-total-duration-computed-from-the-stored-lengths
  (tu/with-terms [Standup Review longDay]
    (v/assert kb (list 'length Standup '(QuantityFn 2 Hour))   C)
    (v/assert kb (list 'length Review  '(QuantityFn 30 Minute)) C)
    (v/assert kb (fwd [(list 'totalDuration (list 'list Standup Review) '?d)]
                      (list longDay Standup Review))
              C)
    (testing "two hours and half an hour add up, and the rule fires on the sum"
      (is (= #{(list longDay Standup Review)} (believed kb longDay))))
    (testing "and the firing names both lengths"
      (let [why (reasons kb longDay (list longDay Standup Review))]
        (is (contains? why (list 'length Standup '(QuantityFn 2 Hour))))
        (is (contains? why (list 'length Review '(QuantityFn 30 Minute))))))))

(tu/deftest-kb withdrawing-a-length-withdraws-what-the-total-concluded
  (tu/with-terms [Standup Review longDay]
    (v/assert kb (list 'length Standup '(QuantityFn 2 Hour))   C)
    (v/assert kb (list 'length Review  '(QuantityFn 30 Minute)) C)
    (v/assert kb (fwd [(list 'totalDuration (list 'list Standup Review) '?d)]
                      (list longDay Standup Review))
              C)
    (is (seq (believed kb longDay)))
    (v/retract! kb (handle-of kb 'length (list 'length Review '(QuantityFn 30 Minute))))
    (testing "with one component unmeasured there is no sum, so there is no conclusion"
      (is (empty? (believed kb longDay))))))

(tu/deftest-kb the-rule-may-arrive-before-the-lengths
  (tu/with-terms [Standup Review longDay]
    (v/assert kb (fwd [(list 'totalDuration (list 'list Standup Review) '?d)]
                      (list longDay Standup Review))
              C)
    (v/assert kb (list 'length Standup '(QuantityFn 2 Hour))   C)
    (v/assert kb (list 'length Review  '(QuantityFn 30 Minute)) C)
    (is (= #{(list longDay Standup Review)} (believed kb longDay)))))

;; ---- is the whale heavier than a ton --------------------------------------

(defn- load-mass-table
  "A two-unit table over **temporary** units.  The shipped CxMeasure already declares
  grams and kilograms, and a test that retracted one of those would be taking away
  content the fixture loaded — a test invents what it intends to destroy."
  [kb small big dimension]
  (v/assert kb (list 'dimensionOf small dimension)      C)
  (v/assert kb (list 'dimensionOf big dimension)        C)
  (v/assert kb (list 'conversionFactor small big 0.001) C)
  (v/assert kb (list 'conversionFactor big big 1)       C))

(tu/deftest-kb a-measure-comparison-rests-on-the-unit-table-it-converted-through
  (tu/with-terms [Gramme Kilo Heft massOf light Mouse]
    (load-mass-table kb Gramme Kilo Heft)
    (v/assert kb (list massOf Mouse (list 'QuantityFn 500 Gramme)) C)
    (v/assert kb (fwd [(list massOf '?x '?q)
                       (list 'quantityLessThan '?q (list 'QuantityFn 1 Kilo))]
                      (list light '?x))
              C)
    (testing "five hundred of the small unit is under one of the big one — but only the
              table says so"
      (is (= #{(list light Mouse)} (believed kb light))))
    (testing "so the firing names the conversion as well as the mass"
      (let [why (reasons kb light (list light Mouse))]
        (is (contains? why (list massOf Mouse (list 'QuantityFn 500 Gramme))))
        (is (contains? why (list 'conversionFactor Gramme Kilo 0.001)))))))

(tu/deftest-kb withdrawing-the-conversion-factor-withdraws-the-comparison-s-conclusion
  (tu/with-terms [Gramme Kilo Heft massOf light Mouse]
    (load-mass-table kb Gramme Kilo Heft)
    (v/assert kb (list massOf Mouse (list 'QuantityFn 500 Gramme)) C)
    (v/assert kb (fwd [(list massOf '?x '?q)
                       (list 'quantityLessThan '?q (list 'QuantityFn 1 Kilo))]
                      (list light '?x))
              C)
    (is (seq (believed kb light)))
    (v/retract! kb (handle-of kb 'conversionFactor (list 'conversionFactor Gramme Kilo 0.001)))
    (testing "without the factor the small unit is its own base, and five hundred of them
              are not under one"
      (is (not (v/ask? kb (list 'quantityLessThan (list 'QuantityFn 500 Gramme)
                                (list 'QuantityFn 1 Kilo))
                       C))
          "the comparison itself has stopped holding")
      (is (empty? (believed kb light))
          "and nothing concluded from it is still believed"))))

(tu/deftest-kb the-unit-table-may-arrive-last
  ;; The order-independence half.  Nothing connects `conversionFactor` to
  ;; `quantityGreaterThan` by predicate, and the mass fact that would have triggered the
  ;; rule has already arrived — so the table arriving is what has to re-join the rule.
  (tu/with-terms [Gramme Kilo Heft massOf heavy Whale]
    (v/assert kb (fwd [(list massOf '?x '?q)
                       (list 'quantityGreaterThan '?q (list 'QuantityFn 1 Kilo))]
                      (list heavy '?x))
              C)
    (v/assert kb (list massOf Whale (list 'QuantityFn 5000 Gramme)) C)
    (testing "with no table the two units are their own dimensions and nothing compares"
      (is (empty? (believed kb heavy))))
    (load-mass-table kb Gramme Kilo Heft)
    (testing "the table arriving last derives what the table arriving first would have"
      (is (= #{(list heavy Whale)} (believed kb heavy))))))

;; ---- and what a purely arithmetic comparison still rests on ---------------

(tu/deftest-kb an-arithmetic-comparison-adds-no-supporter-of-its-own
  ;; The other side of the contract: a prover that reads nothing stored reports nothing,
  ;; so `(lessThan ?a ?b)` leaves the firing supported by the facts that bound it and the
  ;; rule, exactly as before.
  (tu/with-terms [ageOf youngerThan Ann Bob]
    (let [h1 (v/assert kb (list ageOf Ann 10) C {:chain? false})
          h2 (v/assert kb (list ageOf Bob 20) C {:chain? false})
          rh (v/assert kb (fwd [(list ageOf '?x '?a) (list ageOf '?y '?b)
                                (list 'lessThan '?a '?b)]
                               (list youngerThan '?x '?y))
                       C)
          ch (handle-of kb youngerThan (list youngerThan Ann Bob))]
      (is (some? ch))
      (is (= [[#{h1 h2} rh]]
             (mapv (juxt (comp set :antecedents) :informant)
                   (v/supporting-justifications kb ch)))))))
