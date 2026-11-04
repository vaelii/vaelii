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

  This namespace asserts the following, phrased as the questions a reader would ask:

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
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.duration :as dur]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.stp :as stp]
            [vaelii.test-util :as tu]))

;; A fresh KB per test: the upper layer and all three opt-in provers registered.  The
;; upper layer's measure.txt holds the measure structural NATs and the unit table, and its
;; time.txt holds temporalDistance, length and the interval relations.  Registering the
;; provers is what turns stored facts into a computation, and the quantity prover ships in
;; the default registry either way.
;; The KB is built per test because a test registers a prover of its own, which a KB
;; shared across tests would keep.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core!)
                        (v/add-prover (stp/stp-prover))
                        (v/add-prover (dur/duration-prover))
                        (v/add-prover (iv/allen-prover)))))

(def ^:private C 'CxUniverse)

(defn- believed [kb pred]
  (set (map :sentence (v/sentexes-with-functor kb pred {:believed? true}))))

(defn- handle-of [kb pred sentence]
  (:id (first (filter #(= sentence (:sentence %)) (v/sentexes-with-functor kb pred)))))

(defn- reasons
  "The sentences `why` names as supporting `sentence` — one justification's `:because`."
  [kb pred sentence]
  (set (map :sentence
            (:because (first (:support (tu/why-root kb (handle-of kb pred sentence))))))))

;; ---- how long between two events -----------------------------------------

(tu/deftest-kb a-rule-fires-on-a-gap-nobody-stated
  (tu/with-terms [Dawn Noon Dusk longEnough]
    (v/assert kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)) C)
    (v/assert kb (tu/fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
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
    (v/assert kb (tu/fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
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
    (v/assert kb (tu/fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
    (is (seq (believed kb longEnough)))
    (v/retract! kb (handle-of kb 'temporalDistance
                              (list 'temporalDistance Midnight Sunrise '(QuantityFn 5 Hour))))
    (testing "an unrelated gap is no part of why the first two compose"
      (is (= #{(list longEnough Dawn Dusk)} (believed kb longEnough))))))

(tu/deftest-kb the-rule-may-arrive-before-the-constraints
  (tu/with-terms [Dawn Noon Dusk longEnough]
    (v/assert kb (tu/fwd [(list 'temporalDistance Dawn Dusk '?d)] (list longEnough Dawn Dusk)) C)
    (v/assert kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour)) C)
    (v/assert kb (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)) C)
    (testing "the same knowledge in the other order believes the same thing"
      (is (= #{(list longEnough Dawn Dusk)} (believed kb longEnough))))))

;; ---- how long two things take together -----------------------------------

(tu/deftest-kb a-rule-fires-on-a-total-duration-computed-from-the-stored-lengths
  (tu/with-terms [Standup Review longDay]
    (v/assert kb (list 'length Standup '(QuantityFn 2 Hour))   C)
    (v/assert kb (list 'length Review  '(QuantityFn 30 Minute)) C)
    (v/assert kb (tu/fwd [(list 'totalDuration (list 'list Standup Review) '?d)]
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
    (v/assert kb (tu/fwd [(list 'totalDuration (list 'list Standup Review) '?d)]
                         (list longDay Standup Review))
              C)
    (is (seq (believed kb longDay)))
    (v/retract! kb (handle-of kb 'length (list 'length Review '(QuantityFn 30 Minute))))
    (testing "with one component unmeasured there is no sum, so there is no conclusion"
      (is (empty? (believed kb longDay))))))

(tu/deftest-kb the-rule-may-arrive-before-the-lengths
  (tu/with-terms [Standup Review longDay]
    (v/assert kb (tu/fwd [(list 'totalDuration (list 'list Standup Review) '?d)]
                         (list longDay Standup Review))
              C)
    (v/assert kb (list 'length Standup '(QuantityFn 2 Hour))   C)
    (v/assert kb (list 'length Review  '(QuantityFn 30 Minute)) C)
    (is (= #{(list longDay Standup Review)} (believed kb longDay)))))

(defn- unit-rows
  "`unit` as a temporary unit of Duration worth 60 seconds, so a test may retract its rows."
  [unit]
  [(list 'dimensionOf unit 'Duration) (list 'conversionFactor unit 'Second 60)])

(tu/deftest-kb a-duration-rests-on-the-unit-rows-it-converted-through
  ;; rows: Review's length, the answer slot, and which of the Mins rows is retracted
  (doseq [[review-length answer retracted]
          [[#(list 'QuantityFn 30 %) (constantly '?d) 0]
           [#(list 'QuantityFn 30 %) (constantly '?d) 1]
           [(constantly '(QuantityFn 1800 Second)) #(list 'QuantityFn 150 %) 1]]]
    (tu/with-terms [Standup Review Mins longDay]
      (run! #(v/assert kb % C) (unit-rows Mins))
      (v/assert kb (list 'length Standup '(QuantityFn 2 Hour)) C)
      (v/assert kb (list 'length Review (review-length Mins)) C)
      (v/assert kb (tu/fwd [(list 'totalDuration (list 'list Standup Review) (answer Mins))]
                           (list longDay Standup Review))
                C)
      (is (seq (believed kb longDay)))
      (let [row (nth (unit-rows Mins) retracted)]
        (v/retract! kb (v/handle-of kb row C))
        (is (empty? (believed kb longDay)) (pr-str (first row) (answer Mins)))))))

(defn- metric-overlap!
  "Bridge A and B to their endpoints and state the gaps that put B's start 105 minutes
  into A's two hours, B lasting thirty minutes."
  [kb [A As Ae] [B Bs Be]]
  (doseq [s [(list 'startOf A As) (list 'endOf A Ae) (list 'startOf B Bs) (list 'endOf B Be)
             (list 'temporalDistance As Ae '(QuantityFn 2 Hour))
             (list 'temporalDistance Bs Be '(QuantityFn 30 Minute))
             (list 'temporalDistance As Bs '(QuantityFn 105 Minute))]]
    (v/assert kb s C)))

(tu/deftest-kb an-overlap-rests-on-what-narrowed-it
  (tu/with-terms [A B As Ae Bs Be D shared]
    (doseq [[i m] [[A '(QuantityFn 2 Hour)] [B '(QuantityFn 30 Minute)] [D '(QuantityFn 1 Hour)]]]
      (v/assert kb (list 'length i m) C))
    (doseq [i [B D]]
      (v/assert kb (tu/fwd [(list 'overlapDuration A i '?d)] (list shared A i '?d)) C))
    (v/assert kb (list 'before A D) C)
    (metric-overlap! kb [A As Ae] [B Bs Be])
    (is (contains? (believed kb shared) (list shared A D '(QuantityFn 0 Second))))
    (is (contains? (believed kb shared) (list shared A B '(QuantityFn 900 Second))))
    (testing "retracting the Allen relation"
      (v/retract! kb (v/handle-of kb (list 'before A D) C))
      (is (not (contains? (believed kb shared) (list shared A D '(QuantityFn 0 Second))))))
    (testing "retracting a gap the overlap window read"
      (v/retract! kb (v/handle-of kb (list 'temporalDistance As Bs '(QuantityFn 105 Minute)) C))
      (is (not (contains? (believed kb shared) (list shared A B '(QuantityFn 900 Second))))))))

(tu/deftest-kb an-overlap-rule-may-arrive-before-what-narrows-it
  ;; each row states, after the rule and the lengths, one source the answer reads last
  (doseq [last-source [:allen :gaps :endpoints :unit-rows]]
    (tu/with-terms [A B As Ae Bs Be Mins shared]
      (let [unit     (if (= :unit-rows last-source) Mins 'Minute)
            endpoint [(list 'startOf A As) (list 'endOf A Ae)
                      (list 'startOf B Bs) (list 'endOf B Be)]
            gaps     [(list 'temporalDistance As Ae '(QuantityFn 2 Hour))
                      (list 'temporalDistance Bs Be '(QuantityFn 30 Minute))
                      (list 'temporalDistance As Bs '(QuantityFn 105 Minute))]
            [early late expected]
            (case last-source
              :allen     [[] [(list 'contains A B)] '(QuantityFn 1800 Second)]
              :gaps      [endpoint gaps '(QuantityFn 900 Second)]
              :endpoints [gaps endpoint '(QuantityFn 900 Second)]
              :unit-rows [[] (unit-rows Mins) '(QuantityIntervalFn 0 1800 Second)])]
        (v/assert kb (tu/fwd [(list 'overlapDuration A B '?d)] (list shared A B '?d)) C)
        (v/assert kb (list 'length A '(QuantityFn 2 Hour)) C)
        (v/assert kb (list 'length B (list 'QuantityFn 30 unit)) C)
        (run! #(v/assert kb % C) early)
        (run! #(v/assert kb % C) late)
        (is (= #{(list shared A B expected)} (believed kb shared)) (str last-source))))))

(defn- believed-after
  "Assert `sentences` in order, read the believed `pred` sentences, and retract what was
  asserted, so the next reading starts from the same KB."
  [kb sentences pred]
  (let [hs (mapv #(v/assert kb % C) sentences)
        b  (believed kb pred)]
    (run! #(v/retract! kb %) (rseq hs))
    b))

(tu/deftest-kb a-narrowed-bound-is-believed-alone-in-every-order-and-after-a-retraction
  ;; each row: the rule, the sources with the one that narrows the answer last, the
  ;; conclusion over the narrowed answer, and the one over the answer without it
  (doseq [row [:overlap :distance]]
    (tu/with-terms [A B Dawn Mid Noon Dusk concl]
      (let [[rule sources narrow tight wide]
            (case row
              :overlap  [(tu/fwd [(list 'overlapDuration A B '?d)] (list concl A B '?d))
                         [(list 'length A '(QuantityFn 2 Hour))
                          (list 'length B '(QuantityFn 30 Minute))]
                         (list 'before A B)
                         (list concl A B '(QuantityFn 0 Second))
                         (list concl A B '(QuantityIntervalFn 0 1800 Second))]
              :distance [(tu/fwd [(list 'temporalDistance Dawn Dusk '?d)] (list concl Dawn Dusk '?d))
                         [(list 'temporalDistance Dawn Noon '(QuantityIntervalFn 5 7 Hour))
                          (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour))
                          (list 'temporalDistance Dawn Mid '(QuantityFn 3 Hour))]
                         (list 'temporalDistance Mid Noon '(QuantityFn 3 Hour))
                         (list concl Dawn Dusk '(QuantityFn 43200 Second))
                         (list concl Dawn Dusk '(QuantityIntervalFn 39600 46800 Second))])
            all (conj sources narrow)]
        (testing (str row)
          (is (= #{tight} (believed-after kb (cons rule all) concl)) "the rule first")
          (is (= #{tight} (believed-after kb (conj all rule) concl)) "the rule last")
          (is (= #{wide} (believed-after kb (conj sources rule) concl)) "a fresh load without it")
          (let [hs (mapv #(v/assert kb % C) (conj all rule))]
            (v/retract! kb (v/handle-of kb narrow C))
            (is (= #{wide} (believed kb concl)) "retracting what narrowed it")
            (run! #(when (v/sentex kb %) (v/retract! kb %)) (rseq hs))))))))

;; ---- is the whale heavier than a ton --------------------------------------

(defn- load-mass-table
  "A two-unit table over **temporary** units.  The shipped measure.txt already declares
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
    (v/assert kb (tu/fwd [(list massOf '?x '?q)
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
    (v/assert kb (tu/fwd [(list massOf '?x '?q)
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

(tu/deftest-kb a-unit-table-the-rule-cannot-see-compares-nothing
  ;; The scoping half.  `quantity.md` has the forward join read the table at `'?ctx`; what
  ;; a reader sees is what is derived, and a rule and a fact in a sibling of the table
  ;; derive nothing anywhere until their context is wired under it.
  (tu/with-terms [Gramme Kilo Heft massOf heavy Whale CxTable CxUse]
    (doseq [c [CxTable CxUse]]
      (v/assert kb (list 'genlCx c C) C {:strength :monotonic}))
    (v/assert kb (list 'dimensionOf Gramme Heft) CxTable)
    (v/assert kb (list 'dimensionOf Kilo Heft) CxTable)
    (v/assert kb (list 'conversionFactor Gramme Kilo 0.001) CxTable)
    (v/assert kb (list 'conversionFactor Kilo Kilo 1) CxTable)
    (v/assert kb (tu/fwd [(list massOf '?x '?q)
                          (list 'quantityGreaterThan '?q (list 'QuantityFn 1 Kilo))]
                         (list heavy '?x))
              CxUse)
    (v/assert kb (list massOf Whale (list 'QuantityFn 5000 Gramme)) CxUse)
    (testing "the rule's context cannot see the table, so nothing compares"
      (is (empty? (believed kb heavy))))
    (testing "control: wired under the table, the same rule derives"
      (v/assert kb (list 'genlCx CxUse CxTable) C {:strength :monotonic})
      (is (= #{(list heavy Whale)} (believed kb heavy))))))

(tu/deftest-kb the-unit-table-may-arrive-last
  ;; The order-independence half.  Nothing connects `conversionFactor` to
  ;; `quantityGreaterThan` by predicate, and the mass fact that would have triggered the
  ;; rule has already arrived — so the table arriving is what has to re-join the rule.
  (tu/with-terms [Gramme Kilo Heft massOf heavy Whale]
    (v/assert kb (tu/fwd [(list massOf '?x '?q)
                          (list 'quantityGreaterThan '?q (list 'QuantityFn 1 Kilo))]
                         (list heavy '?x))
              C)
    (v/assert kb (list massOf Whale (list 'QuantityFn 5000 Gramme)) C)
    (testing "with no table the two units are their own dimensions and nothing compares"
      (is (empty? (believed kb heavy))))
    (load-mass-table kb Gramme Kilo Heft)
    (testing "the table arriving last derives what the table arriving first would have"
      (is (= #{(list heavy Whale)} (believed kb heavy))))))

;; ---- a client's own prover, built from the public API ---------------------

(defn- ranking-prover
  "A prover a client outside the engine builds with `v/prover` alone: `(outranks A B)`
  holds when A's stored `rankOf` number exceeds B's, and the answer names both rows."
  [rankOf outranks]
  (let [lvar? #(and (symbol? %) (= \? (first (name %))))
        ranks (fn [kb x context]
                (for [{:keys [id sentence]} (v/sentexes-matching kb (list rankOf x '?n) context)]
                  [(second sentence) (nth sentence 2) id]))]
    (v/prover
     {:applicable?        (fn [_ goal _] (and (seq? goal) (= outranks (first goal)) (= 3 (count goal))))
      :solve-with-support (fn [kb [_ a b] context]
                            (for [[ta na ha] (ranks kb a context)
                                  [tb nb hb] (ranks kb b context)
                                  :when (> na nb)]
                              [(cond-> {} (lvar? a) (assoc a ta) (lvar? b) (assoc b tb))
                               #{ha hb}]))
      :support-functors   #{outranks}
      :support-sources    #{rankOf}})))

(tu/deftest-kb a-client-prover-s-conclusion-goes-when-a-fact-it-read-is-retracted
  (tu/with-terms [rankOf outranks rivalOf beats Ann Bob]
    (v/add-prover kb (ranking-prover rankOf outranks))
    (let [ha (v/assert kb (list rankOf Ann 3) C)]
      (v/assert kb (list rankOf Bob 2) C)
      (v/assert kb (list rivalOf Ann Bob) C)
      (v/assert kb (tu/fwd [(list rivalOf '?x '?y) (list outranks '?x '?y)] (list beats '?x '?y)) C)
      (testing "the rule fires on the prover's answer, and the firing names the rows it read"
        (is (= #{(list beats Ann Bob)} (believed kb beats)))
        (is (= #{(list rivalOf Ann Bob) (list rankOf Ann 3) (list rankOf Bob 2)}
               (reasons kb beats (list beats Ann Bob)))))
      (v/retract! kb ha)
      (is (empty? (believed kb beats))))))

(tu/deftest-kb a-client-prover-s-source-may-arrive-after-the-rule
  (tu/with-terms [rankOf outranks rivalOf beats Ann Bob]
    (v/add-prover kb (ranking-prover rankOf outranks))
    (v/assert kb (tu/fwd [(list rivalOf '?x '?y) (list outranks '?x '?y)] (list beats '?x '?y)) C)
    (v/assert kb (list rivalOf Ann Bob) C)
    (v/assert kb (list rankOf Bob 2) C)
    (is (empty? (believed kb beats)))
    (v/assert kb (list rankOf Ann 3) C)
    (is (= #{(list beats Ann Bob)} (believed kb beats)))))

(tu/deftest-kb a-client-prover-s-solve-answers-the-bindings-it-supports
  (tu/with-terms [rankOf outranks Ann Bob Cy]
    (v/add-prover kb (ranking-prover rankOf outranks))
    (doseq [[x n] [[Ann 3] [Bob 2] [Cy 1]]] (v/assert kb (list rankOf x n) C))
    (is (= #{{'?y Bob} {'?y Cy}} (set (v/ask kb (list outranks Ann '?y) C))))
    (is (v/ask? kb (list outranks Bob Cy) C))
    (is (not (v/ask? kb (list outranks Cy Ann) C)))))

;; A datum on a source owes the rule a re-join (`chain/owe-computed-rejoins`).  A run
;; joins the rule once, behind every datum that owed it, and keeps past the computed
;; antecedent only the rows whose answer rests on one of them: the firings the datum made
;; answerable.  Ranks 0 to 4 arriving one by one make 0, 1, 2, 3 and 4 new firings.

(tu/deftest-kb a-source-datum-re-joins-only-the-rows-resting-on-it
  (tu/with-shipped-config
    (let [derive  @#'chain/derive-conclusion
          rejoin  @#'chain/rejoin-in-full
          load!   (fn [kb {:keys [rankOf outranks above person people rule]} order chain?]
                    (doseq [step order]
                      (case step
                        :rule    (vreset! rule (v/assert kb (tu/fwd [(list person '?x)
                                                                     (list outranks '?x '?y)]
                                                                    (list above '?x '?y))
                                                         C))
                        :persons (doseq [p people] (v/assert kb (list person p) C))
                        :ranks   (doseq [[i p] (map-indexed vector people)]
                                   (v/assert kb (list rankOf p i) C {:chain? chain?})))))
          terms!  (fn [kb]
                    (tu/with-terms [rankOf outranks above person Ann Bob Cy Dee Eve]
                      (v/add-prover kb (ranking-prover rankOf outranks))
                      {:rankOf rankOf :outranks outranks :above above :person person
                       :people [Ann Bob Cy Dee Eve] :rule (volatile! nil)}))
          wanted  (fn [{:keys [above people]}]
                    (set (for [i (range 5) j (range i)] (list above (people i) (people j)))))]
      (testing "ranks asserted one at a time after the rule join one row per new firing"
        (let [t    (terms! kb)
              rows (atom 0)]
          (load! kb t [:rule :persons] true)
          (with-redefs-fn {#'chain/derive-conclusion (fn [& a] (swap! rows inc) (apply derive a))}
            #(load! kb t [:ranks] true))
          (is (= 10 @rows))
          (is (= (wanted t) (believed kb (:above t))))))
      (testing "a forward chain over ranks stored unchained re-joins the rule once"
        (let [t     (terms! kb)
              joins (atom 0)]
          (load! kb t [:rule :persons :ranks] false)
          (with-redefs-fn {#'chain/rejoin-in-full
                           (fn [& a]
                             (swap! joins + (count (filter #{@(:rule t)} (second a))))
                             (apply rejoin a))}
            #(v/forward-chain kb {}))
          (is (= 1 @joins))
          (is (= (wanted t) (believed kb (:above t))))))
      (testing "and every arrival order believes the same firings"
        (doseq [order [[:rule :persons :ranks] [:rule :ranks :persons] [:persons :rule :ranks]
                       [:persons :ranks :rule] [:ranks :rule :persons] [:ranks :persons :rule]]]
          (let [t (terms! kb)]
            (load! kb t order true)
            (is (= (wanted t) (believed kb (:above t))) (pr-str order))))))))

(tu/deftest-kb a-run-re-solves-a-quoted-kind-antecedent-a-fixed-number-of-times-whatever-its-data
  ;; Every `genl` edge is a datum `ExpressionKindProver` reads, so each owes the rule a
  ;; re-join.  The count is of the solves inside the rule's own re-joins: one run solves
  ;; the k quoted forms at most twice whatever n is, where a re-join per datum is n·k.
  (tu/with-shipped-config
    (let [solve  @#'chain/solve-computed
          rejoin @#'chain/rejoin-in-full
          k      3
          solves (fn [n]
                   (tu/with-terms [quoted formula_mark]
                     (let [forms (vec (repeatedly k #(list 'Quote (list 'genl (tu/tmp-type)
                                                                        (tu/tmp-type)))))
                           rh    (v/assert kb (tu/fwd [(list quoted '?s) '(formula ?s)]
                                                      (list formula_mark '?s))
                                           C)
                           in?   (volatile! false)
                           calls (atom 0)]
                       (doseq [f forms] (v/assert kb (list quoted f) C))
                       (doseq [_ (range n)]
                         (v/assert kb (list 'genl (tu/tmp-type) (tu/tmp-type)) C {:chain? false}))
                       (with-redefs-fn {#'chain/rejoin-in-full
                                        (fn [& a]
                                          (vreset! in? (boolean (some #{rh} (second a))))
                                          (try (apply rejoin a) (finally (vreset! in? false))))
                                        #'chain/solve-computed
                                        (fn [& a]
                                          (when (and @in? (= 4 (count a))) (swap! calls inc))
                                          (apply solve a))}
                         #(v/forward-chain kb {}))
                       (is (= (set (map #(list formula_mark %) forms))
                              (believed kb formula_mark)))
                       @calls)))
          few    (solves 2)]
      (is (<= k few (* 2 k)))
      (is (= few (solves 8))))))

(tu/deftest-kb a-batch-re-joins-a-computed-rule-once-at-its-settle
  (tu/with-shipped-config
    (tu/with-terms [rankOf outranks above person Ann Bob Cy]
      (v/add-prover kb (ranking-prover rankOf outranks))
      (let [rule   (v/assert kb (tu/fwd [(list person '?x) (list outranks '?x '?y)]
                                        (list above '?x '?y))
                             C)
            rejoin @#'chain/rejoin-in-full
            joins  (atom 0)]
        (doseq [p [Ann Bob Cy]] (v/assert kb (list person p) C))
        (with-redefs-fn {#'chain/rejoin-in-full
                         (fn [& a]
                           (swap! joins + (count (filter #{rule} (second a))))
                           (apply rejoin a))}
          #(v/with-deferred-settle kb
             (doseq [[i p] (map-indexed vector [Ann Bob Cy])]
               (v/assert kb (list rankOf p i) C))))
        (is (= 1 @joins))
        (is (= #{(list above Bob Ann) (list above Cy Ann) (list above Cy Bob)}
               (believed kb above)))))))

;; ---- and what a purely arithmetic comparison still rests on ---------------

(tu/deftest-kb an-arithmetic-comparison-adds-no-supporter-of-its-own
  ;; A prover that reads nothing stored reports nothing, so `(lessThan ?a ?b)` leaves
  ;; the firing supported by the facts that bound it and the rule.
  (tu/with-terms [ageOf youngerThan Ann Bob]
    (let [h1 (v/assert kb (list ageOf Ann 10) C {:chain? false})
          h2 (v/assert kb (list ageOf Bob 20) C {:chain? false})
          rh (v/assert kb (tu/fwd [(list ageOf '?x '?a) (list ageOf '?y '?b)
                                   (list 'lessThan '?a '?b)]
                                  (list youngerThan '?x '?y))
                       C)
          ch (handle-of kb youngerThan (list youngerThan Ann Bob))]
      (is (some? ch))
      (is (= [[#{h1 h2} rh]]
             (mapv (juxt (comp set :antecedents) :informant)
                   (v/supporting-justifications kb ch)))))))

;; ---- a literal a prover answers with no support (#226, test 5) ------------

(defn- forward-reads
  "What `ask?` and two forward rules make of the ground `literal` naming `x`, once `setup`
  is stored: `{:asked … :trigger … :residual …}`.  The trigger rule has `literal` as its
  only antecedent; the residual rule joins it over `x` after a membership arriving last.
  The `^:red` tests below call it for provers that answer a literal at query time and are
  no `SupportingProver`, where no arm of `chain/join-stored-shape` computes the literal:
  a forward join reads the stored tuples alone."
  [kb setup literal x]
  (tu/with-terms [noted_t noted_r mark]
    (v/assert kb (tu/fwd [literal] (list noted_t x)) C)
    (v/assert kb (tu/fwd [(list mark '?x) (walk/postwalk-replace {x '?x} literal)]
                         (list noted_r '?x))
              C)
    (doseq [s setup] (v/assert kb s C))
    (v/assert kb (list mark x) C)
    {:asked    (v/ask? kb literal C)
     :trigger  (contains? (believed kb noted_t) (list noted_t x))
     :residual (contains? (believed kb noted_r) (list noted_r x))}))

(def ^:private read-all {:asked true :trigger true :residual true})

(tu/deftest-kb ^:red a-forward-rule-reads-the-pair-a-reflexive-predicate-proves
  (tu/with-terms [nearTo Dover]
    (is (= read-all (forward-reads kb [(list 'arity nearTo 2) (list 'reflexive nearTo)]
                                   (list nearTo Dover Dover) Dover)))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-allen-relation-two-calendar-terms-state
  (v/add-reasoner kb :calendar)
  (is (= read-all (forward-reads kb [] '(during (MonthFn 2000 3) (YearFn 2000))
                                 '(MonthFn 2000 3)))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-part-a-covering-leaves
  (tu/with-terms [pet dog cat Rex]
    (is (= read-all (forward-reads kb [(list 'covering pet dog cat) (list pet Rex)
                                       (list 'not (list dog Rex))]
                                   (list cat Rex) Rex)))))

(tu/deftest-kb ^:red a-forward-rule-reads-a-membership-a-computed-sufficient-condition-proves
  (tu/with-terms [large]
    (is (= read-all (forward-reads kb [(list 'defnSufficient large '(greaterThan ?x 10))]
                                   (list large 12) 12)))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-denial-a-failed-necessary-condition-proves
  (tu/with-terms [bachelor unmarried Tom]
    (is (= read-all (forward-reads kb [(list 'defnNecessary bachelor (list unmarried '?x))
                                       (list 'not (list unmarried Tom))]
                                   (list 'not (list bachelor Tom)) Tom)))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-denial-a-negates-pair-proves
  (tu/with-terms [scorns admires Ann Bob]
    (is (= read-all (forward-reads kb [(list 'arity scorns 2) (list 'arity admires 2)
                                       (list 'negates scorns admires) (list scorns Ann Bob)]
                                   (list 'not (list admires Ann Bob)) Ann)))))

(tu/deftest-kb ^:red a-forward-rule-reads-a-type-an-argument-declaration-states-under-constraints-only
  (tu/with-terms [livesIn place Ann Dover]
    (tu/without-entailing
     (is (= read-all (forward-reads kb [(list 'arity livesIn 2) (list 'arg livesIn 2 place)
                                        (list livesIn Ann Dover)]
                                    (list place Dover) Dover))))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-position-a-relation-s-arity-admits
  (tu/with-terms [between]
    (is (= read-all (forward-reads kb [(list 'arity between 3)]
                                   (list 'admitsArgnum between 3) between)))))

(tu/deftest-kb ^:red a-forward-rule-reads-an-argument-declaration-a-narrower-one-implies
  (tu/with-terms [feeds mammal animal]
    (is (= read-all (forward-reads kb [(list 'arity feeds 2) (list 'genl mammal animal)
                                       (list 'arg feeds 1 mammal)]
                                   (list 'arg feeds 1 animal) feeds)))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-type-a-function-s-result-declaration-states
  (tu/with-terms [CapitalFn city France]
    (is (= read-all (forward-reads kb [(list 'arity CapitalFn 1) (list 'result CapitalFn city)]
                                   (list city (list CapitalFn France)) France)))))

(tu/deftest-kb ^:red a-forward-rule-reads-the-least-common-supertype-the-taxonomy-computes
  (tu/with-terms [mammal dog cat]
    (is (= read-all (forward-reads kb [(list 'genl dog mammal) (list 'genl cat mammal)]
                                   (list 'minCommonGenl mammal dog cat) mammal)))))
