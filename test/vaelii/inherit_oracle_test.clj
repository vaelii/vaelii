;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-oracle-test
  "The two ways of finding the claims that bear on a preservation goal answer the same
  set.

  `inherit/*retrieval*` at `:auto` picks the product or the extent per goal
  (docs/inherit.md, \"What one question costs\"), so on any given KB only one of them
  runs, and a divergence would be a different answer, not a crash.

  This tests them against each other directly, on randomized KBs, comparing the raw
  claim set rather than the verdict: a future change to `undercut?` or `verdict` could
  hide a retrieval difference behind an unchanged yes/no, and the set is what those
  read.  The shapes are the ones the two paths could disagree on — several claims at
  once, mixed polarity, a negated claim, an asymmetric predicate's converse, claims at
  and off the product's edge, subsumption through a sub-predicate, and a symmetric
  predicate whose mirror can hand a match back in the other argument order."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private ctx 'CxUniverse)

(defn- comparable-claims
  "The claim set as plain data, ordered so two runs are comparable — handles are
  allocated in assertion order and are the same on both paths, but nothing here should
  depend on the order they come back in."
  [kb goal from]
  (->> (inherit/claims kb goal from)
       (map #(select-keys % [:polarity :tuple :handle :sentence :context :class]))
       (sort-by pr-str)
       vec))

(defn- both-paths-agree
  "The two retrieval paths' claim sets for `goal`, and whether they match."
  ([kb goal] (both-paths-agree kb goal ctx))
  ([kb goal from]
   (let [e (binding [inherit/*retrieval* :extent]  (comparable-claims kb goal from))
         p (binding [inherit/*retrieval* :product] (comparable-claims kb goal from))]
     (is (= e p) (str "retrieval paths disagree on " (pr-str goal)))
     e)))

;; ---- a randomized taxonomy with claims scattered over it -----------------

(defn- build-world!
  "A `depth`-deep genl chain per argument, a preserved binary predicate, and `n`
  claims placed at pseudo-random points on the two chains — some inside the goal's
  product, some outside it, some negated."
  [kb {:keys [pred chain-a chain-b n seed negations?]}]
  (let [rng (java.util.Random. (long seed))]
    (v/with-deferred-settle kb
      (doseq [chain [chain-a chain-b]
              [sub sup] (partition 2 1 chain)]
        (v/assert kb (list 'genl sub sup) ctx))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) ctx))
    (v/with-deferred-settle kb
      (dotimes [_ n]
        (let [a (nth chain-a (.nextInt rng (count chain-a)))
              b (nth chain-b (.nextInt rng (count chain-b)))
              s (list pred a b)]
          (v/assert kb (if (and negations? (zero? (.nextInt rng 3))) (list 'not s) s)
                    ctx {:strength (if (zero? (.nextInt rng 2)) :monotonic :default)}))))))

(tu/deftest-kb randomized-taxonomies-answer-the-same-claim-set
  (tu/with-terms [relOf]
    (let [chain-a (mapv (fn [i] (tu/tmp-type (str "oa" i "_t"))) (range 6))
          chain-b (mapv (fn [i] (tu/tmp-type (str "ob" i "_t"))) (range 6))]
      (build-world! kb {:pred relOf :chain-a chain-a :chain-b chain-b
                        :n 14 :seed 20260727 :negations? true})
      ;; every goal on the two chains: the leaf (whole product), the root (one tuple),
      ;; and every mixture between
      (let [found (for [a chain-a, b chain-b]
                    (count (both-paths-agree kb (list relOf a b))))]
        (is (= 36 (count found)))
        (testing "the KB is not trivially empty of claims — an oracle over nothing
                  proves nothing"
          (is (pos? (apply + found)))
          (is (some pos? found)))))))

;; ---- the shapes the two paths could differ on ---------------------------

(tu/deftest-kb a-negated-claim-is-found-the-same-way-by-both
  (tu/with-terms [dog_t animal_t cat_t feline_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) ctx))
    (v/assert kb (list 'not (list typeLargerThan animal_t feline_t)) ctx)
    (let [cs (both-paths-agree kb (list typeLargerThan dog_t cat_t))]
      (is (= [:against] (mapv :polarity cs)))
      (is (= [[animal_t feline_t]] (mapv :tuple cs))))))

(tu/deftest-kb an-asymmetric-converse-is-filed-against-the-same-tuple-either-way
  (tu/with-terms [dog_t animal_t cat_t feline_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'asymmetric typeLargerThan) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) ctx))
    ;; the converse of the goal's direction: it denies (typeLargerThan animal feline)
    (v/assert kb (list typeLargerThan feline_t animal_t) ctx)
    (let [cs (both-paths-agree kb (list typeLargerThan dog_t cat_t))]
      (is (= [:against] (mapv :polarity cs)))
      (is (= [[animal_t feline_t]] (mapv :tuple cs))
          "filed against the tuple it denies, not the tuple it is stated at"))))

(tu/deftest-kb a-sub-predicate-claim-is-found-the-same-way-by-both
  (tu/with-terms [dog_t animal_t cat_t feline_t typeLargerThan muchLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'genl muchLargerThan typeLargerThan) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) ctx))
    (v/assert kb (list muchLargerThan animal_t feline_t) ctx)
    (let [cs (both-paths-agree kb (list typeLargerThan dog_t cat_t))]
      (is (= 1 (count cs)))
      (is (= (list muchLargerThan animal_t feline_t) (:sentence (first cs)))
          "the sub-predicate's own sentence, reached through the genl fan"))))

(tu/deftest-kb a-symmetric-predicates-mirror-is-seen-the-same-way-by-both
  (tu/with-terms [dog_t animal_t cat_t feline_t nearTo]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'symmetric nearTo) ctx)
      (v/assert kb (list 'transitiveInArgInverse nearTo 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse nearTo 2 'genl) ctx))
    ;; stated in the other order: only the mirror reaches the goal's tuple
    (v/assert kb (list nearTo feline_t animal_t) ctx)
    (let [cs (both-paths-agree kb (list nearTo dog_t cat_t))]
      (is (seq cs) "the mirror is read on both paths or on neither"))))

(tu/deftest-kb the-strongest-statement-of-a-tuple-wins-on-both-paths
  (tu/with-terms [dog_t animal_t cat_t feline_t typeLargerThan CxSide]
    (v/assert kb (list 'genlCx CxSide ctx) ctx)
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) ctx))
    ;; the same sentence twice, at two strengths, in two contexts CxSide sees
    (v/assert kb (list typeLargerThan animal_t feline_t) ctx {:strength :default})
    (v/assert kb (list typeLargerThan animal_t feline_t) CxSide {:strength :monotonic})
    (let [cs (both-paths-agree kb (list typeLargerThan dog_t cat_t) CxSide)]
      (is (= 1 (count cs)) "one claim per tuple, not one per sentex")
      (is (= :monotonic (:class (first cs)))
          "the strongest, and both paths agree which that is"))))

(tu/deftest-kb a-goal-off-the-product-finds-nothing-on-either-path
  (tu/with-terms [dog_t animal_t cat_t feline_t bird_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) ctx))
    (v/assert kb (list typeLargerThan animal_t feline_t) ctx)
    (is (empty? (both-paths-agree kb (list typeLargerThan bird_t cat_t)))
        "bird is not below animal, so nothing reaches this tuple")))

(tu/deftest-kb one-preserved-position-binds-the-other-on-both-paths
  (tu/with-terms [dog_t animal_t cat_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx))
    (v/assert kb (list typeLargerThan animal_t cat_t) ctx)
    (testing "the ground argument must match exactly"
      (is (seq (both-paths-agree kb (list typeLargerThan dog_t cat_t))))
      (is (empty? (both-paths-agree kb (list typeLargerThan dog_t animal_t)))))))

(tu/deftest-kb defeat-is-respected-identically-by-both-paths
  (tu/with-terms [dog_t animal_t cat_t feline_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl cat_t feline_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) ctx))
    (let [h (v/assert kb (list typeLargerThan animal_t feline_t) ctx)]
      (is (seq (both-paths-agree kb (list typeLargerThan dog_t cat_t))))
      (v/retract! kb h)
      (is (empty? (both-paths-agree kb (list typeLargerThan dog_t cat_t)))
          "a retracted claim is gone from both paths"))))
