;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.literal-cache-engine-test
  "The literal cache as the engine sees it: sharing, scoping, invalidation, and the two
  ways a cached answer could be wrong — a truncated run storing a prefix as though it
  were the extent, and a writing scope storing a value its own writes invalidated.

  Entry-count claims are made against `matches-visible` directly, because that is the
  unit cached; a whole `ask` also fills the cache with the metadata probes its provers
  issue, which are real entries and not the ones under test."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- entries [kb] @(reasoning/matches kb))

(defn- fresh-cache!
  "Clear the cache so a count means what the test did, not what asserting the fixture's
  own facts happened to leave behind."
  [kb]
  (lc/clear-cache kb))

(defn- matches [kb sentence context]
  (doall (res/matches-visible kb sentence context)))

(defn- bound-values [ms v] (set (keep #(get (second %) v) ms)))

;; ---- sharing -------------------------------------------------------------

(tu/deftest-kb two-spellings-of-one-literal-share-one-entry
  (tu/with-terms [parentOf Tom Bob Ann CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (v/assert kb (list parentOf Tom Ann) CxFarm)
    (fresh-cache! kb)
    (let [a (matches kb (list parentOf Tom '?y) CxFarm)
          b (matches kb (list parentOf Tom '?z) CxFarm)]
      (testing "each caller gets the full extent, under its own variable name"
        (is (= #{Bob Ann} (bound-values a '?y)))
        (is (= #{Bob Ann} (bound-values b '?z)))
        (is (empty? (bound-values b '?y)) "the other caller's name is not what comes back"))
      (testing "and they share a single entry"
        (is (= 1 (count (entries kb))))))))

(tu/deftest-kb three-spellings-share-the-one-stored-value
  (tu/with-terms [parentOf Tom Bob CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (fresh-cache! kb)
    (doseq [v '[?y ?z ?w]] (matches kb (list parentOf Tom v) CxFarm))
    (is (= 1 (count (entries kb))))
    (testing "the second and third callers read the very value the first stored"
      (let [stored (:value (val (first (entries kb))))]
        (is (identical? stored (:value (val (first (entries kb))))))
        (is (= 1 (count stored)))))))

(tu/deftest-kb partially-ground-literals-share-on-their-ground-arguments
  ;; the common post-substitution case, and the one a rule join produces most
  (tu/with-terms [between A B C CxFarm]
    (v/assert kb (list between A B C) CxFarm)
    (fresh-cache! kb)
    (matches kb (list between A '?m '?n) CxFarm)
    (matches kb (list between A '?p '?q) CxFarm)
    (is (= 1 (count (entries kb))) "same ground prefix, same entry")
    (matches kb (list between B '?m '?n) CxFarm)
    (is (= 2 (count (entries kb))) "a different ground argument is a different question")))

(tu/deftest-kb a-repeated-variable-does-not-share-with-two-distinct-ones
  ;; the `goal-key` trap, end to end: (P ?x ?x) and (P ?x ?y) must get different
  ;; entries AND different answers
  (tu/with-terms [likes A B CxFarm]
    (v/assert kb (list likes A B) CxFarm)
    (v/assert kb (list likes A A) CxFarm)
    (fresh-cache! kb)
    (let [distinct-vars (matches kb (list likes '?x '?y) CxFarm)
          repeated-var  (matches kb (list likes '?x '?x) CxFarm)]
      (is (= 2 (count distinct-vars)) "(likes ?x ?y) sees both facts")
      (is (= 1 (count repeated-var)) "(likes ?x ?x) sees only the reflexive one")
      (is (= 2 (count (entries kb))) "and they are two entries, not one"))))

(tu/deftest-kb the-same-literal-in-two-contexts-does-not-share
  (tu/with-terms [parentOf Tom Bob Ann CxFarm CxBarn]
    (v/assert kb (list 'genlCx CxBarn CxFarm) CxFarm)
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (v/assert kb (list parentOf Tom Ann) CxBarn)
    (fresh-cache! kb)
    (let [farm (matches kb (list parentOf Tom '?y) CxFarm)
          barn (matches kb (list parentOf Tom '?y) CxBarn)]
      (testing "each context sees what it should — Barn inherits Farm, not the reverse"
        (is (= #{Bob} (bound-values farm '?y)))
        (is (= #{Bob Ann} (bound-values barn '?y))))
      (is (= 2 (count (entries kb))) "context is part of the key"))))

;; ---- invalidation --------------------------------------------------------

(tu/deftest-kb an-unrelated-assertion-retires-every-entry
  (tu/with-terms [parentOf Tom Bob Ann sky_colour CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (fresh-cache! kb)
    (is (= #{Bob} (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y)))
    (let [before (:hits (lc/stats kb))]
      (is (= #{Bob} (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y)))
      (is (= (inc before) (:hits (lc/stats kb))) "an unmoved clock is a hit"))
    (testing "a fact about something else still moves the clock, so the next read rebuilds"
      (v/assert kb (list sky_colour Tom) CxFarm)
      (let [before (:hits (lc/stats kb))]
        (is (= #{Bob} (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y)))
        (is (= before (:hits (lc/stats kb))) "not a hit — the clock moved")))
    (testing "and a new fact is seen"
      (let [h (v/assert kb (list parentOf Tom Ann) CxFarm)]
        (is (= #{Bob Ann} (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y)))
        (testing "as is its retraction — a belief flip moves the clock too"
          (v/retract! kb h)
          (is (= #{Bob} (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y))))))))

;; ---- the two ways a stored answer could be wrong -------------------------

(tu/deftest-kb a-bounded-run-stores-nothing-it-did-not-finish
  ;; the truncation hazard: a consumer that stopped early must not leave a prefix behind
  ;; that a later unbounded ask is served as though it were the whole extent
  (tu/with-terms [parentOf Tom CxFarm]
    (let [kids (vec (repeatedly 5 tu/tmp-ind))]
      (doseq [k kids] (v/assert kb (list parentOf Tom k) CxFarm))
      (fresh-cache! kb)
      (testing "a capped run yields exactly its cap"
        (let [r (v/ask-within kb (list parentOf Tom '?y) CxFarm {:max-results 1})]
          (is (= 1 (count (:results r))))
          (is (= :capped (:status r)))))
      (testing "and the unbounded ask that follows still sees all five"
        (is (= (set kids)
               (set (map #(get % '?y) (v/ask kb (list parentOf Tom '?y) CxFarm)))))))))

(tu/deftest-kb a-lazy-consumer-taking-one-realizes-one
  ;; invariant 2: caching must not make a bounded stream eager.  `storing` accumulates
  ;; as the consumer pulls and stores only when the source itself ends.
  (tu/with-terms [parentOf Tom CxFarm]
    (doseq [k (repeatedly 5 tu/tmp-ind)] (v/assert kb (list parentOf Tom k) CxFarm))
    (fresh-cache! kb)
    (let [ms (res/matches-visible kb (list parentOf Tom '?y) CxFarm)]
      (is (= 1 (count (take 1 ms))))
      (is (empty? (entries kb)) "an unfinished stream stored nothing")
      (is (= 5 (count (doall ms))))
      (is (= 1 (count (entries kb))) "running dry is what stores it"))))

(tu/deftest-kb forward-chaining-leaves-no-stale-answer-behind
  ;; a scope that writes while it reads (chain/process-datum, under observe/with-pin)
  ;; moves the clock under its own reads, so nothing it computed can be served after it
  (tu/with-terms [dog animal Rex CxFarm]
    (v/assert kb (list 'genl dog animal) CxFarm)
    (fresh-cache! kb)
    (is (empty? (bound-values (matches kb (list animal '?x) CxFarm) '?x)))
    (testing "a fact that forward chaining acts on is visible to the next query"
      (v/assert kb (list dog Rex) CxFarm)
      (is (v/ask? kb (list animal Rex) CxFarm)))
    (testing "and a chaining run's own conclusions are what a fresh query reads"
      (v/forward-chain kb)
      (is (v/ask? kb (list animal Rex) CxFarm)))))

;; ---- the toggle ----------------------------------------------------------

(tu/deftest-kb off-is-free-and-answers-the-same
  (tu/with-terms [parentOf Tom Bob Ann CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (v/assert kb (list parentOf Tom Ann) CxFarm)
    (fresh-cache! kb)
    (let [on  (binding [lc/*enabled* true]  (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y))
          _   (fresh-cache! kb)
          off (binding [lc/*enabled* false] (bound-values (matches kb (list parentOf Tom '?y) CxFarm) '?y))]
      (is (= #{Bob Ann} on))
      (is (= on off) "the toggle changes cost, not results")
      (is (empty? (entries kb)) "and off allocates no entry"))))
