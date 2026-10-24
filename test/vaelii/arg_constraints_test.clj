;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arg-constraints-test
  "The argument-constraint chokepoint (`res/arg-constraints`, `res/arg-constraints-at`) over
  the core vocabulary, whose forward rules store the declaration each sugar spelling
  stands for: `(args P T)` stores `(argAndRest P 1 T)`, so the chokepoint looks up `arg`
  and `argAndRest` alone at the instance level and still answers for `args`."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private instance-spellings
  "Every spelling of an instance-level argument constraint, sugar included."
  '#{arg argAndRest args arg1 arg2 arg3 arg4 arg5})

(defn- read-with-lookups
  "`[entries looked-up]`: `res/arg-constraints` of `pred` read from the store (the memo
  bypassed), and the instance-level declaration functors the read looked up."
  [kb pred]
  (let [seen (atom #{})
        orig res/constraining-predicates]
    (with-redefs [tax/clock-held               (fn [_ _ _ read] (read))
                  res/constraining-predicates (fn [kb kind & more]
                                                (swap! seen conj kind)
                                                (apply orig kb kind more))]
      [(res/arg-constraints kb pred 'CxUniverse)
       (into #{} (filter instance-spellings) @seen)])))

(tu/deftest-kb an-args-declaration-reaches-the-chokepoint-as-its-argAndRest-twin
  (tu/with-terms [herdOf animal_k]
    (v/assert kb (list 'genl animal_k 'thing) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate herdOf) 'CxUniverse)
    (let [h (v/assert kb (list 'args herdOf animal_k) 'CxUniverse)]
      (is (seq (v/sentexes-matching kb (list 'argAndRest herdOf 1 animal_k) 'CxUniverse))
          "the forward rule stores the argAndRest twin")
      (let [[entries looked-up] (read-with-lookups kb herdOf)]
        (is (= [{:from 1 :to nil :type animal_k :kind :instance :via herdOf}] entries)
            "the twin is the one entry, a tail from 1")
        (is (= '#{arg argAndRest} looked-up)
            "the instance-level lookups are arg and argAndRest alone"))
      (testing "retracting the args declaration takes its twin, and the entry, with it"
        (v/retract! kb h)
        (is (empty? (res/arg-constraints kb herdOf 'CxUniverse)))))))

(tu/deftest-kb the-argnum-chokepoint-answers-an-args-declaration-at-every-position
  (tu/with-terms [herdOf animal_k]
    (v/assert kb (list 'genl animal_k 'thing) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate herdOf) 'CxUniverse)
    (v/assert kb (list 'args herdOf animal_k) 'CxUniverse)
    (doseq [n [1 2 7]]
      (is (= [animal_k] (map :type (res/arg-constraints-at kb herdOf 'CxUniverse n)))
          (str "position " n)))))

(tu/deftest-kb the-argument-type-prover-reads-an-args-declaration-through-its-twin
  (tu/with-terms [herdOf animal_k Herd1 Rex]
    (v/assert kb (list 'genl animal_k 'thing) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate herdOf) 'CxUniverse)
    (v/assert kb (list 'args herdOf animal_k) 'CxUniverse)
    (v/assert kb (list herdOf Herd1 Rex) 'CxUniverse)
    (is (= [{}] (prover-types/solve (provers/->ArgTypeProver) kb (list animal_k Rex)
                                    'CxUniverse)))))

;; ---- the entry point: assert-time checks and entailments -------------------

(defn- check-with-lookups
  "`[violations looked-up]`: `v/check` of `sentence` (the memo bypassed), or where it
  reports nothing the argument conviction `assert` holds the fact inert under
  (`tu/write-conviction`), and the instance-level declaration functors the entry point
  looked up while checking it."
  [kb sentence]
  (let [seen (atom #{})
        orig res/constraining-predicates]
    (with-redefs [tax/clock-held              (fn [_ _ _ read] (read))
                  res/constraining-predicates (fn [kb kind & more]
                                                (swap! seen conj kind)
                                                (apply orig kb kind more))]
      [(vec (or (seq (v/check kb sentence 'CxUniverse))
                (some-> (tu/write-conviction kb sentence 'CxUniverse) vector)))
       (into #{} (filter instance-spellings) @seen)])))

(tu/deftest-kb the-args-sugar-rule-is-the-one-core-txt-states
  ;; tests on a KB without core.txt assert `tu/args-sugar-rule` to read the `args`
  ;; spelling, so it has to be the rule core.txt ships
  (is (str/includes? (slurp (io/resource "kb/upper/core.txt")) (pr-str tu/args-sugar-rule))))

(tu/deftest-kb the-entry-point-reads-an-args-declaration-through-its-twin
  ;; the assert-time checks look up `arg` and `argAndRest` alone, as the chokepoint does:
  ;; an `args` declaration is refused and entails through its stored twin, so a KB
  ;; stating only the twin gets the same refusals
  (tu/with-terms [herdOf flockOf animal_k Herd1 Rex]
    (v/assert kb (list 'genl animal_k 'thing) 'CxUniverse)
    (doseq [p [herdOf flockOf]]
      (v/assert kb (list 'variable_arity_predicate p) 'CxUniverse))
    (v/assert kb (list 'args herdOf animal_k) 'CxUniverse)
    (v/assert kb (list 'argAndRest flockOf 1 animal_k) 'CxUniverse)
    (let [twin                (v/handle-of kb (list 'argAndRest herdOf 1 animal_k) 'CxUniverse)
          [herd-vs looked-up] (check-with-lookups kb (list herdOf Herd1 "notAnAnimal"))
          [flock-vs]          (check-with-lookups kb (list flockOf Herd1 "notAnAnimal"))]
      (is (some? twin) "the forward rule stores the twin")
      (testing "the refusal names the twin, and is the one a KB stating only argAndRest gets"
        (is (= [:arg-type] (map :type herd-vs)))
        (is (re-find #"\(argAndRest from 1, position 2 of " (:message (first herd-vs))))
        (is (= (map #(dissoc % :sentence :message) herd-vs)
               (map #(dissoc % :sentence :message) flock-vs)))
        (is (= (:message (first flock-vs))
               (str/replace (:message (first herd-vs)) (str herdOf) (str flockOf)))))
      (testing "the instance-level lookups are arg and argAndRest alone"
        (is (= '#{arg argAndRest} looked-up)))
      (testing "the membership the declaration entails rests on the twin alone"
        (v/assert kb (list herdOf Herd1 Rex) 'CxUniverse)
        (let [sups (:support (v/why kb (v/handle-of kb (list animal_k Rex) 'CxUniverse)))]
          (is (= ['argAndRest] (map :informant sups)))
          (is (some #{twin} (map :handle (:because (first sups))))))))))
