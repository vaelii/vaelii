;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arg-constraints-test
  "The argument-constraint chokepoint (`res/arg-constraints`, `res/arg-constraints-at`) over
  the upper ontology, whose `kb/upper/interface-rules.txt` forward rules store the
  declaration each sugar spelling stands for: `(args P T)` stores `(argAndRest P 1 T)`,
  so the chokepoint looks up `arg` and `argAndRest` alone at the instance level and still
  answers for `args`."
  (:require [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

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

(tu/deftest-kb the-refusal-record-holds-no-firing-of-a-rule-that-does-not-forward-chain
  (let [named (fn [] (into #{} (for [[rh es] @(reasoning/refused kb)
                                     :when (and (set? es)
                                                (not (rules/forward-sentex? (p/get-sentex (:records kb) rh))))]
                                 rh)))]
    (is (empty? (named)) "after the core load")
    (tu/with-terms [herdOf animal_k]
      (v/assert kb (list 'genl animal_k 'thing) 'CxUniverse)
      (v/assert kb (list 'variable_arity_predicate herdOf) 'CxUniverse)
      (v/assert kb (list 'args herdOf animal_k) 'CxUniverse)
      (is (empty? (named)) "after an args declaration"))))

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
      ;; the subject is the entailment, which the constraint-only reading does not make
      (testing "the membership the declaration entails rests on the twin alone"
        (tu/with-entailing
          (v/assert kb (list herdOf Herd1 Rex) 'CxUniverse)
          (let [sups (:support (tu/why-root kb (v/handle-of kb (list animal_k Rex) 'CxUniverse)))]
            (is (= ['argAndRest] (map #(kb/mint-kind kb (:informant %)) sups)))
            (is (some #{twin} (map :handle (:because (first sups)))))))))))

;; ---- an inverse carries its partner's argument types ----------------------
;; (inverse P Q) says (P a b) holds exactly when (Q b a) does, so argument 1 of P is
;; argument 2 of Q and argument 2 of P is argument 1 of Q.  core.txt's forward rules type
;; each position of one partner by the swapped position of the other, for arg and for
;; quotedArg.  The rules read the inverse from ?p to ?q only, and inverse is symmetric, so
;; one inverse sentence is read from both partners.

(defn- believed-in-universe?
  "Is `sentence` stored in CxUniverse and believed there?"
  [kb sentence]
  (boolean (some->> (v/handle-of kb sentence 'CxUniverse) (v/in? kb))))

(defn- inverse-supports
  "The antecedent sentences of each justification of `sentence` in CxUniverse that reads
  `:supports` there and rests on an `inverse` sentence, as a set of sets."
  [kb sentence]
  (when-some [h (v/handle-of kb sentence 'CxUniverse)]
    (let [verdicts (v/justification-verdicts kb h 'CxUniverse)]
      (into #{} (comp (filter #(= :supports (verdicts (:id %))))
                      (map #(into #{} (map (fn [a] (:sentence (v/sentex kb a)))) (:antecedents %)))
                      (filter #(some (fn [s] (= 'inverse (first s))) %)))
            (v/supporting-justifications kb h)))))

(tu/deftest-kb an-inverse-types-each-argument-of-its-partner-at-the-swapped-position
  (tu/with-terms [holds heldBy names namedBy holder_k held_k]
    (doseq [t [holder_k held_k]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [p [holds heldBy names namedBy]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (let [inv (v/assert kb (list 'inverse holds heldBy) 'CxUniverse)]
      (v/assert kb (list 'arg holds 1 holder_k) 'CxUniverse)
      (v/assert kb (list 'arg holds 2 held_k) 'CxUniverse)
      ;; the quotedArg declarations sit on the second partner of the inverse and on the
      ;; first, so the pair reads the inverse in both directions
      (v/assert kb (list 'inverse names namedBy) 'CxUniverse)
      (v/assert kb (list 'quotedArg namedBy 1 'string) 'CxUniverse)
      (v/assert kb (list 'quotedArg names 1 'symbol) 'CxUniverse)
      (testing "arg: each position of the first partner types the swapped position of the second"
        (is (true? (believed-in-universe? kb (list 'arg heldBy 2 holder_k))))
        (is (true? (believed-in-universe? kb (list 'arg heldBy 1 held_k))))
        (is (false? (believed-in-universe? kb (list 'arg heldBy 1 holder_k))))
        ;; inverse is symmetric, so the inverse stores in sorted order, heldBy first, and
        ;; the rule reads it through the mirror, naming (symmetric inverse)
        (is (= #{#{(list 'inverse heldBy holds) (list 'arg holds 1 holder_k) '(symmetric inverse)}}
               (inverse-supports kb (list 'arg heldBy 2 holder_k)))))
      (testing "quotedArg: a declaration on either partner types the swapped position of the other"
        (is (true? (believed-in-universe? kb (list 'quotedArg names 2 'string))))
        (is (true? (believed-in-universe? kb (list 'quotedArg namedBy 2 'symbol))))
        (is (false? (believed-in-universe? kb (list 'quotedArg names 1 'string)))))
      (testing "retracting the inverse takes the derived declarations with it"
        (v/retract! kb inv)
        (is (false? (believed-in-universe? kb (list 'arg heldBy 2 holder_k))))
        (is (false? (believed-in-universe? kb (list 'arg heldBy 1 held_k))))))))

(tu/deftest-kb one-inverse-sentence-types-both-partners
  ;; core.txt's rules read (inverse ?p ?q) from ?p to ?q only, and inverse is symmetric,
  ;; so the one sentence (inverse parentOf childOf) also reads as (inverse childOf
  ;; parentOf) and a declaration on either partner types the other
  (tu/with-terms [parentOf childOf parent_k child_k]
    (doseq [t [parent_k child_k]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [p [parentOf childOf]]
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'inverse parentOf childOf) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 1 parent_k) 'CxUniverse)
    (v/assert kb (list 'arg childOf 1 child_k) 'CxUniverse)
    (testing "childOf from parentOf"
      (is (true? (believed-in-universe? kb (list 'arg childOf 2 parent_k)))))
    (testing "parentOf from childOf"
      (is (true? (believed-in-universe? kb (list 'arg parentOf 2 child_k)))))))

(tu/deftest-kb childOf-has-the-argument-types-of-parentOf-through-the-inverse
  ;; life.txt states (inverse parentOf childOf) beside childOf's two declarations, and the
  ;; rules derive both declarations from parentOf's.  inverse is symmetric, so it stores
  ;; as (inverse childOf parentOf) and the rules read it through the mirror
  (doseq [n [1 2]]
    (is (= #{#{'(inverse childOf parentOf) '(symmetric inverse)
               (list 'arg 'parentOf (- 3 n) 'organism)}}
           (inverse-supports kb (list 'arg 'childOf n 'organism)))
        (str "position " n))))

(tu/deftest-kb an-inert-inverse-types-no-argument
  ;; space.txt states each converse pair inert, and an inert sentence is no premise, so
  ;; westOf's declarations rest on no inverse
  (doseq [n [1 2]]
    (is (= #{} (inverse-supports kb (list 'arg 'westOf n 'spatial))) (str "position " n))))
