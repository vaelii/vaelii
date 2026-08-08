;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicate-subsumption-test
  "Predicate subsumption in matching: `(genl fatherOf parentOf)` makes a `parentOf`
  query (and antecedent, and goal) reach a stored `fatherOf` fact — the subtype rule
  the type hierarchy already gives, generalized to the predicate hierarchy.

  It reuses the existing `genl` closure (no new taxonomy state): `wff` already accepts
  a genl edge between predicates (it only forbids individuals), so the whole of the
  change is `res/match1` and `res/match-pattern` fanning the functor over its
  `specs` for every arity instead of only for unary literals.  These pin the new
  capability, that it follows belief (retract the edge and it is gone), and — via
  `match-pattern-equals-manual-union` — that the fan is exactly the union over the
  spec closure.

  The **backward dual** lives here too: a rule concluding a *spec* of the goal's
  predicate answers the goal, so `candidate-rules` draws candidates from
  `res/concluding-rule-handles` (`specs ∩ rules-by-consequent`) and the chainers
  unify the goal against the consequent with `res/subsuming-unify`.  Exercised with
  a **backward-only** rule so forward chaining cannot materialize the subtype
  conclusion and mask the backward path."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(tu/deftest-kb match1-subsumes-a-sub-predicate
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})
    (testing "a fatherOf fact satisfies a parentOf antecedent, binding the arguments"
      (is (= {(symbol "?x") A (symbol "?y") B}
             (res/match1 kb (list parentOf (symbol "?x") (symbol "?y")) (list fatherOf A B)))))
    (testing "an unrelated predicate does not"
      (is (nil? (res/match1 kb (list parentOf (symbol "?x") (symbol "?y")) (list loves A B)))))
    (testing "the equal-functor case is a plain unify, unchanged"
      (is (= {(symbol "?x") A (symbol "?y") B}
             (res/match1 kb (list parentOf (symbol "?x") (symbol "?y")) (list parentOf A B)))))))

(tu/deftest-kb match-pattern-reaches-sub-predicate-facts
  (tu/with-terms [fatherOf parentOf A B C D]
    (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'CoreContext {:strength :monotonic})
    (v/assert kb (list parentOf C D) 'CoreContext {:strength :monotonic})
    (testing "a parentOf query matches both the direct parentOf fact and the fatherOf one"
      (let [sentences (set (map (fn [[h _]] (:sentence (v/sentex kb h)))
                                (res/match-pattern kb (list parentOf (symbol "?x") (symbol "?y")) '?ctx)))]
        (is (contains? sentences (list parentOf C D)))
        (is (contains? sentences (list fatherOf A B)))))
    (testing "a fatherOf query does NOT reach the parentOf fact (subsumption is one-way)"
      (let [sentences (set (map (fn [[h _]] (:sentence (v/sentex kb h)))
                                (res/match-pattern kb (list fatherOf (symbol "?x") (symbol "?y")) '?ctx)))]
        (is (contains? sentences (list fatherOf A B)))
        (is (not (contains? sentences (list parentOf C D))))))))

(tu/deftest-kb match-pattern-equals-manual-union
  ;; the oracle: the generalized fan is exactly the union of raw matches over the spec
  ;; closure — nothing more, nothing less
  (tu/with-terms [fatherOf motherOf parentOf A B C D E F]
    (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})
    (v/assert kb (list 'genl motherOf parentOf) 'CoreContext {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'CoreContext {:strength :monotonic})
    (v/assert kb (list motherOf C D) 'CoreContext {:strength :monotonic})
    (v/assert kb (list parentOf E F) 'CoreContext {:strength :monotonic})
    (doseq [pat [(list parentOf (symbol "?x") (symbol "?y"))
                 (list parentOf A (symbol "?y"))
                 (list parentOf (symbol "?x") D)
                 (list parentOf E F)]]
      (let [got   (proj (res/match-pattern kb pat '?ctx))
            manual (proj (mapcat (fn [f'] (res/raw-match kb (cons f' (rest pat)) '?ctx))
                                 (tax/specs (:taxonomy kb) parentOf)))]
        (is (= manual got) (str "match-pattern diverged from the spec-union on " (pr-str pat)))))))

(tu/deftest-kb forward-chaining-fires-through-subsumption
  (tu/with-terms [fatherOf parentOf hasChild A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})
    (v/assert kb (list 'implies (list parentOf (symbol "?x") (symbol "?y"))
                       (list hasChild (symbol "?y") (symbol "?x"))) 'CoreContext)
    (v/assert kb (list fatherOf A B) 'CoreContext {:strength :monotonic})
    (testing "a rule on the super-predicate fires on a sub-predicate fact"
      (is (seq (v/sentexes-matching kb (list hasChild B A) 'CoreContext))))))

(tu/deftest-kb ask-reaches-through-subsumption-and-follows-belief
  (tu/with-terms [fatherOf parentOf A B]
    (v/assert kb (list fatherOf A B) 'CoreContext {:strength :monotonic})
    (testing "before the genl edge, a parentOf goal is not answered by the fatherOf fact"
      (is (not (v/ask? kb (list parentOf A B) 'CoreContext))))
    (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})]
      (testing "with the edge, the goal is answered by subsumption"
        (is (v/ask? kb (list parentOf A B) 'CoreContext)))
      (testing "retracting the edge withdraws the subsumption (belief-following)"
        (v/retract! kb edge)
        (is (not (v/ask? kb (list parentOf A B) 'CoreContext)))))))

;; ---- backward dual: a subtype-concluding rule answers a supertype goal ----

(tu/deftest-kb subsuming-unify-honors-consequent-specificity
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})
    (let [x (symbol "?x") y (symbol "?y")]
      (testing "a fatherOf consequent answers a parentOf goal, binding the arguments"
        (is (= {x A y B}
               (res/subsuming-unify kb (list parentOf x y) (list fatherOf A B)))))
      (testing "an unrelated consequent does not"
        (is (nil? (res/subsuming-unify kb (list parentOf x y) (list loves A B)))))
      (testing "the equal-functor case is a plain unify, unchanged"
        (is (= {x A y B}
               (res/subsuming-unify kb (list parentOf x y) (list parentOf A B)))))
      (testing "one-way: a parentOf consequent does NOT answer a fatherOf goal (super ⊉ sub)"
        (is (nil? (res/subsuming-unify kb (list fatherOf x y) (list parentOf A B))))))))

(tu/deftest-kb concluding-rule-handles-is-specs-intersect-index
  (tu/with-terms [fatherOf parentOf sonOf A B]
    (let [rule (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                              'CoreContext {:direction :backward})]
      (testing "before the edge, only fatherOf's own goal reaches the rule"
        (is (contains? (res/concluding-rule-handles kb fatherOf) rule))
        (is (not (contains? (res/concluding-rule-handles kb parentOf) rule))))
      (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})]
        (testing "with fatherOf ⊑ parentOf, a parentOf goal reaches the fatherOf rule"
          (is (contains? (res/concluding-rule-handles kb parentOf) rule)))
        (testing "and it is exactly specs(parentOf) ∩ rules-by-consequent"
          (is (= (into #{} (mapcat #(seq (p/rules-by-consequent (:index kb) %)))
                       (tax/specs (:taxonomy kb) parentOf))
                 (res/concluding-rule-handles kb parentOf))))
        (testing "retracting the edge withdraws the rule from the parentOf goal"
          (v/retract! kb edge)
          (is (not (contains? (res/concluding-rule-handles kb parentOf) rule))))))))

(tu/deftest-kb all-chainers-answer-supertype-goal-from-subtype-rule
  ;; fatherOf ⊑ parentOf, and a *backward-only* rule concludes the subtype fatherOf
  ;; from a sonOf fact.  Forward chaining cannot fire a backward rule, so (fatherOf A B)
  ;; is never stored — the only way to answer a parentOf goal is to backward-chain the
  ;; rule and unify parentOf against its fatherOf consequent by subsumption.
  (tu/with-terms [fatherOf parentOf sonOf A B]
    (let [p (symbol "?p") c (symbol "?c")]
      (v/assert kb (list 'genl fatherOf parentOf) 'CoreContext {:strength :monotonic})
      (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                     'CoreContext {:direction :backward})
      (v/assert kb (list sonOf B A) 'CoreContext {:strength :monotonic})
      (testing "the subtype conclusion is never materialized (backward rule, no forward firing)"
        (is (nil? (v/handle-of kb (list fatherOf A B) 'CoreContext)))
        (is (empty? (v/sentexes-matching kb (list parentOf A B) 'CoreContext))))
      (testing "the node engine answers the parentOf goal via the fatherOf-concluding rule, with the right binding"
        (is (v/query? kb (list parentOf p c) 'CoreContext {:max-depth 2}))
        (is (contains? (set (v/query kb (list parentOf p c) 'CoreContext {:max-depth 2}))
                       {p A c B})))
      (testing "prove (recur DFS) agrees"
        (is (v/provable? kb (list parentOf p c) 'CoreContext))
        (is (some #(and (= A (% p)) (= B (% c))) (v/prove kb (list parentOf p c) 'CoreContext))))
      (testing "backward (lazy) agrees"
        (is (some #(and (= A (% p)) (= B (% c))) (v/prove kb (list parentOf p c) 'CoreContext)))))))

;; ---- the fan-out is scoped by the vantage --------------------------------
;; A genl edge connects a sub-predicate's facts to a supertype pattern only where
;; the edge is visible: matching from a context that cannot see `(genl dog animal)`
;; does not reach `(dog Muffet)` from `(animal ?x)`, however visible the fact itself.
;; Both retrieval paths — the reference fan-out and the set-algebra twin — must
;; agree, and the any-context read keeps the global fan.

(tu/deftest-kb the-matching-fan-out-walks-only-visible-genl-edges
  (tu/with-terms [dog_t animal_t Muffet AContext BContext]
    (v/assert kb (list 'genlContext AContext 'CoreContext) 'CoreContext)
    (v/assert kb (list 'genlContext BContext 'CoreContext) 'CoreContext)
    (v/assert kb (list 'genl dog_t animal_t) AContext)
    (v/assert kb (list dog_t Muffet) 'CoreContext)
    (doseq [hierarchical? [true false]]
      (binding [res/*hierarchical-retrieval* hierarchical?]
        (testing (str "hierarchical-retrieval " hierarchical?)
          (testing "the edge is visible from A, so the supertype query reaches the fact"
            (is (seq (v/ask kb (list animal_t '?x) AContext))))
          (testing "and invisible from the sibling, which sees the fact but not the edge"
            (is (empty? (v/ask kb (list animal_t '?x) BContext))))
          (testing "the any-context read keeps the global fan"
            (is (seq (v/ask kb (list animal_t '?x) '?ctx)))))))))

(tu/deftest-kb a-subtype-concluding-rule-answers-only-where-the-edge-is-visible
  ;; the backward dual of the scoped fan-out: concluding-rule-handles intersects the
  ;; consequent index with the spec closure *as seen from the goal's context*, so a
  ;; rule concluding fatherOf answers a parentOf goal exactly where
  ;; (genl fatherOf parentOf) is visible — in all three chainers.
  (tu/with-terms [fatherOf parentOf sonOf A B AContext BContext]
    (let [p (symbol "?p") c (symbol "?c")]
      (v/assert kb (list 'genlContext AContext 'CoreContext) 'CoreContext)
      (v/assert kb (list 'genlContext BContext 'CoreContext) 'CoreContext)
      (v/assert kb (list 'genl fatherOf parentOf) AContext {:strength :monotonic})
      (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                     'CoreContext {:direction :backward})
      (v/assert kb (list sonOf B A) 'CoreContext {:strength :monotonic})
      (testing "the goal is answered where the subtype edge is visible"
        (is (v/query? kb (list parentOf p c) AContext {:max-depth 2}))
        (is (v/provable? kb (list parentOf p c) AContext))
        (is (some #(and (= A (% p)) (= B (% c))) (v/prove kb (list parentOf p c) AContext))))
      (testing "and not where it is out of sight, though rule and fact are visible"
        (is (not (v/query? kb (list parentOf p c) BContext {:max-depth 2})))
        (is (not (v/provable? kb (list parentOf p c) BContext)))
        (is (empty? (v/prove kb (list parentOf p c) BContext))))
      (testing "the subtype goal itself still answers from either sibling"
        (is (v/query? kb (list fatherOf p c) BContext {:max-depth 2}))))))
