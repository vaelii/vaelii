;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negative-subsumption-test
  "Subsumption under a negation, which runs the other way.  `(genl dog animal)` puts a
  stored `(dog Muffet)` under the pattern `(animal ?x)`; the same edge puts a stored
  `(not (animal Muffet))` under the pattern `(not (dog ?x))`, because `dog ⊑ animal`
  entails `¬animal ⊑ ¬dog`.  The two directions are exclusive, and the wrong one is
  what these pin hardest: `(not (dog Muffet))` says nothing about `(not (animal ?x))`.

  Every site the positive fan runs at has a negative twin here — `res/match1` (the
  forward trigger), `res/match-pattern` (retrieval), `res/subsuming-unify` and the
  backward chainers, `rules/trigger-keys` (which rules an arriving negation reaches) —
  plus the oracle that the retrieval fan is exactly the union over the genl closure, and
  the belief- and vantage-following the positive side already has.

  The companion for the positive direction is `predicate-subsumption-test`; the
  antecedent index key a negation files under is `negated-antecedent-index-test`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))
(defn- negate [s] (list 'not s))

;; ---- the trigger match ---------------------------------------------------

(tu/deftest-kb match1-subsumes-a-genl-under-a-negation
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxCore {:strength :monotonic})
    (let [x (symbol "?x") y (symbol "?y")]
      (testing "a negated parentOf fact satisfies a negated fatherOf antecedent"
        (is (= {x A y B}
               (res/match1 kb (negate (list fatherOf x y)) (negate (list parentOf A B))))))
      (testing "and the reverse does not — the positive direction is not the negative one"
        (is (nil? (res/match1 kb (negate (list parentOf x y)) (negate (list fatherOf A B))))))
      (testing "an unrelated predicate does not"
        (is (nil? (res/match1 kb (negate (list fatherOf x y)) (negate (list loves A B))))))
      (testing "the equal-functor case is a plain unify, unchanged"
        (is (= {x A y B}
               (res/match1 kb (negate (list parentOf x y)) (negate (list parentOf A B))))))
      (testing "polarity does not cross in either direction"
        (is (nil? (res/match1 kb (negate (list fatherOf x y)) (list parentOf A B))))
        (is (nil? (res/match1 kb (list parentOf x y) (negate (list fatherOf A B)))))))))

(tu/deftest-kb match1-subsumes-a-genl-under-a-negation-for-a-unary-type
  ;; a negation is two elements long, so it has the form the unary-type branch takes and
  ;; is told apart from one by the negation arm running first; the same claim at arity 1
  (tu/with-terms [dog_t animal_t Muffet]
    (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
    (let [x (symbol "?x")]
      (is (= {x Muffet}
             (res/match1 kb (negate (list dog_t x)) (negate (list animal_t Muffet)))))
      (is (nil? (res/match1 kb (negate (list animal_t x)) (negate (list dog_t Muffet))))))))

;; ---- retrieval -----------------------------------------------------------

(tu/deftest-kb match-pattern-reaches-a-negated-genl-fact
  (tu/with-terms [dog_t animal_t A B]
    (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
    (v/assert kb (negate (list animal_t A)) 'CxCore {:strength :monotonic})
    (v/assert kb (negate (list dog_t B)) 'CxCore {:strength :monotonic})
    (testing "a negated dog query matches the negated animal fact and the direct one"
      (let [sentences (set (map (fn [[h _]] (:sentence (v/sentex kb h)))
                                (res/match-pattern kb (negate (list dog_t (symbol "?x"))) '?ctx)))]
        (is (contains? sentences (negate (list animal_t A))))
        (is (contains? sentences (negate (list dog_t B))))))
    (testing "a negated animal query does NOT reach the negated dog fact (one-way)"
      (let [sentences (set (map (fn [[h _]] (:sentence (v/sentex kb h)))
                                (res/match-pattern kb (negate (list animal_t (symbol "?x"))) '?ctx)))]
        (is (contains? sentences (negate (list animal_t A))))
        (is (not (contains? sentences (negate (list dog_t B)))))))))

(tu/deftest-kb negative-match-pattern-equals-the-manual-genl-union
  ;; the oracle, mirroring `predicate-subsumption-test`'s: the negative fan is exactly
  ;; the union of raw matches over the genl closure of the body's functor
  (tu/with-terms [dog_t canine_t animal_t A B C]
    (v/assert kb (list 'genl dog_t canine_t) 'CxCore {:strength :monotonic})
    (v/assert kb (list 'genl canine_t animal_t) 'CxCore {:strength :monotonic})
    (v/assert kb (negate (list animal_t A)) 'CxCore {:strength :monotonic})
    (v/assert kb (negate (list canine_t B)) 'CxCore {:strength :monotonic})
    (v/assert kb (negate (list dog_t C)) 'CxCore {:strength :monotonic})
    (doseq [pat [(negate (list dog_t (symbol "?x")))
                 (negate (list canine_t (symbol "?x")))
                 (negate (list animal_t (symbol "?x")))
                 (negate (list dog_t A))
                 (negate (list dog_t C))]]
      (let [body   (second pat)
            got    (proj (res/match-pattern kb pat '?ctx))
            manual (proj (mapcat (fn [f'] (res/raw-match kb (negate (cons f' (rest body))) '?ctx))
                                 (tax/genls-global (reasoning/taxonomy kb) (first body))))]
        (is (= manual got)
            (str "the negative fan diverged from the genl-union on " (pr-str pat)))))))

(tu/deftest-kb super-predicates-is-the-genl-closure
  (tu/with-terms [dog_t animal_t]
    (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
    (is (= (tax/genls-global (reasoning/taxonomy kb) dog_t) (res/super-predicates kb dog_t nil)))
    (is (contains? (res/super-predicates kb dog_t nil) animal_t))
    (is (not (contains? (res/sub-predicates kb dog_t nil) animal_t)))))

;; ---- ask, belief, and the chainers ---------------------------------------

(tu/deftest-kb ask-reaches-through-a-negation-and-follows-belief
  (tu/with-terms [dog_t animal_t A]
    (v/assert kb (negate (list animal_t A)) 'CxCore {:strength :monotonic})
    (testing "before the genl edge, the negated subtype goal is unanswered"
      (is (not (v/ask? kb (negate (list dog_t A)) 'CxCore))))
    (let [edge (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})]
      (testing "with the edge, the contrapositive answers it"
        (is (v/ask? kb (negate (list dog_t A)) 'CxCore)))
      (testing "retracting the edge withdraws it (belief-following)"
        (v/retract! kb edge)
        (is (not (v/ask? kb (negate (list dog_t A)) 'CxCore)))))))

(tu/deftest-kb forward-chaining-fires-a-negated-antecedent-through-the-genl-edge
  (tu/with-terms [dog_t animal_t notADog A]
    (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
    (v/assert-rule kb [(negate (list dog_t (symbol "?x")))]
                   (list notADog (symbol "?x")) 'CxCore {:direction :forward})
    (v/assert kb (negate (list animal_t A)) 'CxCore {:strength :monotonic})
    (testing "a rule negated on the subtype fires on a fact negated on the supertype"
      (is (seq (v/sentexes-matching kb (list notADog A) 'CxCore))))))

(tu/deftest-kb the-negative-firing-rests-on-the-genl-edge-it-climbed
  ;; A firing that reached its antecedent through a `genl` edge names a witness for the
  ;; path it climbed (`chain/subsumption-links`), so dropping the edge withdraws what it
  ;; licensed.  The negative fan climbs the same edges in the other direction and owes
  ;; the same witness — without it the conclusion outlives its own reason.
  (tu/with-terms [dog_t animal_t notADog A]
    (let [x    (symbol "?x")
          edge (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})]
      (v/assert-rule kb [(negate (list dog_t x))] (list notADog x) 'CxCore {:direction :forward})
      (v/assert kb (negate (list animal_t A)) 'CxCore {:strength :monotonic})
      (is (seq (v/sentexes-matching kb (list notADog A) 'CxCore))
          "the rule fires through the contrapositive")
      (v/retract! kb edge)
      (is (empty? (v/sentexes-matching kb (list notADog A) 'CxCore))
          "and the conclusion goes with the edge it climbed"))))

(tu/deftest-kb a-genl-edge-arriving-last-fires-the-negated-antecedent
  ;; Order independence, the taxonomy half: an edge asserted *after* the facts changes
  ;; which antecedents they satisfy, and the semi-naive agenda cannot see that — the
  ;; arriving datum is the edge.  `special/subsumption-seeds` puts the newly matchable
  ;; facts back on the agenda, and under a negation the newly matchable ones sit on the
  ;; **genls** of the edge's super, not on the specs of its sub.
  (tu/with-terms [dog_t animal_t notADog A]
    (let [x (symbol "?x")]
      (v/assert-rule kb [(negate (list dog_t x))] (list notADog x) 'CxCore {:direction :forward})
      (v/assert kb (negate (list animal_t A)) 'CxCore {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list notADog A) 'CxCore))
          "nothing relates the two predicates yet")
      (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
      (is (seq (v/sentexes-matching kb (list notADog A) 'CxCore))
          "the edge arriving last derives what it would have derived arriving first"))))

(tu/deftest-kb forward-chaining-does-not-fire-the-other-way
  (tu/with-terms [dog_t animal_t notAnAnimal A]
    (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
    (v/assert-rule kb [(negate (list animal_t (symbol "?x")))]
                   (list notAnAnimal (symbol "?x")) 'CxCore {:direction :forward})
    (v/assert kb (negate (list dog_t A)) 'CxCore {:strength :monotonic})
    (testing "not being a dog is not not being an animal"
      (is (empty? (v/sentexes-matching kb (list notAnAnimal A) 'CxCore))))))

(tu/deftest-kb subsuming-unify-honors-consequent-genl-under-a-negation
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxCore {:strength :monotonic})
    (let [x (symbol "?x") y (symbol "?y")]
      (testing "a negated parentOf consequent answers a negated fatherOf goal"
        (is (= {x A y B}
               (res/subsuming-unify kb (negate (list fatherOf x y))
                                    (negate (list parentOf A B))))))
      (testing "one-way: a negated fatherOf consequent does not answer a negated parentOf goal"
        (is (nil? (res/subsuming-unify kb (negate (list parentOf x y))
                                       (negate (list fatherOf A B))))))
      (testing "an unrelated consequent does not"
        (is (nil? (res/subsuming-unify kb (negate (list fatherOf x y))
                                       (negate (list loves A B))))))
      (testing "the equal-functor case is a plain unify, unchanged"
        (is (= {x A y B}
               (res/subsuming-unify kb (negate (list parentOf x y))
                                    (negate (list parentOf A B))))))
      (testing "polarity does not cross"
        (is (nil? (res/subsuming-unify kb (negate (list fatherOf x y))
                                       (list parentOf A B))))))))

(tu/deftest-kb all-chainers-answer-a-negated-subtype-goal-from-a-negated-supertype-rule
  ;; the backward dual, with a *backward-only* rule so forward chaining cannot
  ;; materialize `(not (animal A))` and mask the backward path
  (tu/with-terms [dog_t animal_t robot_t A]
    (let [x (symbol "?x")]
      (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
      (v/assert-rule kb [(list robot_t x)] (negate (list animal_t x))
                     'CxCore {:direction :backward})
      (v/assert kb (list robot_t A) 'CxCore {:strength :monotonic})
      (testing "the negated supertype conclusion is never materialized"
        (is (nil? (v/handle-of kb (negate (list animal_t A)) 'CxCore)))
        (is (empty? (v/sentexes-matching kb (negate (list dog_t A)) 'CxCore))))
      (testing "the node engine answers the negated subtype goal, with the right binding"
        (is (v/query? kb (negate (list dog_t x)) 'CxCore {:max-depth 2}))
        (is (contains? (set (v/query kb (negate (list dog_t x)) 'CxCore {:max-depth 2}))
                       {x A})))
      (testing "prove agrees"
        (is (v/provable? kb (negate (list dog_t x)) 'CxCore))
        (is (some #(= A (% x)) (v/prove kb (negate (list dog_t x)) 'CxCore)))))))

;; ---- which rules an arriving negation reaches ----------------------------

(tu/deftest-kb trigger-keys-fan-the-negated-specs-off-the-rule-roster
  (tu/with-terms [dog_t animal_t other_t grounded A]
    (v/assert kb (list 'genl dog_t animal_t) 'CxCore {:strength :monotonic})
    (let [tax'   (reasoning/taxonomy kb)
          roster #(deref (reasoning/rule-antecedents kb))]
      (testing "with no rule reading a negation, an arriving negation names no key"
        (is (empty? (rules/trigger-keys tax' (negate (list animal_t A)) (roster)))))
      (v/assert-rule kb [(negate (list dog_t (symbol "?x")))]
                     (list grounded (symbol "?x")) 'CxCore {:direction :forward})
      (testing "a negation on the supertype reaches the rule negated on the subtype"
        (is (= [[:not dog_t]]
               (vec (rules/trigger-keys tax' (negate (list animal_t A)) (roster))))))
      (testing "and a negation on the subtype reaches it too — genls is reflexive"
        (is (= [[:not dog_t]]
               (vec (rules/trigger-keys tax' (negate (list dog_t A)) (roster))))))
      (testing "a negation on an unrelated predicate reaches nothing"
        (is (empty? (rules/trigger-keys tax' (negate (list other_t A)) (roster)))))
      (testing "a positive fact still names its predicate and its supertypes"
        (is (= (tax/genls-global tax' dog_t)
               (set (rules/trigger-keys tax' (list dog_t A) (roster)))))))))

;; ---- the fan is scoped by the vantage ------------------------------------

(tu/deftest-kb the-negative-fan-walks-only-visible-genl-edges
  (tu/with-terms [dog_t animal_t Muffet CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxCore) 'CxCore)
    (v/assert kb (list 'genlCx CxB 'CxCore) 'CxCore)
    (v/assert kb (list 'genl dog_t animal_t) CxA)
    (v/assert kb (negate (list animal_t Muffet)) 'CxCore)
    (doseq [hierarchical? [true false]]
      (binding [res/*hierarchical-retrieval* hierarchical?]
        (testing (str "hierarchical-retrieval " hierarchical?)
          (testing "the edge is visible from A, so the negated subtype query reaches the fact"
            (is (seq (v/ask kb (negate (list dog_t (symbol "?x"))) CxA))))
          (testing "and invisible from the sibling, which sees the fact but not the edge"
            (is (empty? (v/ask kb (negate (list dog_t (symbol "?x"))) CxB))))
          (testing "the any-context read keeps the global fan"
            (is (seq (v/ask kb (negate (list dog_t (symbol "?x"))) '?ctx)))))))))

;; ---- the exception re-check reaches the same distance -------------------

(tu/deftest-kb a-negated-exception-conjunct-is-re-checked-contravariantly
  ;; The exception path's half of the contravariant fan.  An `exceptWhen` conjunct
  ;; `(not (winged ?x))` is answered by a stored `(not (appendaged X))` once
  ;; `winged ⊑ appendaged`, so the arrival of that negation has to reach the firing whose
  ;; exception it now blocks.  The narrowing filter (`settle/reachable-predicates`) takes
  ;; both closures under a negation for exactly this: `genls` for the negative trigger
  ;; that answers the conjunct directly, `specs` for the positive one that moves it by
  ;; contradicting what the conjunct reads.
  (tu/with-terms [winged_t appendaged_t bird_t flies Opus]
    (let [x (symbol "?x")]
      (v/assert kb (list 'genl winged_t appendaged_t) 'CxCore {:strength :monotonic})
      (v/assert kb (list 'exceptWhen (negate (list winged_t x))
                         (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list 'and (list bird_t x)) (list flies x)))))
                'CxCore)
      (v/assert kb (list bird_t Opus) 'CxCore)
      (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx))
          "the rule concludes while nothing excepts it")
      (v/assert kb (negate (list appendaged_t Opus)) 'CxCore)
      (is (empty? (v/sentexes-matching kb (list flies Opus) '?ctx))
          "a negation on the supertype satisfies the negated exception, contravariantly"))))

(tu/deftest-kb a-contravariant-exception-is-released-when-the-negation-goes
  ;; The withdrawal direction of the same channel, and a separate claim from the arrival:
  ;; blocking and releasing are two passes of the settle loop, and the narrowing
  ;; (`settle/reachable-predicates`) is asked once per direction.  A trigger that reaches
  ;; the firing on the way in but not on the way out leaves the conclusion swept with
  ;; nothing to derive it again, which is what `released-rules` re-chains.
  (tu/with-terms [winged_t appendaged_t bird_t flies Opus]
    (let [x (symbol "?x")]
      (v/assert kb (list 'genl winged_t appendaged_t) 'CxCore {:strength :monotonic})
      (v/assert kb (list 'exceptWhen (negate (list winged_t x))
                         (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list 'and (list bird_t x)) (list flies x)))))
                'CxCore)
      (v/assert kb (list bird_t Opus) 'CxCore)
      (let [neg (v/assert kb (negate (list appendaged_t Opus)) 'CxCore)]
        (is (empty? (v/sentexes-matching kb (list flies Opus) '?ctx))
            "the supertype negation satisfies the negated exception")
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx))
            "and the conclusion is derived again once it goes")))))

(tu/deftest-kb a-negated-exception-conjunct-still-sees-its-own-predicate
  ;; the other half of the union: the `specs` side, which a positive trigger moves
  (tu/with-terms [winged_t bird_t flies Opus]
    (let [x (symbol "?x")]
      (v/assert kb (list 'exceptWhen (negate (list winged_t x))
                         (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list 'and (list bird_t x)) (list flies x)))))
                'CxCore)
      (v/assert kb (list bird_t Opus) 'CxCore)
      (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx)))
      (let [neg (v/assert kb (negate (list winged_t Opus)) 'CxCore)]
        (is (empty? (v/sentexes-matching kb (list flies Opus) '?ctx))
            "the exception holds on its own predicate")
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx))
            "and is released when the negation goes")))))
