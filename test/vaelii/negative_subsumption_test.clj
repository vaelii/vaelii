;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negative-subsumption-test
  "Subsumption under a negation, which runs the other way.  `(genl dog animal)` puts a
  stored `(dog Muffet)` under the pattern `(animal ?x)`; the same edge puts a stored
  `(not (animal Muffet))` under the pattern `(not (dog ?x))`, because a `:monotonic`
  `dog ⊑ animal` entails `¬animal ⊑ ¬dog`; a `:default` one does not.  The two directions
  are exclusive, and the wrong one is what these assert hardest: `(not (dog Muffet))` says
  nothing about `(not (animal ?x))`.

  Every site the positive fan runs at has a negative twin here — `res/match1` (the
  forward trigger), `res/match-pattern` (retrieval), `res/subsuming-unify` and the
  backward chainers, `rules/trigger-keys` (which rules an arriving negation reaches) —
  plus the oracle that the retrieval fan is exactly the union over the genl closure, and
  the belief- and vantage-following the positive side already has.

  The companion for the positive direction is `predicate-subsumption-test`; the
  antecedent index key a negation files under is `negated-antecedent-index-test`."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))
(defn- negate [s] (list 'not s))

;; ---- the trigger match ---------------------------------------------------

(tu/deftest-kb match1-subsumes-a-genl-under-a-negation
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
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
    (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
    (let [x (symbol "?x")]
      (is (= {x Muffet}
             (res/match1 kb (negate (list dog_t x)) (negate (list animal_t Muffet)))))
      (is (nil? (res/match1 kb (negate (list animal_t x)) (negate (list dog_t Muffet))))))))

;; ---- retrieval -----------------------------------------------------------

(tu/deftest-kb match-pattern-reaches-a-negated-genl-fact
  (tu/with-terms [dog_t animal_t A B]
    (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
    (v/assert kb (negate (list animal_t A)) 'CxUniverse {:strength :monotonic})
    (v/assert kb (negate (list dog_t B)) 'CxUniverse {:strength :monotonic})
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
    (v/assert kb (list 'genl dog_t canine_t) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl canine_t animal_t) 'CxUniverse {:strength :monotonic})
    (v/assert kb (negate (list animal_t A)) 'CxUniverse {:strength :monotonic})
    (v/assert kb (negate (list canine_t B)) 'CxUniverse {:strength :monotonic})
    (v/assert kb (negate (list dog_t C)) 'CxUniverse {:strength :monotonic})
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
    (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
    (is (= (tax/genls-global (reasoning/taxonomy kb) dog_t) (res/super-predicates kb dog_t nil)))
    (is (contains? (res/super-predicates kb dog_t nil) animal_t))
    (is (not (contains? (res/sub-predicates kb dog_t nil) animal_t)))))

;; ---- ask, belief, and the chainers ---------------------------------------

(tu/deftest-kb ask-reaches-through-a-negation-and-follows-belief
  (tu/with-terms [dog_t animal_t A]
    (v/assert kb (negate (list animal_t A)) 'CxUniverse {:strength :monotonic})
    (testing "before the genl edge, the negated subtype goal is unanswered"
      (is (not (v/ask? kb (negate (list dog_t A)) 'CxUniverse))))
    (let [edge (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})]
      (testing "with the edge, the contrapositive answers it"
        (is (v/ask? kb (negate (list dog_t A)) 'CxUniverse)))
      (testing "retracting the edge withdraws it (belief-following)"
        (v/retract! kb edge)
        (is (not (v/ask? kb (negate (list dog_t A)) 'CxUniverse)))))))

(tu/deftest-kb forward-chaining-fires-a-negated-antecedent-through-the-genl-edge
  (tu/with-terms [dog_t animal_t notADog A]
    (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(negate (list dog_t (symbol "?x")))]
                   (list notADog (symbol "?x")) 'CxUniverse {:direction :forward})
    (v/assert kb (negate (list animal_t A)) 'CxUniverse {:strength :monotonic})
    (testing "a rule negated on the subtype fires on a fact negated on the supertype"
      (is (seq (v/sentexes-matching kb (list notADog A) 'CxUniverse))))))

(tu/deftest-kb the-negative-firing-rests-on-the-genl-edge-it-climbed
  ;; A firing that reached its antecedent through a `genl` edge names a witness for the
  ;; path it climbed (`chain/subsumption-links`), so dropping the edge withdraws what it
  ;; licensed.  The negative fan climbs the same edges in the other direction and owes
  ;; the same witness — without it the conclusion outlives its own reason.
  (tu/with-terms [dog_t animal_t notADog A]
    (let [x    (symbol "?x")
          edge (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})]
      (v/assert-rule kb [(negate (list dog_t x))] (list notADog x) 'CxUniverse {:direction :forward})
      (v/assert kb (negate (list animal_t A)) 'CxUniverse {:strength :monotonic})
      (is (seq (v/sentexes-matching kb (list notADog A) 'CxUniverse))
          "the rule fires through the contrapositive")
      (v/retract! kb edge)
      (is (empty? (v/sentexes-matching kb (list notADog A) 'CxUniverse))
          "and the conclusion goes with the edge it climbed"))))

(tu/deftest-kb a-genl-edge-arriving-last-fires-the-negated-antecedent
  ;; Order independence, the taxonomy half: an edge asserted *after* the facts changes
  ;; which antecedents they satisfy, and the semi-naive agenda cannot see that — the
  ;; arriving datum is the edge.  `special/subsumption-seeds` puts the newly matchable
  ;; facts back on the agenda, and under a negation the newly matchable ones sit on the
  ;; **genls** of the edge's super, not on the specs of its sub.
  (tu/with-terms [dog_t animal_t notADog A]
    (let [x (symbol "?x")]
      (v/assert-rule kb [(negate (list dog_t x))] (list notADog x) 'CxUniverse {:direction :forward})
      (v/assert kb (negate (list animal_t A)) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list notADog A) 'CxUniverse))
          "nothing relates the two predicates yet")
      (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
      (is (seq (v/sentexes-matching kb (list notADog A) 'CxUniverse))
          "the edge arriving last derives what it would have derived arriving first"))))

(defn- negative-seeds-by-definition
  "The negative half of `special/subsumption-seeds` of the `[sub super]` pairs `edges`, one
  pair at a time and from its definition alone: for a pair whose `sub` reaches, down its
  signed spec closure, a predicate some stored rule reads under a negation, the believed
  negative facts on a predicate of `super`'s signed closure up."
  [kb edges]
  (let [idx  (:index kb)
        tx   (reasoning/taxonomy kb)
        negs (into #{} (comp (filter vector?) (map second)) (reads/as-stored-rule-keys idx))]
    (into #{} (mapcat (fn [[sub super]]
                        (when (some negs (rules/signed-reach tx :down sub))
                          (for [f (rules/signed-reach tx :up super)
                                h (reads/as-stored-with-functor idx f)
                                :when (and (jtms/in? (reasoning/tms kb) h)
                                           (sx/negative? (v/sentex kb h)))]
                            h))))
          edges)))

(tu/deftest-kb a-batch-of-edges-seeds-what-its-edges-seed-one-at-a-time
  (tu/with-terms [top_t animal_t dog_t puppy_t notPuppy seen relLow relHigh relTop notLow
                  A B C]
    (let [x     (symbol "?x")
          y     (symbol "?y")
          M     {:strength :monotonic}
          kinds (vec (repeatedly 24 #(tu/tmp-type "kind")))
          edges (into [(list 'genl puppy_t dog_t) (list 'genl dog_t animal_t)
                       (list 'genl animal_t top_t) (list 'genl relHigh relTop)]
                      (map #(list 'genl % animal_t))
                      kinds)
          agree (fn [label]
                  (let [batch (special/batch-subsumption-seeds kb edges)
                        each  (into #{} (mapcat #(special/subsumption-seeds kb %)) edges)
                        named (negative-seeds-by-definition kb (mapcat special/sentence-edges edges))]
                    (testing label
                      (is (= (count batch) (count (set batch))) "each seed appears once")
                      (is (= each (set batch)) "the batch seeds the union of its edges' seeds")
                      (is (set/subset? named (set batch))
                          "the batch seeds every negative fact the definition names"))
                    (set batch)))]
      (v/assert-rule kb [(negate (list puppy_t x))] (list notPuppy x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb [(list animal_t x)] (list seen x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb [(negate (list relLow x y))] (list notLow x y) 'CxUniverse {:direction :forward})
      (v/assert kb (negate (list animal_t A)) 'CxUniverse M)
      (v/assert kb (negate (list top_t C)) 'CxUniverse M)
      (v/assert kb (negate (list relTop A B)) 'CxUniverse M)
      (v/assert kb (list puppy_t B) 'CxUniverse M)
      (doseq [k kinds] (v/assert kb (list k (tu/tmp-ind "Kid")) 'CxUniverse M))
      (doseq [e edges] (v/assert kb e 'CxUniverse M))
      (let [free (agree "on a KB declaring no genlInverse edge")]
        (is (contains? free (v/handle-of kb (negate (list animal_t A)) 'CxUniverse)))
        (is (contains? free (v/handle-of kb (negate (list top_t C)) 'CxUniverse)))
        (is (not (contains? free (v/handle-of kb (negate (list relTop A B)) 'CxUniverse)))))
      (v/assert kb (list 'genlInverse relLow relHigh) 'CxUniverse M)
      (let [signed (agree "on a KB declaring one")]
        (is (contains? signed (v/handle-of kb (negate (list animal_t A)) 'CxUniverse)))
        (is (contains? signed (v/handle-of kb (negate (list relTop A B)) 'CxUniverse)))))))

(tu/deftest-kb forward-chaining-does-not-fire-the-other-way
  (tu/with-terms [dog_t animal_t notAnAnimal A]
    (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(negate (list animal_t (symbol "?x")))]
                   (list notAnAnimal (symbol "?x")) 'CxUniverse {:direction :forward})
    (v/assert kb (negate (list dog_t A)) 'CxUniverse {:strength :monotonic})
    (testing "not being a dog is not not being an animal"
      (is (empty? (v/sentexes-matching kb (list notAnAnimal A) 'CxUniverse))))))

;; ---- a :default edge does not contrapose ---------------------------------

(tu/deftest-kb a-denial-answers-a-negated-subtype-goal-through-a-monotonic-edge-only-in-every-order
  ;; the two KBs of #188: a stored `(not (pb Zz))`, and a backward rule concluding it
  (doseq [strength [:default :monotonic]
          derived? [false true]
          order    (tu/orders (if derived? [:edge :rule :fact] [:edge :deny]))]
    (tu/with-terms [pa_t pb_t pc_t Zz]
      (let [x      (symbol "?x")
            mono?  (= :monotonic strength)
            writes {:edge #(v/assert kb (list 'genl pa_t pb_t) 'CxUniverse {:strength strength})
                    :deny #(v/assert kb (negate (list pb_t Zz)) 'CxUniverse {:strength :monotonic})
                    :rule #(v/assert-rule kb [(list pc_t x)] (negate (list pb_t x)) 'CxUniverse
                                          {:direction :backward})
                    :fact #(v/assert kb (list pc_t Zz) 'CxUniverse {:strength :monotonic})}]
        (doseq [w order] ((writes w)))
        (testing [strength order]
          (if derived?
            (is (= (if mono? :false :unknown)
                   (:verdict (v/argue kb (list pa_t Zz) 'CxUniverse {:max-depth 5}))))
            (do (is (= mono? (v/query? kb (negate (list pa_t Zz)) 'CxUniverse)))
                (is (= (if mono? :false :unknown) (:verdict (v/argue kb (list pa_t Zz) 'CxUniverse)))))))))))

(tu/deftest-kb a-negated-antecedent-fires-through-a-monotonic-edge-only
  (doseq [strength [:default :monotonic]]
    (tu/with-terms [pa_t pb_t notPa A]
      (let [x (symbol "?x")]
        (v/assert kb (list 'genl pa_t pb_t) 'CxUniverse {:strength strength})
        (v/assert-rule kb [(negate (list pa_t x))] (list notPa x) 'CxUniverse {:direction :forward})
        (v/assert kb (negate (list pb_t A)) 'CxUniverse {:strength :monotonic})
        (is (= (= :monotonic strength)
               (boolean (seq (v/sentexes-matching kb (list notPa A) 'CxUniverse))))
            (str strength))))))

(tu/deftest-kb a-monotonic-supporter-arriving-last-fires-the-negated-antecedent-where-it-is-seen
  ;; the edge is installed throughout, so only its class moves: the second supporter's
  ;; arrival and retraction reach the firing as an edge arriving and leaving does, and a
  ;; rule in CxUniverse places its conclusion in CxSide, the context holding the edge at
  ;; :monotonic, not in CxUniverse, which holds it at :default
  (doseq [rule-cx [:side :universe]]
    (tu/with-terms [pa_t pb_t notPa A CxSide]
      (let [x    (symbol "?x")
            seen (fn [cx] (v/ask? kb (list notPa A) cx))]
        (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genl pa_t pb_t) 'CxUniverse {:strength :default})
        (v/assert-rule kb [(negate (list pa_t x))] (list notPa x)
                       (if (= :side rule-cx) CxSide 'CxUniverse) {:direction :forward})
        (v/assert kb (negate (list pb_t A)) 'CxUniverse {:strength :monotonic})
        (testing rule-cx
          (is (not (seen CxSide)) "the default supporter licenses nothing")
          (let [mono (v/assert kb (list 'genl pa_t pb_t) CxSide {:strength :monotonic})]
            (is (= [true false] [(seen CxSide) (seen 'CxUniverse)])
                "the monotonic supporter licenses the firing where it is seen")
            (v/retract! kb mono)
            (is (not (seen CxSide)) "and the firing leaves with it, though the default supporter stays")))))))

(tu/deftest-kb a-negated-exception-blocks-through-a-monotonic-edge-where-it-is-seen
  ;; the exception (not (pa ?x)) holds of A through pa ⊑ pb in CxSide, which holds the
  ;; edge at :monotonic, and not in CxUniverse, which holds it at :default: the guard
  ;; defeat is placed in CxSide.  With the CxUniverse edge at :monotonic it blocks in both.
  (doseq [[universe-edge seen] [[:default [true false]] [:monotonic [false false]]]]
    (tu/with-terms [pa_t pb_t r_t s_t A CxSide]
      (let [x (symbol "?x")]
        (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genl pa_t pb_t) 'CxUniverse {:strength universe-edge})
        (v/assert kb (list 'genl pa_t pb_t) CxSide {:strength :monotonic})
        (v/assert kb (list 'exceptWhen (negate (list pa_t x))
                           (list 'set/defaultRule
                                 (list 'set/forwardRule (rules/rule-sentence [(list r_t x)] (list s_t x)))))
                  'CxUniverse)
        (v/assert kb (list r_t A) 'CxUniverse {:strength :monotonic})
        (v/assert kb (negate (list pb_t A)) 'CxUniverse {:strength :monotonic})
        (is (= seen (mapv #(v/ask? kb (list s_t A) %) ['CxUniverse CxSide])) (str universe-edge))))))

(tu/deftest-kb subsuming-unify-honors-consequent-genl-under-a-negation
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
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
      (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list robot_t x)] (negate (list animal_t x))
                     'CxUniverse {:direction :backward})
      (v/assert kb (list robot_t A) 'CxUniverse {:strength :monotonic})
      (testing "the negated supertype conclusion is never materialized"
        (is (nil? (v/handle-of kb (negate (list animal_t A)) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (negate (list dog_t A)) 'CxUniverse))))
      (testing "the node engine answers the negated subtype goal, with the right binding"
        (is (v/query? kb (negate (list dog_t x)) 'CxUniverse {:max-depth 2}))
        (is (contains? (set (v/query kb (negate (list dog_t x)) 'CxUniverse {:max-depth 2}))
                       {x A})))
      (testing "prove agrees"
        (is (v/provable? kb (negate (list dog_t x)) 'CxUniverse))
        (is (some #(= A (% x)) (v/prove kb (negate (list dog_t x)) 'CxUniverse)))))))

;; ---- which rules an arriving negation reaches ----------------------------

(tu/deftest-kb trigger-keys-fan-the-negated-specs-off-the-rule-key-set
  (tu/with-terms [dog_t animal_t other_t grounded A]
    (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
    (let [tax' (reasoning/taxonomy kb)]
      (testing "with no rule reading a negation, an arriving negation names no key"
        (is (empty? (rules/trigger-keys tax' (negate (list animal_t A)) (:index kb)))))
      (v/assert-rule kb [(negate (list dog_t (symbol "?x")))]
                     (list grounded (symbol "?x")) 'CxUniverse {:direction :forward})
      (testing "a negation on the supertype reaches the rule negated on the subtype"
        (is (= [[:not dog_t]]
               (vec (rules/trigger-keys tax' (negate (list animal_t A)) (:index kb))))))
      (testing "and a negation on the subtype reaches it too — genls is reflexive"
        (is (= [[:not dog_t]]
               (vec (rules/trigger-keys tax' (negate (list dog_t A)) (:index kb))))))
      (testing "a negation on an unrelated predicate reaches nothing"
        (is (empty? (rules/trigger-keys tax' (negate (list other_t A)) (:index kb)))))
      (testing "a positive fact names no key while no rule reads its predicate or a supertype"
        (is (empty? (rules/trigger-keys tax' (list dog_t A) (:index kb)))))
      (v/assert-rule kb [(list animal_t (symbol "?x"))]
                     (list grounded (symbol "?x")) 'CxUniverse {:direction :forward})
      (testing "a positive fact names the supertypes some rule reads"
        (is (= [animal_t] (rules/trigger-keys tax' (list dog_t A) (:index kb))))))))

;; ---- the fan is scoped by the vantage ------------------------------------

(tu/deftest-kb the-negative-fan-walks-only-visible-genl-edges
  (tu/with-terms [dog_t animal_t Muffet CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl dog_t animal_t) CxA {:strength :monotonic})
    (v/assert kb (negate (list animal_t Muffet)) 'CxUniverse)
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
  ;; exception it now blocks.  The narrowing filter (`recheck/reachable-predicates`) takes
  ;; both closures under a negation for exactly this: `genls` for the negative trigger
  ;; that answers the conjunct directly, `specs` for the positive one that moves it by
  ;; contradicting what the conjunct reads.
  (tu/with-terms [winged_t appendaged_t bird_t flies Opus]
    (let [x (symbol "?x")]
      (v/assert kb (list 'genl winged_t appendaged_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'exceptWhen (negate (list winged_t x))
                         (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list 'and (list bird_t x)) (list flies x)))))
                'CxUniverse)
      (v/assert kb (list bird_t Opus) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx))
          "the rule concludes while nothing excepts it")
      (v/assert kb (negate (list appendaged_t Opus)) 'CxUniverse)
      (is (empty? (v/sentexes-matching kb (list flies Opus) '?ctx))
          "a negation on the supertype satisfies the negated exception, contravariantly"))))

(tu/deftest-kb a-contravariant-exception-is-released-when-the-negation-goes
  ;; The withdrawal direction of the same channel, and a separate claim from the arrival:
  ;; blocking and releasing are two passes of the settle loop, and the narrowing
  ;; (`recheck/reachable-predicates`) is asked once per direction.  A trigger that reaches
  ;; the firing on the way in but not on the way out leaves the conclusion swept with
  ;; nothing to derive it again, which is what `released-rules` re-chains.
  (tu/with-terms [winged_t appendaged_t bird_t flies Opus]
    (let [x (symbol "?x")]
      (v/assert kb (list 'genl winged_t appendaged_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'exceptWhen (negate (list winged_t x))
                         (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list 'and (list bird_t x)) (list flies x)))))
                'CxUniverse)
      (v/assert kb (list bird_t Opus) 'CxUniverse)
      (let [neg (v/assert kb (negate (list appendaged_t Opus)) 'CxUniverse)]
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
                'CxUniverse)
      (v/assert kb (list bird_t Opus) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx)))
      (let [neg (v/assert kb (negate (list winged_t Opus)) 'CxUniverse)]
        (is (empty? (v/sentexes-matching kb (list flies Opus) '?ctx))
            "the exception holds on its own predicate")
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb (list flies Opus) '?ctx))
            "and is released when the negation goes")))))
