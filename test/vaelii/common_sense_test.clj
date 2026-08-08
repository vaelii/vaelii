;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.common-sense-test
  "Common sense over the shipped schema and the test-world's cast: the everyday
  inferences a knowledge base is *for*, one per reasoning subsystem, each written the
  way somebody would ask it rather than the way the engine implements it.

  Every test here answers a question with no stored answer.  That is the whole
  selection rule — a test that reads back what a fixture asserted belongs beside the
  subsystem it exercises, and there are a hundred of those elsewhere.  What is left is
  the sweep: taxonomy and the disjointness that bounds it, inheritance down kinds,
  argument types read as entailments, evaluable arithmetic, defaults and their defeat,
  aggregation, negation as failure, abduction under a grant, the equality partition,
  reified functions, skolemized witnesses, measure comparison, mereology, context
  scoping, and how hard each answer was to get.

  The qualitative calculi are the other half, and they need networks rather than a
  cast, so they live in `common-sense-qualitative-test` beside this."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private N 'NaturalWorldContext)
(def ^:private S 'SocialWorldContext)

(defn- refusal
  "The `:type` of the ex-info `assert` throws for `sentence`, or `:stored` when it takes
  it.  Discriminating on the type is the contract; the message is for a reader."
  [kb sentence context]
  (try (v/assert kb sentence context) :stored
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- what a kind is, and what it rules out ------------------------------

(tu/deftest-kb taxonomic-and-relational-inference-compose
  (testing "genl reaches the root for a deeply nested type"
    (is (v/isa? kb 'Tweety 'thing)))                    ; penguin -> ... -> thing
  (testing "transitive / inverse / symmetric relations answer via metadata"
    (is (v/ask? kb '(ancestorOf Tom Ann)))              ; transitive over parentOf
    (is (v/ask? kb '(childOf Ann Bob)))                 ; inverse of parentOf
    (is (v/ask? kb '(siblingOf Carol Ann))))            ; symmetric
  (testing "the mortality default reaches an individual known only by a subtype"
    (is (seq (v/sentexes-matching kb '(mortal Muffet) 'NaturalWorldContext)))))

(tu/deftest-kb one-thing-cannot-be-two-kinds-that-exclude-each-other
  ;; Common sense says a dog is not a cat.  The KB says it twice over: once from a
  ;; stated `(disjoint dog cat)`, and once from the `vertebrateClass` metatype, which
  ;; separates all five classes pairwise and hands the separation down to every
  ;; subtype — so a penguin is not a dog without a word being written about either.
  (testing "the stated pair, and the pair a metatype separates"
    (is (v/disjoint? kb 'dog 'cat))
    (is (v/disjoint? kb 'penguin 'dog)))
  (testing "and the KB refuses the membership rather than storing a contradiction"
    (is (= :disjoint (refusal kb '(cat Muffet) N)))
    (is (= :disjoint (refusal kb '(dog Tweety) N))))
  (testing "what nothing rules out stays open — an open world, not a closed one"
    (is (not (v/disjoint? kb 'dog 'food)))
    (is (not (v/isa? kb 'Muffet 'food)))))

(tu/deftest-kb a-size-claim-about-two-kinds-reaches-the-kinds-beneath-them
  ;; (largerThan mammal insect) is stated; nothing is stated about dogs or ants.  The
  ;; reach is licensed by `argPreserving` on both positions along genl, which is a
  ;; claim about largerThan and not about the world — declared, so it can be wrong,
  ;; rather than assumed, where it could not be.
  (testing "the stated claim, and one nobody stated"
    (is (v/ask? kb '(largerThan mammal insect)))
    (is (v/ask? kb '(largerThan dog ant))))
  (testing "the inherited one is answered and not stored"
    (is (empty? (v/sentexes-matching kb '(largerThan dog ant) '?ctx))))
  (testing "and the relation stays asymmetric under inheritance"
    (is (not (v/ask? kb '(largerThan ant dog))))))

(tu/deftest-kb what-a-kind-has-is-inherited-downward-and-not-upward
  ;; partType preserves its FIRST position along genl and not its second, and the
  ;; asymmetry is the claim: penguins have wings because birds do, while birds having
  ;; wings says nothing about which kinds of wing they have.
  (testing "a kind of bird has whatever parts birds have"
    (is (v/ask? kb '(partType bird wing)))
    (is (v/ask? kb '(partType penguin wing)))
    (is (empty? (v/sentexes-matching kb '(partType penguin wing) '?ctx))))
  (testing "and the second position generalizes to nothing"
    (is (not (v/ask? kb '(partType bird body_part))))))

;; ---- what follows from how a thing is used ------------------------------

(tu/deftest-kb type-inferred-from-how-a-thing-is-used
  ;; Bone1 is never given a type; it is only ever eaten by Muffet. Because
  ;; (argIsa eats 2 food), we can infer Bone1 is food — and, by genl, a
  ;; physical_object and a thing — without ever storing those memberships.
  (testing "the type is not stored, only inferable"
    (is (empty? (v/sentexes-matching kb '(food Bone1) '?ctx))))
  (testing "the individual's type follows from the relation's argIsa"
    (is (v/ask? kb '(food Bone1)))
    (is (v/ask? kb '(physical_object Bone1)))            ; a supertype of food
    (is (not (v/ask? kb '(vehicle Bone1)))))            ; but only what actually follows
  (testing "asking for all of an individual's inferred types"
    (is (= '#{food physical_object thing}
           (set (map #(get % '?t) (v/ask kb '(?t Bone1) '?ctx)))))))

;; ---- arithmetic, and the ordering derived from it ------------------------

(tu/deftest-kb arithmetic-is-computed-not-stored
  (testing "ground numeric comparisons are evaluated by a prover"
    (is (v/ask? kb '(lessThan 1970 1995)))
    (is (not (v/ask? kb '(lessThan 1995 1970))))
    (is (v/ask? kb '(greaterThan 1995 1970)))
    (is (not (v/ask? kb '(greaterThan 1970 1995))))))

(tu/deftest-kb evaluate-computes-symbolic-expressions
  (testing "binds the value of an arithmetic expression"
    (is (= 3  (get (first (v/ask kb '(evaluate ?s (+ 1 2)) '?ctx)) '?s)))
    (is (= 18 (get (first (v/ask kb '(evaluate ?r (* 3 (+ 2 4))) '?ctx)) '?r))))
  (testing "checks a ground result"
    (is (v/ask? kb '(evaluate 7 (+ 3 4))))
    (is (not (v/ask? kb '(evaluate 8 (+ 3 4))))))
  (testing "an unevaluable expression (unbound var / unknown op) yields nothing"
    (is (empty? (v/ask kb '(evaluate ?x (+ ?unbound 1)) '?ctx)))
    (is (empty? (v/ask kb '(evaluate ?x (bogus 1 2)) '?ctx)))))

(tu/deftest-kb age-ordering-derived-by-comparing-birth-years
  ;; olderThan is a backward rule whose third antecedent, (lessThan ?bx ?by), is
  ;; discharged by the arithmetic prover — inference feeding computation.
  (testing "Tom (1970) is older than Bob (1995), not the other way around"
    (is (v/query? kb '(olderThan Tom Bob) '?ctx {:max-depth 2}))
    (is (not (v/query? kb '(olderThan Bob Tom) '?ctx {:max-depth 2}))))
  (testing "people without a recorded birth year are not ordered"
    (is (not (v/query? kb '(olderThan Dave Tom) '?ctx {:max-depth 2})))))

;; ---- defaults, and taking one back --------------------------------------

(tu/deftest-kb a-default-conclusion-feeds-a-further-rule
  ;; flying ⇒ can travel (strict). An eagle flies by default, so it can travel;
  ;; a penguin's flight is defeated, so the downstream conclusion never holds.
  (testing "the eagle inherits can-travel through the flight default"
    (is (v/ask? kb '(flies Sam)))
    (is (seq (v/sentexes-matching kb '(canTravel Sam) 'NaturalWorldContext))))
  (testing "the penguin, defeated on flight, does not get can-travel"
    (is (empty? (v/sentexes-matching kb '(flies Tweety) 'NaturalWorldContext)))
    (is (empty? (v/sentexes-matching kb '(canTravel Tweety) 'NaturalWorldContext)))))

(tu/deftest-kb being-told-an-animal-is-asleep-takes-back-what-was-assumed
  ;; Every animal is awake by default, which is the reading a story assumes without
  ;; saying it.  Told otherwise, the KB does not have to be corrected: the default is
  ;; blocked where it would have fired and its conclusion goes out, the negation is
  ;; derived from the positive claim, and nothing is left in conflict.
  (tu/with-terms [Rex]
    (v/assert kb (list 'dog Rex) N)
    (testing "the default holds of an animal nothing else is known about"
      (is (seq (v/sentexes-matching kb (list 'awake Rex) N))))
    (v/assert kb (list 'asleep Rex) N)
    (testing "and goes out the moment something better is known"
      (is (empty? (v/sentexes-matching kb (list 'awake Rex) N)))
      (is (seq (v/sentexes-matching kb (list 'not (list 'awake Rex)) N))))
    (testing "with no contradiction to report — a defeated default is not a clash"
      (is (empty? (v/conflicts kb))))
    (testing "and the neighbour's default is untouched"
      (is (seq (v/sentexes-matching kb '(awake Muffet) N))))))

(tu/deftest-kb known-true-beats-a-default-and-two-defaults-are-left-standing
  ;; What a KB does when told the opposite of what it assumed depends entirely on how
  ;; hard each side is claimed, and both answers here are the common-sense one.  Told
  ;; something known-true, it drops the assumption and can say which one and why.  Told
  ;; a second defeasible claim, it holds both: neither outranks the other, and picking
  ;; one would be inventing the tie-break nobody supplied.
  (tu/with-terms [Rex]
    (v/assert kb (list 'dog Rex) N)
    (is (seq (v/sentexes-matching kb (list 'mortal Rex) N)))
    (testing "a second defeasible claim is a dilemma the KB represents rather than settles"
      (let [h (v/assert kb (list 'not (list 'mortal Rex)) N)]
        (is (seq (v/sentexes-matching kb (list 'mortal Rex) N)))
        (is (seq (v/sentexes-matching kb (list 'not (list 'mortal Rex)) N)))
        (is (empty? (v/conflicts kb))
            "and not a contradiction to report — nothing known-true is in trouble")
        (v/retract! kb h)))
    (testing "known-true content defeats the default outright"
      (v/assert kb (list 'not (list 'mortal Rex)) N {:strength :monotonic})
      (is (empty? (v/sentexes-matching kb (list 'mortal Rex) N)))
      (is (= :defeated (:reason (v/why-not kb (v/handle-of kb (list 'mortal Rex) N)))))
      (is (empty? (v/conflicts kb))))))

;; ---- counting what is believed ------------------------------------------

(tu/deftest-kb how-many-is-a-question-and-never-a-fact
  ;; A count is a function of what is believed now.  Storing one would put a computed
  ;; value under truth maintenance with nothing to invalidate it, so the aggregates are
  ;; query operators: they answer and leave nothing behind.
  (testing "how many children Bob has"
    (is (= 2 (get (first (v/ask kb '(agg/count ?n ?c (parentOf Bob ?c)) N)) '?n))))
  (testing "how many people there are"
    (is (= 7 (get (first (v/ask kb '(agg/count ?n ?p (person ?p)) N)) '?n))))
  (testing "a count over nothing is zero, where a maximum over nothing is no answer"
    (is (= 0 (get (first (v/ask kb '(agg/count ?n ?p (parentOf ?p Tom)) N)) '?n)))
    (is (empty? (v/ask kb '(agg/max ?m ?y (birthYearOf Dave ?y)) S))))
  (testing "and the answer is nowhere in the store"
    (is (empty? (v/sentexes-with-functor kb 'agg/count)))))

(tu/deftest-kb a-count-follows-belief-rather-than-what-is-stored
  ;; The point of computing it: retract a fact and the count moves, with nothing to
  ;; recompute and nothing that could be stale.
  (tu/with-terms [Pup]
    (is (= 2 (get (first (v/ask kb '(agg/count ?n ?c (parentOf Bob ?c)) N)) '?n)))
    (let [h (v/assert kb (list 'parentOf 'Bob Pup) N)]
      (is (= 3 (get (first (v/ask kb '(agg/count ?n ?c (parentOf Bob ?c)) N)) '?n)))
      (v/retract! kb h))
    (is (= 2 (get (first (v/ask kb '(agg/count ?n ?c (parentOf Bob ?c)) N)) '?n)))))

;; ---- what is not known --------------------------------------------------

(tu/deftest-kb what-is-not-known-is-a-different-claim-from-what-is-false
  ;; Negation as failure is the reading a KB needs for "nobody told me", and it is not
  ;; the reading `not` has: (unknown S) is about the KB, (not S) is about the world.
  (testing "nothing says the cat is asleep, so the question is open"
    (is (v/ask? kb '(unknown (asleep Whiskers))))
    (is (empty? (v/sentexes-matching kb '(not (asleep Whiskers)) '?ctx))))
  (testing "the default that fills the gap is a positive claim, not the absence of one"
    (is (seq (v/sentexes-matching kb '(awake Whiskers) N))))
  (testing "and what IS known does not read as unknown"
    (is (not (v/ask? kb '(unknown (awake Whiskers))))))
  (testing "an existential asks whether anything at all satisfies it"
    (is (v/ask? kb '(thereExists ?c (parentOf Tom ?c))))
    (is (v/ask? kb '(unknown (thereExists ?p (parentOf ?p Tom))))))  ; Tom's parents: nobody's
  (testing "neither is assertible — a query operator is not a fact"
    (is (= :not-well-formed (refusal kb '(unknown (asleep Whiskers)) N)))))

;; ---- guessing, under a grant --------------------------------------------

(tu/deftest-kb an-explanation-is-offered-only-for-what-the-theory-will-assume
  ;; Why would a dog not be awake?  Because it is asleep — the one thing BiologyContext
  ;; grants, and the abducer will hypothesize nothing else.  A grant is a policy of the
  ;; context rather than a capability of the engine, which is what keeps abduction
  ;; from explaining everything and therefore nothing.
  (tu/with-terms [Rex]
    (v/assert kb (list 'dog Rex) N)
    (testing "the goal does not follow from what is known"
      (is (not (v/provable? kb (list 'not (list 'awake Rex)) N))))
    (let [r (v/abduce kb (list 'not (list 'awake Rex)) N)]
      (testing "and one assumption would make it follow"
        (is (= #{(list 'asleep Rex)} (set (map :sentence (:hypotheses r)))))
        (is (seq (:solutions r))))
      (testing "the hypothesis is named as one rather than passing as a proof"
        (is (nil? (v/handle-of kb (list 'asleep Rex) (:context r))))
        (is (not (v/provable? kb (list 'not (list 'awake Rex)) N)))))
    (testing "a dead end nothing grants is reported, not assumed"
      (let [r (v/abduce kb (list 'flies Rex) N)]
        (is (empty? (:hypotheses r)))
        (is (= [(list 'bird Rex)] (:refused r)))))))

;; ---- two names for one thing --------------------------------------------

(tu/deftest-kb two-names-for-one-person-answer-as-one-person
  ;; The everyday case a KB meets constantly: a second spelling arrives for somebody it
  ;; already knows.  The equality partition merges the two, and what was known of the
  ;; one is answered of the other — in both directions, since the partition is a
  ;; partition and not a rewrite rule pointing one way.
  (tu/with-terms [Bobby]
    (v/assert kb (list 'person Bobby) N)
    (testing "before the identity is stated, the two are separate"
      (is (not (v/same-class? kb Bobby 'Bob)))
      (is (not (v/ask? kb (list 'parentOf 'Tom Bobby)))))
    (v/assert kb (list 'sameAs Bobby 'Bob) N)
    (testing "afterwards one class has one representative"
      (is (v/same-class? kb Bobby 'Bob))
      (is (= (v/representative kb Bobby) (v/representative kb 'Bob)))
      (is (contains? (set (v/equiv-class kb 'Bob)) Bobby)))
    (testing "so Tom is this person's parent under either name"
      (is (v/ask? kb (list 'parentOf 'Tom Bobby)))
      (is (v/ask? kb '(parentOf Tom Bob))))))

(tu/deftest-kb one-child-has-one-mother-and-a-second-name-for-her-merges
  ;; motherOf is functional, so a second, different mother is not a second fact.  Two
  ;; symbols are two names — they merge — where two numbers could not be one thing and
  ;; a second birth year is refused outright.
  (tu/with-terms [Pup Dam Mum]
    (v/assert kb (list 'dog Pup) N)
    (v/assert kb (list 'dog Dam) N)
    (v/assert kb (list 'dog Mum) N)
    (v/assert kb (list 'motherOf Pup Dam) N)
    (v/assert kb (list 'motherOf Pup Mum) N)
    (testing "the two mothers are one animal under two names"
      (is (v/same-class? kb Dam Mum)))
    (testing "where two numbers cannot merge, and the second is refused"
      (is (= :functional (refusal kb '(birthYearOf Tom 1971) S))))))

;; ---- naming a thing by the role it plays --------------------------------

(tu/deftest-kb the-mother-of-a-dog-is-the-dog-the-kb-already-knows
  ;; (MotherFn Pup) is a way of naming somebody without knowing their name.  Because
  ;; the function corresponds to motherOf, it resolves to the mother already stored
  ;; rather than minting a second name for her — and the sentence that used it is
  ;; stored about her, so a later question finds it.
  (tu/with-terms [Pup Dam]
    (v/assert kb (list 'dog Pup) N)
    (v/assert kb (list 'dog Dam) N)
    (v/assert kb (list 'motherOf Pup Dam) N)
    (testing "maternity entails parenthood, and the kinship theory reads on from there"
      (is (seq (v/sentexes-matching kb (list 'parentOf Dam Pup) N)))
      (is (v/ask? kb (list 'childOf Pup Dam)))
      (is (v/ask? kb (list 'ancestorOf Dam Pup))))
    (testing "and a sentence about `the mother of Pup` is a sentence about her"
      (v/assert kb (list 'likes 'Ann (list 'MotherFn Pup)) S)
      (is (v/ask? kb (list 'likes 'Ann Dam) S)))))

(tu/deftest-kb a-role-nobody-has-filled-still-answers-questions-about-itself
  ;; Nobody has said who this dog's father is, so the application mints a placeholder
  ;; — and projects it back onto fatherOf, which is what keeps the constant from being
  ;; an opaque thing the KB can say nothing about.
  (tu/with-terms [Stray]
    (v/assert kb (list 'dog Stray) N)
    (is (empty? (v/sentexes-matching kb (list 'fatherOf Stray '?f) '?ctx)))
    (v/assert kb (list 'likes 'Ann (list 'FatherFn Stray)) S)
    (let [[sx] (v/sentexes-matching kb (list 'fatherOf Stray '?f) '?ctx)
          father (nth (:sentence sx) 2)]
      (testing "the placeholder is projected back, so whose father it is, is askable"
        (is (v/reified-term? father))
        (is (= (list 'FatherFn Stray) (v/term-expression kb father))))
      (testing "and it carries the type the function's result is declared to have"
        (is (v/isa? kb father 'animal))))))

;; ---- a witness nobody named ---------------------------------------------

(tu/deftest-kb every-dog-had-a-mother-whether-or-not-anyone-knows-who
  ;; A head existential is the honest form of "there is one, I cannot name them": the
  ;; firing mints a deterministic witness instead of leaving the claim unsaid or
  ;; inventing a name that looks like somebody's.
  (tu/with-terms [Stray]
    (v/assert kb (list 'dog Stray) N)
    (v/assert kb '(implies (and (dog ?x)) (exists ?m (motherOf ?x ?m))) 'WellContext)
    (let [[sx] (v/sentexes-matching kb (list 'motherOf Stray '?m) N)]
      (is (some? sx) "the rule fired over the dog and left a witness")
      (testing "the witness is a minted constant and not a name anybody wrote"
        (is (v/reified-term? (nth (:sentence sx) 2))))
      (testing "and the theory reads on from it exactly as it would from a named mother"
        (is (seq (v/sentexes-matching kb (list 'parentOf (nth (:sentence sx) 2) Stray) N)))))))

;; ---- measures -----------------------------------------------------------

(tu/deftest-kb a-kilogram-outweighs-nine-hundred-and-ninety-nine-grams
  ;; The units ship, so this is answerable without a caller stating a table first.
  ;; The comparison is computed from the two magnitudes once both are normalized, and
  ;; a comparison across dimensions is not false but not comparable.
  (testing "the same dimension, written in two units"
    (is (v/ask? kb '(quantityGreaterThan (QuantityFn 1 Kilogram) (QuantityFn 999 Gram))))
    (is (v/ask? kb '(sameQuantity (QuantityFn 1 Hour) (QuantityFn 60 Minute))))
    (is (v/ask? kb '(quantityLessThan (QuantityFn 1 Centimeter) (QuantityFn 1 Meter)))))
  (testing "and a mass against a length answers nothing at all"
    (is (not (v/ask? kb '(quantityGreaterThan (QuantityFn 1 Kilogram) (QuantityFn 1 Meter)))))
    (is (not (v/ask? kb '(quantityLessThan (QuantityFn 1 Kilogram) (QuantityFn 1 Meter)))))))

(tu/deftest-kb which-of-two-animals-is-heavier-is-read-off-their-weights
  ;; Nobody states heavierThan.  It is a backward rule over two weightOf measures, so
  ;; it holds exactly while both weights do — the same shape olderThan has over two
  ;; birth years, one dimension up.
  (v/assert kb '(weightOf Muffet (QuantityFn 20 Kilogram)) N)
  (v/assert kb '(weightOf Whiskers (QuantityFn 4500 Gram)) N)
  (testing "the dog outweighs the cat, in units nobody bothered to match"
    (is (v/query? kb '(heavierThan Muffet Whiskers) N {:max-depth 2}))
    (is (not (v/query? kb '(heavierThan Whiskers Muffet) N {:max-depth 2}))))
  (testing "an animal with no weight on record is not ordered against anything"
    (is (not (v/query? kb '(heavierThan Muffet Sam) N {:max-depth 2}))))
  (testing "and a second, different weight is a contradiction rather than a second fact"
    (is (= :functional (refusal kb '(weightOf Muffet (QuantityFn 30 Kilogram)) N)))))

;; ---- where a thing is ---------------------------------------------------

(tu/deftest-kb a-part-is-wherever-its-whole-is
  ;; Two theories meeting: mereology carries location down parthood, and locatedIn is
  ;; transitive, so the piston is in the house through four facts and neither of them
  ;; is about pistons or houses.
  (testing "the rule fires down one level and stores what it concluded"
    (is (seq (v/sentexes-matching kb '(locatedIn Engine1 Garage1) N))))
  (testing "and the chain answers further than anything stored reaches"
    (is (v/ask? kb '(locatedIn Piston1 House1)))
    (is (not (v/ask? kb '(locatedIn House1 Piston1)))))
  (testing "owning a whole is owning its parts"
    (is (seq (v/sentexes-matching kb '(owns Tom Roof1) S)))))

;; ---- which theory is asking ---------------------------------------------

(tu/deftest-kb an-answer-is-an-answer-from-somewhere
  ;; The cast's social facts and its natural-world facts sit in sibling contexts, so a
  ;; rule joining one of each has nowhere to put its conclusion and does not fire.
  ;; That is the containment a contextualized KB buys: a theory reasons with what it
  ;; can see, and two theories do not silently pool their facts.
  (testing "each fact is visible where it was written"
    (is (seq (v/sentexes-matching kb '(owns Tom Car1) S)))
    (is (empty? (v/sentexes-matching kb '(owns Tom Car1) N))))
  (testing "so the ownership rule reaches the parts written beside it"
    (is (seq (v/sentexes-matching kb '(owns Tom Chimney1) S))))
  (testing "and not the parts written in the sibling theory"
    (is (seq (v/sentexes-matching kb '(partOf Engine1 Car1) N)))
    (is (empty? (v/sentexes-matching kb '(owns Tom Engine1) '?ctx))))
  (testing "a context sees up its own cone and no further"
    (is (v/sees? kb N 'BiologyContext))
    (is (not (v/sees? kb N S)))))

;; ---- how hard the answer was --------------------------------------------

(tu/deftest-kb the-cheapest-level-that-answers-is-the-one-that-answers
  ;; The same question costs wildly different amounts depending on where the answer
  ;; already is, and the stack says which — a stored fact is a lookup, a defeasible
  ;; conclusion is a lookup because forward chaining already ran, and an ordering
  ;; nobody stored is a proof.
  (testing "a stored membership, and a default that already fired, are both reads"
    (is (= 2 (:level (v/escalate kb '(dog Muffet) N))))
    (is (= 2 (:level (v/escalate kb '(mortal Muffet) N)))))
  (testing "an ordering derived on demand is a backward proof"
    (is (= 7 (:level (v/escalate kb '(olderThan Tom Bob) S)))))
  (testing "and every level agrees about what is true, whatever it costs"
    (is (v/ask? kb '(mortal Muffet)))
    (is (v/provable? kb '(mortal Muffet) N))))
