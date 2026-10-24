;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-test
  "Argument-position preservation: `(transitiveInArg P n R)` /
  `(transitiveInArgInverse P n R)`, the specificity that lets a stated claim override an
  inherited one, and the `(asymmetric P)` conflict that a strict claim raises instead.

  The running example: `(typeLargerThan dog cat)` reaches a golden retriever and a maine
  coon, and also a chihuahua and a maine coon, where it is false (docs/inherit.md,
  \"Strict versus typical, from the strength that was already there\")."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- kinds!
  "dog ⊃ {golden_retriever chihuahua}, cat ⊃ {maine_coon siamese}, the edges asserted
  with `opts`."
  ([kb terms] (kinds! kb terms {}))
  ([kb {:keys [dog cat gr chi mc sia]} opts]
   (v/with-deferred-settle kb
     (doseq [[sub sup] [[gr dog] [chi dog] [mc cat] [sia cat]]]
       (v/assert kb (list 'genl sub sup) 'CxUniverse opts)))))

(defn- preserving!
  ([kb pred] (preserving! kb pred {}))
  ([kb pred opts]
   (v/with-deferred-settle kb
     (v/assert kb (list 'asymmetric pred) 'CxUniverse opts)
     (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse opts)
     (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse opts))))

;; ---- the inheritance itself ----------------------------------------------

(tu/deftest-kb a-claim-about-two-kinds-reaches-their-subkinds
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t typeLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typeLargerThan)
    (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
    (testing "both positions inherit, together and singly"
      (is (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) 'CxUniverse))
      (is (v/ask? kb (list typeLargerThan golden_retriever_t cat_t) 'CxUniverse))
      (is (v/ask? kb (list typeLargerThan dog_t maine_coon_t) 'CxUniverse))
      (is (v/ask? kb (list typeLargerThan dog_t cat_t) 'CxUniverse)))
    (testing "and it does not run backwards, or sideways to an unrelated kind"
      (is (not (v/ask? kb (list typeLargerThan maine_coon_t golden_retriever_t) 'CxUniverse)))
      (is (not (v/ask? kb (list typeLargerThan cat_t dog_t) 'CxUniverse))))))

(tu/deftest-kb no-declaration-means-no-inheritance
  ;; The default for every predicate: a claim about two kinds says nothing about their
  ;; subkinds until someone says it does.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t typeLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
    (is (v/ask? kb (list typeLargerThan dog_t cat_t) 'CxUniverse))
    (is (not (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) 'CxUniverse)))
    (is (nil? (inherit/verdict kb (list typeLargerThan golden_retriever_t maine_coon_t)
                               'CxUniverse)))))

(tu/deftest-kb one-position-can-be-preserved-without-the-other
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t chases]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list 'transitiveInArgInverse chases 1 'genl) 'CxUniverse)
    (v/assert kb (list chases dog_t cat_t) 'CxUniverse)
    (is (v/ask? kb (list chases golden_retriever_t cat_t) 'CxUniverse))
    (is (not (v/ask? kb (list chases dog_t maine_coon_t) 'CxUniverse))
        "position 2 was not declared, so it stays fixed")))

;; ---- the relation is a parameter -----------------------------------------

(tu/deftest-kb the-preserved-relation-need-not-be-genl
  ;; `(transitiveInArg P n R)` names R.  Here it is an ordinary declared-transitive
  ;; predicate over individuals, with no types in sight.
  (tu/with-terms [tangiblePartOf needs_maintenance Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Piston Engine) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needs_maintenance 1 tangiblePartOf) 'CxUniverse)
      (v/assert kb (list needs_maintenance Car) 'CxUniverse))
    (testing "one hop and two, through the transitive relation that was named"
      (is (v/ask? kb (list needs_maintenance Engine) 'CxUniverse))
      (is (v/ask? kb (list needs_maintenance Piston) 'CxUniverse)))
    (testing "and not upward"
      (is (not (v/ask? kb (list needs_maintenance 'TmpUnrelatedThing) 'CxUniverse))))))

(tu/deftest-kb transitiveInArg-reads-the-relation-along-its-arrow
  ;; So neither direction needs an inverse predicate declared for its own sake.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  hasMemberSomewhere Earth]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list 'transitiveInArg hasMemberSomewhere 1 'genl) 'CxUniverse)
    (v/assert kb (list hasMemberSomewhere chihuahua_t Earth) 'CxUniverse)
    (is (v/ask? kb (list hasMemberSomewhere dog_t Earth) 'CxUniverse)
        "upward: a subkind's claim reaches the kind")
    (is (not (v/ask? kb (list hasMemberSomewhere siamese_t Earth) 'CxUniverse))
        "but not back down to a sibling")))

(tu/deftest-kb transitiveInArg-carries-a-claim-up-genl-and-the-inverse-carries-it-down
  ;; The direction each name carries, checked against Cyc's `transitiveViaArg`:
  ;; `(transitiveInArg P n R)` moves a claim along R's arrow, so a stored `(P W)` with
  ;; `(genl W S)` gives `(P S)` — up to a supertype — and `transitiveInArgInverse` moves
  ;; it against the arrow, down to a subtype.  Neither name reaches the other way.
  (tu/with-terms [animal_t dog_t poodle_t carriedUp carriedDown]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse)
      (v/assert kb (list 'genl poodle_t dog_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg carriedUp 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse carriedDown 1 'genl) 'CxUniverse)
      (v/assert kb (list carriedUp dog_t) 'CxUniverse)
      (v/assert kb (list carriedDown dog_t) 'CxUniverse))
    (testing "transitiveInArg: up to the supertype, and not down to the subtype"
      (is (v/ask? kb (list carriedUp animal_t) 'CxUniverse))
      (is (not (v/ask? kb (list carriedUp poodle_t) 'CxUniverse))))
    (testing "transitiveInArgInverse: down to the subtype, and not up to the supertype"
      (is (v/ask? kb (list carriedDown poodle_t) 'CxUniverse))
      (is (not (v/ask? kb (list carriedDown animal_t) 'CxUniverse))))))

(tu/deftest-kb the-preserved-relation-can-be-the-context-hierarchy
  ;; The other closure the engine owns: an argument that names a *context* can be
  ;; preserved along `genlCx`, so a claim about a wide context reaches the
  ;; contexts below it — and `transitiveInArg` reads the lattice upward.  No
  ;; `(transitive genlCx)` declaration exists or is needed: the walk reads the
  ;; cached context closure, exactly as `genl` reads the type closure.
  (tu/with-terms [appliesIn reportedBelow TheDecree CxWide CxMid CxNarrow
                  CxSide]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxWide 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxMid CxWide) 'CxUniverse)
      (v/assert kb (list 'genlCx CxNarrow CxMid) 'CxUniverse)
      (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse appliesIn 2 'genlCx) 'CxUniverse)
      (v/assert kb (list appliesIn TheDecree CxWide) 'CxUniverse))
    (testing "one hop and two, down the cached context closure"
      (is (v/ask? kb (list appliesIn TheDecree CxMid) 'CxUniverse))
      (is (v/ask? kb (list appliesIn TheDecree CxNarrow) 'CxUniverse)))
    (testing "and not upward, or sideways to an incomparable context"
      (is (not (v/ask? kb (list appliesIn TheDecree 'CxUniverse) 'CxUniverse)))
      (is (not (v/ask? kb (list appliesIn TheDecree CxSide) 'CxUniverse))))
    (testing "transitiveInArg reads the lattice upward"
      (v/with-deferred-settle kb
        (v/assert kb (list 'transitiveInArg reportedBelow 2 'genlCx)
                  'CxUniverse)
        (v/assert kb (list reportedBelow TheDecree CxNarrow) 'CxUniverse))
      (is (v/ask? kb (list reportedBelow TheDecree CxMid) 'CxUniverse) "one hop")
      (is (v/ask? kb (list reportedBelow TheDecree CxWide) 'CxUniverse) "two")
      (is (not (v/ask? kb (list reportedBelow TheDecree CxSide) 'CxUniverse))
          "and not to a context with nothing below it"))
    (testing "a late edge extends the reach, and retracting it takes the reach back"
      (v/assert kb (list 'genlCx CxSide CxMid) 'CxUniverse)
      (is (v/ask? kb (list appliesIn TheDecree CxSide) 'CxUniverse)
          "the incomparable context is now below the wide one, and the claim arrives")
      (v/retract! kb (v/handle-of kb (list 'genlCx CxSide CxMid)
                                  'CxUniverse))
      (is (not (v/ask? kb (list appliesIn TheDecree CxSide) 'CxUniverse))))))

(tu/deftest-kb transitiveInArg-walks-a-declared-relation-too
  ;; The direction and the relation are independent axes: `transitiveInArg` along
  ;; a declared-transitive predicate reads its stored facts along their arrow, so a claim about
  ;; a part reaches the assemblies it sits in.
  (tu/with-terms [tangiblePartOf dirty Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Piston Engine) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg dirty 1 tangiblePartOf) 'CxUniverse)
      (v/assert kb (list dirty Piston) 'CxUniverse))
    (is (v/ask? kb (list dirty Engine) 'CxUniverse) "one hop up the part chain")
    (is (v/ask? kb (list dirty Car) 'CxUniverse) "and two")
    (is (not (v/ask? kb (list dirty 'TmpOtherThing) 'CxUniverse))
        "a thing on no chain inherits nothing")))

;; ---- the semantics travel with the relation --------------------------------
;; Undercutting, strength and negation are stated over `genl` in the sections below,
;; and the code that decides them is relation-generic — `below?` compares tuples along
;; whatever relation the declaration names.  These assert that the semantics hold off
;; `genl` too, so a regression scoped to the non-genl arms cannot pass the suite.

(tu/deftest-kb a-specific-claim-undercuts-along-the-relation-it-travelled
  (testing "along the context lattice"
    (tu/with-terms [appliesIn TheDecree CxWide CxMid CxNarrow CxSide]
      (v/with-deferred-settle kb
        (v/assert kb (list 'genlCx CxWide 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxMid CxWide) 'CxUniverse)
        (v/assert kb (list 'genlCx CxNarrow CxMid) 'CxUniverse)
        (v/assert kb (list 'genlCx CxSide CxWide) 'CxUniverse)
        (v/assert kb (list 'transitiveInArgInverse appliesIn 2 'genlCx) 'CxUniverse)
        (v/assert kb (list appliesIn TheDecree CxWide) 'CxUniverse))
      (is (v/ask? kb (list appliesIn TheDecree CxNarrow) 'CxUniverse))
      (v/assert kb (list 'not (list appliesIn TheDecree CxMid)) 'CxUniverse)
      (is (not (v/ask? kb (list appliesIn TheDecree CxNarrow) 'CxUniverse))
          "below the denial the nearer claim decides")
      (is (v/ask? kb (list appliesIn TheDecree CxSide) 'CxUniverse)
          "a branch the denial says nothing about still inherits")))
  (testing "along a declared fact-relation"
    (tu/with-terms [tangiblePartOf needs_maintenance Car Engine Piston Wheel]
      (v/with-deferred-settle kb
        (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
        (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
        (v/assert kb (list tangiblePartOf Piston Engine) 'CxUniverse)
        (v/assert kb (list tangiblePartOf Wheel Car) 'CxUniverse)
        (v/assert kb (list 'transitiveInArgInverse needs_maintenance 1 tangiblePartOf) 'CxUniverse)
        (v/assert kb (list needs_maintenance Car) 'CxUniverse))
      (is (v/ask? kb (list needs_maintenance Piston) 'CxUniverse))
      (v/assert kb (list 'not (list needs_maintenance Engine)) 'CxUniverse)
      (is (not (v/ask? kb (list needs_maintenance Piston) 'CxUniverse))
          "the denial at the engine stops what only the engine's chain carried")
      (is (v/ask? kb (list needs_maintenance Wheel) 'CxUniverse)
          "the wheel's chain does not pass the engine"))))

(tu/deftest-kb specificity-under-transitiveInArg-follows-the-travel-direction
  ;; The upward walk reads the relation along its arrow, and `below?` reads the
  ;; declaration's direction with it: nearer to the goal along the travelled direction
  ;; is more specific, so under `transitiveInArg … genl` the *supertype*'s claim
  ;; is the one that decides — it sits closer to the upward goal than the subtype's.
  (tu/with-terms [dog_t animal_t thing_t hasMemberSomewhere]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse)
      (v/assert kb (list 'genl animal_t thing_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg hasMemberSomewhere 1 'genl) 'CxUniverse)
      (v/assert kb (list hasMemberSomewhere dog_t) 'CxUniverse))
    (is (v/ask? kb (list hasMemberSomewhere thing_t) 'CxUniverse) "the chain reaches up")
    (v/assert kb (list 'not (list hasMemberSomewhere animal_t)) 'CxUniverse)
    (is (= :against (inherit/verdict kb (list hasMemberSomewhere animal_t) 'CxUniverse))
        "at the denial's own tuple the stated claim wins over the inherited one")
    (is (not (v/ask? kb (list hasMemberSomewhere thing_t) 'CxUniverse))
        "and above it, the claim nearer the goal along the travelled direction decides")))

(tu/deftest-kb known-true-content-does-not-yield-off-genl
  ;; "A :monotonic claim is never undercut" is stated of the strength, not of the
  ;; relation: along a fact-relation the contrary specific claim leaves a dilemma
  ;; standing rather than silently overriding the fixed background.
  (tu/with-terms [tangiblePartOf needs_maintenance Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Piston Engine) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needs_maintenance 1 tangiblePartOf) 'CxUniverse))
    (v/assert kb (list needs_maintenance Car) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list needs_maintenance Engine)) 'CxUniverse)
    (is (= :ambiguous (inherit/verdict kb (list needs_maintenance Piston) 'CxUniverse))
        "the monotonic general claim does not yield, so the disagreement is represented")
    (is (not (v/ask? kb (list needs_maintenance Piston) 'CxUniverse))
        "and the prover answers neither way")))

(tu/deftest-kb a-negation-blocks-the-walk-whatever-relation-it-travels
  ;; The negation probe is relation-generic: a believed `(not (P …))` at a tuple in
  ;; range argues `:against` along `genlCx` and a fact-relation exactly as along
  ;; `genl` — and the negated *goal* stays unanswered either way, because an
  ;; inheritance that only licenses claims has nothing to say about refutation.
  (tu/with-terms [appliesIn TheDecree CxWide CxNarrow]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxWide 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxNarrow CxWide) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse appliesIn 2 'genlCx) 'CxUniverse)
      (v/assert kb (list appliesIn TheDecree CxWide) 'CxUniverse)
      (v/assert kb (list 'not (list appliesIn TheDecree CxWide)) 'CxUniverse))
    (is (= :ambiguous (inherit/verdict kb (list appliesIn TheDecree CxNarrow)
                                       'CxUniverse))
        "a claim and its negation at one tuple are not a clean for, down the lattice either")
    (is (not (v/ask? kb (list appliesIn TheDecree CxNarrow) 'CxUniverse)))
    (is (not (v/ask? kb (list 'not (list appliesIn TheDecree CxNarrow))
                     'CxUniverse))
        "the negated goal is not answered by preservation: :against is open-world")))

(tu/deftest-kb the-mirror-and-the-hop-compose-under-transitiveInArg
  ;; A claim reachable only through the symmetric mirror *and* an argument hop along
  ;; the relation's arrow: stored `(adjacentTo Garden Piston)`, mirrored to put the piston at the
  ;; preserved position, then walked up the part chain.
  (tu/with-terms [tangiblePartOf adjacentTo Garden Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Piston Engine) 'CxUniverse)
      (v/assert kb (list 'symmetric adjacentTo) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg adjacentTo 1 tangiblePartOf) 'CxUniverse))
    (v/assert kb (list adjacentTo Garden Piston) 'CxUniverse)
    (is (v/ask? kb (list adjacentTo Engine Garden) 'CxUniverse) "one hop, mirrored")
    (is (v/ask? kb (list adjacentTo Car Garden) 'CxUniverse) "and two")
    (is (v/ask? kb (list adjacentTo Garden Car) 'CxUniverse)
        "and the inherited claim has a mirror of its own")
    (is (not (v/ask? kb (list adjacentTo Garden 'TmpElsewhere) 'CxUniverse)))))

(tu/deftest-kb a-position-past-the-arity-preserves-nothing
  ;; `wff` checks the position is a positive integer and not that the predicate has
  ;; it; `by-position` drops what no tuple can satisfy, so the declaration is stored,
  ;; inert, and licenses nothing — asserted so a regression that reads past a tuple's
  ;; end, or takes the declaration's existence for a licence, is caught here.
  (tu/with-terms [dog_t cat_t golden_retriever_t chases]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl golden_retriever_t dog_t) 'CxUniverse)
      (v/assert kb (list 'binary_predicate chases) 'CxUniverse))
    (is (integer? (v/assert kb (list 'transitiveInArgInverse chases 3 'genl) 'CxUniverse))
        "admitted: the structural check does not read the arity")
    (v/assert kb (list chases dog_t cat_t) 'CxUniverse)
    (is (not (v/ask? kb (list chases golden_retriever_t cat_t) 'CxUniverse))
        "no position it names exists, so nothing inherits")
    (is (nil? (inherit/verdict kb (list chases golden_retriever_t cat_t) 'CxUniverse)))
    (is (v/ask? kb (list chases dog_t cat_t) 'CxUniverse)
        "the stored fact still answers, by the ordinary matcher")))

(tu/deftest-kb an-open-goal-returns-the-stored-tuples-and-only-those
  ;; docs/inherit.md's ground-only contract, asserted: `TransitiveInArgProver` answers a
  ;; ground goal, and an open one is left to the fact and rule provers — so a query
  ;; enumerates the stored extent while `ask?` answers each licensed tuple.  A future
  ;; enumerator changes this test deliberately or not at all.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl golden_retriever_t dog_t) 'CxUniverse)
      (v/assert kb (list 'genl maine_coon_t cat_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
      (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse))
    (is (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) 'CxUniverse)
        "each licensed ground tuple answers")
    (is (= [{'?x dog_t '?y cat_t}]
           (vec (v/ask kb (list typeLargerThan '?x '?y) 'CxUniverse)))
        "the open goal enumerates the stored extent and no licensed tuple")
    (is (empty? (v/ask kb (list typeLargerThan '?x maine_coon_t) 'CxUniverse))
        "a half-open goal bound off the stored extent enumerates nothing")))

(tu/deftest-kb the-licence-stays-with-the-predicate-it-names
  ;; docs/inherit.md, opening section: facts travel up the predicate hierarchy, and
  ;; licences do not travel down it.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typeLargerThan muchLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typeLargerThan)
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl muchLargerThan typeLargerThan) 'CxUniverse)
      (v/assert kb (list muchLargerThan dog_t cat_t) 'CxUniverse))
    (is (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) 'CxUniverse)
        "the super-predicate's goal inherits, reading the sub-predicate's fact")
    (is (not (v/ask? kb (list muchLargerThan golden_retriever_t maine_coon_t)
                     'CxUniverse))
        "the sub-predicate's goal does not: nobody declared muchLargerThan preserving")))

(tu/deftest-kb a-relation-nobody-declared-transitive-is-refused
  ;; Both spellings of the declaration reach the same refusal.
  (tu/with-terms [cursed begat sired A B D]
    (doseq [[what rel] [["untyped" begat] ["typed" sired]]]
      (when (= "typed" what)
        (v/assert kb (list 'binary_predicate sired) 'CxUniverse))
      (let [e (try (v/assert kb (list 'transitiveInArgInverse cursed 1 rel) 'CxUniverse)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) (str what " relation: the declaration is refused"))
        (is (= :not-well-formed (:type (ex-data e))) what)))
    (testing "nothing was stored, so no closure is walked"
      (v/with-deferred-settle kb
        (v/assert kb (list begat A B) 'CxUniverse)
        (v/assert kb (list begat B D) 'CxUniverse)
        (v/assert kb (list cursed D) 'CxUniverse))
      (is (not (v/ask? kb (list cursed A) 'CxUniverse)))
      (is (not (v/ask? kb (list cursed B) 'CxUniverse))))
    (testing "declaring the transitivity first admits it, and then it walks"
      (v/assert kb (list 'transitive begat) 'CxUniverse)
      (is (integer? (v/assert kb (list 'transitiveInArgInverse cursed 1 begat) 'CxUniverse)))
      (is (v/ask? kb (list cursed B) 'CxUniverse) "one hop")
      (is (v/ask? kb (list cursed A) 'CxUniverse) "two"))))

(tu/deftest-kb the-declaration-is-about-a-relation-however-that-relation-is-written
  ;; The inheriting relation is held to what `arg`'s first argument is held to, and
  ;; for the same reasons: a function is spelled like an individual, and a relation can
  ;; be *denoted* by a NAT rather than named.  A `nm/individual?` test gets this exactly
  ;; backwards — a compound is not an individual, so it refuses the conventional
  ;; CapitalCamelCase spelling and waves the exotic one through.
  (tu/with-terms [Milli inheritsAlong chases]
    (v/assert kb (list 'transitive inheritsAlong) 'CxUniverse)
    (testing "a CapitalCamelCase relation — a function name — is admitted, as arg's is"
      (is (integer? (v/assert kb (list 'arg Milli 1 'thing) 'CxUniverse)))
      (is (integer? (v/assert kb (list 'transitiveInArgInverse Milli 1 inheritsAlong)
                              'CxUniverse))))
    (testing "and so is a relation a NAT denotes"
      (is (integer? (v/assert kb (list 'transitiveInArgInverse (list Milli 'thing) 1 inheritsAlong)
                              'CxUniverse))))
    (testing "but the relation preserved *along* stays a symbol: the reach walk builds
              (R x ?v) from it, and there is no transitivity to read off a compound"
      (let [e (try (v/assert kb (list 'transitiveInArgInverse chases 1 (list Milli 'thing))
                             'CxUniverse)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e))
        (is (= :not-well-formed (:type (ex-data e))))))))

(tu/deftest-kb a-self-tuple-is-not-a-claim-against-itself
  ;; At `[a a]` the converse of `(P a b)` *is* `(P a b)`, so reading it as opposition
  ;; would file one sentex on both sides and report a dilemma the KB does not hold —
  ;; `contradictions` says nothing about it, and neither should this.
  (tu/with-terms [outranks Ann]
    (v/with-deferred-settle kb
      (v/assert kb (list 'asymmetric outranks) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse outranks 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse outranks 2 'genl) 'CxUniverse)
      (v/assert kb (list outranks Ann Ann) 'CxUniverse))
    (is (empty? (v/contradictions kb)) "the KB reports no clash here")
    (is (= :for (inherit/verdict kb (list outranks Ann Ann) 'CxUniverse))
        "so the one believed claim is what bears on it")
    (testing "a converse at a tuple of two different terms still denies"
      (tu/with-terms [Bob]
        (v/assert kb (list outranks Bob Ann) 'CxUniverse)
        (is (= :against (inherit/verdict kb (list outranks Ann Bob) 'CxUniverse))
            "nothing states (outranks Ann Bob), and its mirror is believed")
        (testing "and once both directions are believed, that is the dilemma"
          (v/assert kb (list outranks Ann Bob) 'CxUniverse)
          (is (= :ambiguous (inherit/verdict kb (list outranks Ann Bob)
                                             'CxUniverse))))))))

(tu/deftest-kb the-transitivity-licence-is-read-from-the-asking-context
  ;; The pair lives here rather than in `context_scoping_test` because it cannot be
  ;; built on a KB carrying the upper layer: `transitive` is a `decontextualized_predicate`
  ;; there, so every declaration is lifted into CxUniverse and every context sees
  ;; it (that is the *control*, and it is stated over there).  This KB has no such
  ;; declaration, so nothing lifts and the scoped read is observable.
  (tu/with-terms [cursed3 begat3 A3 B3 CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'transitive begat3) CxA)
    (is (integer? (v/assert kb (list 'transitiveInArgInverse cursed3 1 begat3) CxB))
        "admitted: the structural check asks whether the relation is transitive at all,
         and leaves what this writer may do with it to the read")
    (v/assert kb (list begat3 A3 B3) CxB)
    (v/assert kb (list cursed3 B3) CxB)
    (is (not (v/ask? kb (list cursed3 A3) CxB))
        "B holds the claim and the edge, and no licence to walk the relation")
    (testing "and the same declaration walks once the licence is where B can see it"
      (v/assert kb (list 'transitive begat3) 'CxUniverse)
      (is (v/ask? kb (list cursed3 A3) CxB)))))

(tu/deftest-kb a-permuting-mark-is-read-from-every-context-on-this-kb-too
  ;; The exception to the pair above.  `(symmetric R)` and the three commutativity marks
  ;; decide the argument order a sentex is stored in, and a sentex has one key for every
  ;; context, so the store answers the mirror of a fact from a context that cannot see the
  ;; mark.  The engine lifts each statement of one into CxUniverse whatever the KB
  ;; declares (`special/deduce-lifts`), so every other reader answers as the store does —
  ;; here, with no `decontextualized_predicate` anywhere, as on a KB carrying the upper layer.
  (doseq [[kind mark] [[:symmetric #(list 'symmetric %)]
                       [:commutative #(list 'commutative %)]
                       [nil #(list 'commutativeInArgs % 1 2)]
                       [nil #(list 'commutativeInArgAndRest % 1)]]]
    (tu/with-terms [bondedTo Ann Bob CxA CxB]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'arity bondedTo 2) 'CxUniverse)
      (v/assert kb (mark bondedTo) CxA)
      (v/assert kb (list bondedTo Ann Bob) 'CxUniverse)
      (doseq [reader ['CxUniverse CxA CxB]]
        (testing (str (first (mark bondedTo)) " read from " reader)
          (is (v/ask? kb (list bondedTo Bob Ann) reader) "the store answers the mirror")
          (is (v/ask? kb (mark bondedTo) reader) "and the mark it answers it through holds")
          (when kind
            (is (v/has-prop? kb kind bondedTo reader) "and so is the property")))))))

(tu/deftest-kb a-permuting-mark-is-read-from-a-context-with-no-edge
  ;; CxI is named by no `genlCx` edge, so it sees no statement of a mark stated in CxA,
  ;; nor the copy in CxUniverse.  The store sorts CxI's fact under the mark all the same,
  ;; so `has-prop?` reads the property from CxI as the store does, while the mark asked as
  ;; a sentence is answered where a statement is visible, as any sentence is.  A mark
  ;; stated in CxI is lifted, so CxUniverse and both siblings read it.  Each in either order.
  (doseq [[kind mark] [[:symmetric #(list 'symmetric %)]
                       [:commutative #(list 'commutative %)]
                       [nil #(list 'commutativeInArgs % 1 2)]
                       [nil #(list 'commutativeInArgAndRest % 1)]]
          mark-in-ci? [false true]
          mark-first? [true false]]
    (tu/with-terms [bondedTo Ann Bob CxA CxB CxI]
      (let [[mark-cx fact-cx readers] (if mark-in-ci?
                                        [CxI 'CxUniverse ['CxUniverse CxA CxB]]
                                        [CxA CxI [CxI]])]
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'arity bondedTo 2) 'CxUniverse)
        (when mark-first? (v/assert kb (mark bondedTo) mark-cx))
        (v/assert kb (list bondedTo Ann Bob) fact-cx)
        (when-not mark-first? (v/assert kb (mark bondedTo) mark-cx))
        (doseq [reader readers]
          (testing (str (first (mark bondedTo)) " stated in " mark-cx ", read from " reader
                        (if mark-first? ", mark first" ", mark last"))
            (is (v/ask? kb (list bondedTo Bob Ann) reader) "the store answers the mirror")
            (is (= (not= CxI reader) (v/ask? kb (mark bondedTo) reader))
                "the statement answers where it is visible")
            (when kind
              (is (v/has-prop? kb kind bondedTo reader) "and the property holds"))))))))

(tu/deftest-kb all-three-transitivities-compose-in-one-goal
  ;; Subsumption, preservation and visibility meet in one read: the claim is stored
  ;; under a *sub-predicate* of the goal's, about the *supertypes* of the goal's
  ;; arguments, and the licence and the predicate edge sit at different depths of the
  ;; asking context's ancestor set.  Each pairing is asserted on its own — here and in
  ;; `predicate_subsumption_test` — and this is the intersection, where the fact reach
  ;; has to fan to the sub-predicate *as seen from the asking context* for a tuple the
  ;; argument walk proposed.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t typeLargerThan muchLargerThan
                  CxTop CxAsk]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxTop 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxAsk CxTop) 'CxUniverse)
      ;; the kinds and the claim, where every context sees them
      (v/assert kb (list 'genl golden_retriever_t dog_t) 'CxUniverse)
      (v/assert kb (list 'genl maine_coon_t cat_t) 'CxUniverse)
      (v/assert kb (list muchLargerThan dog_t cat_t) 'CxUniverse)
      ;; the licence partway up the ancestor set, the predicate edge at its bottom
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) CxTop)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) CxTop)
      (v/assert kb (list 'genl muchLargerThan typeLargerThan) CxAsk))
    (testing "where every piece is visible, the goal needing all three answers"
      (is (v/ask? kb (list typeLargerThan dog_t cat_t) CxAsk)
          "subsumption alone: the kinds-level goal under the super-predicate")
      (is (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) CxAsk)
          "subsumption and preservation together: the subkinds under the super-predicate"))
    (testing "one level up, exactly the predicate edge is out of sight"
      (is (v/ask? kb (list muchLargerThan dog_t cat_t) CxTop)
          "the stored claim itself is visible")
      (is (not (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) CxTop))
          "but no visible edge puts it under the goal's predicate"))
    (testing "at the root the licence is out of sight too, and nothing walks"
      (is (not (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t)
                       'CxUniverse))))))

(tu/deftest-kb withdrawing-the-transitivity-withdraws-the-inheritance
  ;; Read at use and not only at assert: the declaration is still stored, but a relation
  ;; nobody currently says composes is one whose reach we have no right to close.
  (tu/with-terms [cursed begat A B D]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive begat) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse cursed 1 begat) 'CxUniverse)
      (v/assert kb (list begat A B) 'CxUniverse)
      (v/assert kb (list begat B D) 'CxUniverse)
      (v/assert kb (list cursed D) 'CxUniverse))
    (is (v/ask? kb (list cursed A) 'CxUniverse))
    (v/retract! kb (v/handle-of kb (list 'transitive begat) 'CxUniverse))
    (is (not (v/ask? kb (list cursed A) 'CxUniverse)))
    (is (nil? (inherit/verdict kb (list cursed A) 'CxUniverse))
        "the position is not walked at all, so the predicate inherits nothing")
    (is (v/ask? kb (list cursed D) 'CxUniverse) "the stated claim is untouched")))

;; ---- the scope: kinds, and not their members -----------------------------

(tu/deftest-kb preservation-along-genl-stays-at-the-level-of-kinds
  ;; docs/inherit.md, "Preservation stays on one side of the type/instance line"
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typeLargerThan Rex Whiskers]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/with-deferred-settle kb
      (v/assert kb (list golden_retriever_t Rex) 'CxUniverse)
      (v/assert kb (list maine_coon_t Whiskers) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
      (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse))
    (is (v/ask? kb (list typeLargerThan golden_retriever_t maine_coon_t) 'CxUniverse)
        "the subkinds")
    (is (not (v/ask? kb (list typeLargerThan Rex Whiskers) 'CxUniverse))
        "and not their members")
    (is (nil? (inherit/verdict kb (list typeLargerThan Rex Whiskers) 'CxUniverse))
        "nothing bears on the pair at all — it is not an ambiguity, it is silence")))

(tu/deftest-kb two-declarations-at-one-position-reach-what-either-reaches
  (tu/with-terms [tangiblePartOf locatedIn needsAttention Car Engine Garage Bike]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
      (v/assert kb (list 'transitive locatedIn) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
      (v/assert kb (list locatedIn Bike Garage) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needsAttention 1 tangiblePartOf) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needsAttention 1 locatedIn) 'CxUniverse)
      (v/assert kb (list needsAttention Car) 'CxUniverse)
      (v/assert kb (list needsAttention Garage) 'CxUniverse))
    (is (v/ask? kb (list needsAttention Engine) 'CxUniverse)
        "the first declaration reaches, down tangiblePartOf")
    (is (v/ask? kb (list needsAttention Bike) 'CxUniverse)
        "and so does the second, along locatedIn — from the same argument position")))

(tu/deftest-kb both-directions-at-one-position-reach-the-connected-component
  ;; `transitiveInArg` carries `(flagged mammal)` up to `(flagged animal)`, and
  ;; `transitiveInArgInverse` carries that conclusion down to `reptile`: the two
  ;; declarations entail the claim of every kind connected to `mammal`.
  (tu/with-terms [animal_t mammal_t dog_t golden_retriever_t reptile_t flagged]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl mammal_t animal_t) 'CxUniverse)
      (v/assert kb (list 'genl reptile_t animal_t) 'CxUniverse)
      (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
      (v/assert kb (list 'genl golden_retriever_t dog_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse flagged 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg flagged 1 'genl) 'CxUniverse)
      (v/assert kb (list flagged mammal_t) 'CxUniverse))
    (testing "downward, one hop and two"
      (is (v/ask? kb (list flagged dog_t) 'CxUniverse))
      (is (v/ask? kb (list flagged golden_retriever_t) 'CxUniverse)))
    (testing "and upward, by the transitiveInArg declaration at the same position"
      (is (v/ask? kb (list flagged animal_t) 'CxUniverse)))
    (testing "and down again from the superkind, to its other subkinds"
      (is (v/ask? kb (list flagged reptile_t) 'CxUniverse)))))

(tu/deftest-kb two-relations-at-one-position-compose
  ;; `(needsCheck Crate Monday)` reaches `Engine` along `heldIn`, and the conclusion at
  ;; `Engine` reaches `Piston` along `partOf`: a reach across both relations.
  (tu/with-terms [partOf heldIn needsCheck Piston Engine Crate Monday]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) 'CxUniverse)
      (v/assert kb (list 'transitive heldIn) 'CxUniverse)
      (v/assert kb (list partOf Piston Engine) 'CxUniverse)
      (v/assert kb (list heldIn Engine Crate) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needsCheck 1 partOf) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needsCheck 1 heldIn) 'CxUniverse)
      (v/assert kb (list needsCheck Crate Monday) 'CxUniverse))
    (is (v/ask? kb (list needsCheck Engine Monday) 'CxUniverse) "one heldIn step")
    (is (v/ask? kb (list needsCheck Piston Monday) 'CxUniverse) "heldIn, then partOf")
    (is (not (v/ask? kb (list needsCheck Crate 'TmpTuesday) 'CxUniverse)))))

(tu/deftest-kb a-denial-at-a-term-between-two-relations-undercuts-the-claim-above-it
  ;; The joint reach orders claims too: `Engine` lies between `Piston` and `Crate`, so the
  ;; denial stated at `Engine` is more specific than the default claim at `Crate`.
  (tu/with-terms [partOf heldIn needsCheck Piston Engine Crate Monday]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) 'CxUniverse)
      (v/assert kb (list 'transitive heldIn) 'CxUniverse)
      (v/assert kb (list partOf Piston Engine) 'CxUniverse)
      (v/assert kb (list heldIn Engine Crate) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needsCheck 1 partOf) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse needsCheck 1 heldIn) 'CxUniverse)
      (v/assert kb (list needsCheck Crate Monday) 'CxUniverse)
      (v/assert kb (list 'not (list needsCheck Engine Monday)) 'CxUniverse))
    (is (= :against (inherit/verdict kb (list needsCheck Piston Monday) 'CxUniverse)))))

(defn- mereology!
  "`(transitive partOf)`, `(transitive locatedIn)`, `(transitiveInArgInverse locatedIn 1
  partOf)`, and the parts and places of `terms`."
  [kb {:keys [partOf locatedIn Piston Engine Car Garage House]}]
  (v/with-deferred-settle kb
    (v/assert kb (list 'transitive partOf) 'CxUniverse)
    (v/assert kb (list 'transitive locatedIn) 'CxUniverse)
    (v/assert kb (list 'transitiveInArgInverse locatedIn 1 partOf) 'CxUniverse)
    (v/assert kb (list partOf Piston Engine) 'CxUniverse)
    (v/assert kb (list partOf Engine Car) 'CxUniverse)
    (v/assert kb (list locatedIn Car Garage) 'CxUniverse)
    (v/assert kb (list locatedIn Garage House) 'CxUniverse)))

(tu/deftest-kb a-preserved-transitive-predicate-composes-with-its-own-transitivity
  ;; `(locatedIn Garage House)` is a claim the prover reads at `Car`'s reach once
  ;; `(locatedIn Car Garage)` composes with it, and `Piston` is a part of `Car`.
  (tu/with-terms [partOf locatedIn Piston Engine Car Garage House Key]
    (mereology! kb {:partOf partOf :locatedIn locatedIn :Piston Piston :Engine Engine
                    :Car Car :Garage Garage :House House})
    (is (v/ask? kb (list locatedIn Piston Garage) 'CxUniverse) "a part is where its whole is")
    (is (v/ask? kb (list locatedIn Piston House) 'CxUniverse) "and where that place is")
    (is (not (v/ask? kb (list locatedIn Piston Car) 'CxUniverse)) "a whole is no place")
    (testing "a located thing inside a part reaches past the whole"
      (v/assert kb (list locatedIn Key Piston) 'CxUniverse)
      (is (v/ask? kb (list locatedIn Key House) 'CxUniverse)))))

(tu/deftest-kb the-self-relation-carries-no-denial
  ;; `(locatedIn Car Garage)` and `(not (locatedIn Garage Shed))` leave `(locatedIn Car
  ;; Shed)` open, so the denial reaches `Car` along no `locatedIn` step; a denial at `Car`
  ;; reaches its part `Engine` along `partOf`.
  (tu/with-terms [partOf locatedIn Piston Engine Car Garage House Shed]
    (mereology! kb {:partOf partOf :locatedIn locatedIn :Piston Piston :Engine Engine
                    :Car Car :Garage Garage :House House})
    (v/assert kb (list 'not (list locatedIn Garage Shed)) 'CxUniverse)
    (is (nil? (inherit/verdict kb (list locatedIn Car Shed) 'CxUniverse)))
    (v/assert kb (list 'not (list locatedIn Car Shed)) 'CxUniverse)
    (is (= :against (inherit/verdict kb (list locatedIn Engine Shed) 'CxUniverse)))))

(tu/deftest-kb a-position-reaches-along-genl-and-a-declared-relation
  ;; The two declarations at one position need not name the same *kind* of relation:
  ;; `genl` reads the engine's cached type closure, `tangiblePartOf` is walked over stored
  ;; facts, and the position's reach is their joint closure — the same argument descending
  ;; a type chain and a part chain at once.
  (tu/with-terms [equipment_t lathe_t Chuck tangiblePartOf hazard]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
      (v/assert kb (list 'genl lathe_t equipment_t) 'CxUniverse)
      (v/assert kb (list tangiblePartOf Chuck equipment_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse hazard 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse hazard 1 tangiblePartOf) 'CxUniverse)
      (v/assert kb (list hazard equipment_t) 'CxUniverse))
    (is (v/ask? kb (list hazard lathe_t) 'CxUniverse)
        "down the cached type closure: a kind of equipment")
    (is (v/ask? kb (list hazard Chuck) 'CxUniverse)
        "down the stored part chain: a part of the equipment")
    (is (not (v/ask? kb (list hazard 'TmpBystander) 'CxUniverse))
        "and a term on neither chain inherits nothing")))

(tu/deftest-kb opposite-directions-at-two-positions-compose-in-one-goal
  ;; A predicate may preserve one position forward and another backward.  A ground goal's
  ;; tuple is the product of the positions' reaches, so `(outshadows predator rabbit)`
  ;; answers a goal about a *subkind* of the first argument and a *superkind* of the
  ;; second at once — while neither position's direction leaks into the other.
  (tu/with-terms [predator_t wolf_t big_animal_t rabbit_t bunny_t small_mammal_t outshadows]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl wolf_t predator_t) 'CxUniverse)
      (v/assert kb (list 'genl predator_t big_animal_t) 'CxUniverse)
      (v/assert kb (list 'genl rabbit_t small_mammal_t) 'CxUniverse)
      (v/assert kb (list 'genl bunny_t rabbit_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse outshadows 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg outshadows 2 'genl) 'CxUniverse)
      (v/assert kb (list outshadows predator_t rabbit_t) 'CxUniverse))
    (is (v/ask? kb (list outshadows wolf_t small_mammal_t) 'CxUniverse)
        "position 1 to a subkind, position 2 to a superkind, in one goal")
    (testing "and each position keeps to its own direction"
      (is (not (v/ask? kb (list outshadows big_animal_t rabbit_t) 'CxUniverse))
          "arg1 is forward-only — the claim does not climb to predator's superkind")
      (is (not (v/ask? kb (list outshadows predator_t bunny_t) 'CxUniverse))
          "arg2 is inverse-only — the claim does not descend to rabbit's subkind"))))

;; ---- specificity: the stated claim overrides the inherited one -----------

(tu/deftest-kb a-specific-default-claim-undercuts-the-general-one
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typicallyLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typicallyLargerThan)
    (v/assert kb (list typicallyLargerThan dog_t cat_t) 'CxUniverse)   ; :default
    (is (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'CxUniverse)
        "inherited before anything contradicts it")
    (testing "the more specific contrary claim is accepted, not refused"
      (is (integer? (v/assert kb (list typicallyLargerThan maine_coon_t chihuahua_t)
                              'CxUniverse))))
    (testing "and it wins for that pair"
      (is (v/ask? kb (list typicallyLargerThan maine_coon_t chihuahua_t) 'CxUniverse))
      (is (not (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'CxUniverse))))
    (testing "without defeating the general claim or leaving anything to arbitrate"
      (is (v/ask? kb (list typicallyLargerThan dog_t cat_t) 'CxUniverse))
      (is (empty? (v/contradictions kb)))
      (is (empty? (v/conflicts kb))))
    (testing "and untouched pairs still inherit"
      (is (v/ask? kb (list typicallyLargerThan golden_retriever_t siamese_t) 'CxUniverse))
      (is (v/ask? kb (list typicallyLargerThan golden_retriever_t maine_coon_t) 'CxUniverse)))))

(tu/deftest-kb an-explicit-negation-undercuts-the-same-way
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typicallyLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list 'transitiveInArgInverse typicallyLargerThan 1 'genl) 'CxUniverse)
    (v/assert kb (list 'transitiveInArgInverse typicallyLargerThan 2 'genl) 'CxUniverse)
    (v/assert kb (list typicallyLargerThan dog_t cat_t) 'CxUniverse)
    (is (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'CxUniverse))
    (v/assert kb (list 'not (list typicallyLargerThan chihuahua_t maine_coon_t)) 'CxUniverse)
    (is (not (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'CxUniverse))
        "the negation is the most specific claim about that pair")
    (is (v/ask? kb (list typicallyLargerThan golden_retriever_t maine_coon_t) 'CxUniverse)
        "and says nothing about any other")))

(tu/deftest-kb a-claim-and-its-negation-at-one-tuple-are-not-a-clean-for
  ;; The KB holds both `P` and `(not P)` of one pair, reports the dilemma through
  ;; `contradictions`, and believes both at `:default`.  Every probe per tuple is
  ;; therefore made: taking whichever answered first would read this as a clean `:for`
  ;; and hand `verdict` a decision the engine, looking at the same two sentexes,
  ;; refuses to make.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  rankedOver]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitiveInArgInverse rankedOver 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse rankedOver 2 'genl) 'CxUniverse)
      (v/assert kb (list rankedOver dog_t cat_t) 'CxUniverse)
      (v/assert kb (list 'not (list rankedOver dog_t cat_t)) 'CxUniverse))
    (is (seq (v/contradictions kb))
        "the engine represents the pair rather than deciding it")
    (is (= :ambiguous (inherit/verdict kb (list rankedOver dog_t cat_t) 'CxUniverse))
        "and so does this, about the same two sentexes")
    (is (= :ambiguous (inherit/verdict kb (list rankedOver chihuahua_t maine_coon_t)
                                       'CxUniverse))
        "the pair the contradictory tuple reaches inherits the ambiguity, not the :for")
    (is (not (v/ask? kb (list rankedOver chihuahua_t maine_coon_t) 'CxUniverse))
        "so nothing is answered for the inherited pair")
    (is (v/ask? kb (list rankedOver dog_t cat_t) 'CxUniverse)
        "while the stated pair is still answered — by the fact prover, which reads the
         believed positive sentex and is not this prover")))

(tu/deftest-kb incomparable-claims-are-not-decided
  ;; Two claims that disagree and neither of which is more specific.  The engine's
  ;; stance on an unresolvable clash is to represent it, so the prover answers nothing
  ;; rather than picking a side.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  pet_t predator_t rankedOver]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t pet_t) 'CxUniverse)
      (v/assert kb (list 'genl maine_coon_t predator_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse rankedOver 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse rankedOver 2 'genl) 'CxUniverse)
      (v/assert kb (list rankedOver dog_t cat_t) 'CxUniverse)
      (v/assert kb (list 'not (list rankedOver pet_t predator_t)) 'CxUniverse))
    (is (= :ambiguous (inherit/verdict kb (list rankedOver chihuahua_t maine_coon_t)
                                       'CxUniverse))
        "[dog cat] and [pet predator] both reach the pair and neither is below the other")
    (is (not (v/ask? kb (list rankedOver chihuahua_t maine_coon_t) 'CxUniverse))
        "so nothing is answered")))

;; ---- strict: the same shape, defeated instead of overridden --------------

(tu/deftest-kb a-contrary-claim-against-known-true-content-is-stored-and-loses
  ;; known-true content here is the claim and the reading: the edges and the declarations
  ;; are `:monotonic` too
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t typeLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t}
            {:strength :monotonic})
    (preserving! kb typeLargerThan {:strength :monotonic})
    (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (testing "the inherited claim is as binding as the one that was written"
      (is (tu/stored-in-clash? kb (list typeLargerThan maine_coon_t chihuahua_t) 'CxUniverse)))
    (testing "and so is the plain converse of a directly-stated one"
      (is (tu/stored-in-clash? kb (list typeLargerThan cat_t dog_t) 'CxUniverse)))
    (testing "neither contrary claim is believed, and the known-true reading stands"
      (is (not (v/ask? kb (list typeLargerThan maine_coon_t chihuahua_t) 'CxUniverse)))
      (is (not (v/ask? kb (list typeLargerThan cat_t dog_t) 'CxUniverse)))
      (is (v/ask? kb (list typeLargerThan chihuahua_t maine_coon_t) 'CxUniverse)))))

(tu/deftest-kb a-contrary-claim-against-a-default-reading-is-believed-and-reports-nothing
  ;; the claim known-true and the edges and declarations `:default`: the reading is capped
  ;; at `:default`, so it is undercut, the converse is believed, and no clash forms
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t typeLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typeLargerThan)
    (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (is (integer? (v/assert kb (list typeLargerThan maine_coon_t chihuahua_t) 'CxUniverse)))
    (is (v/ask? kb (list typeLargerThan maine_coon_t chihuahua_t) 'CxUniverse))
    (is (empty? (v/contradictions kb)))
    (is (empty? (v/conflicts kb)))))

(tu/deftest-kb asymmetry-alone-catches-a-converse-with-no-inheritance
  ;; The check does not need a preserved position: an asymmetric predicate's converse
  ;; contradicts it wherever both are known true.
  (tu/with-terms [dog_t cat_t typeLargerThan]
    (v/assert kb (list 'asymmetric typeLargerThan) 'CxUniverse)
    (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (is (tu/stored-in-clash? kb (list typeLargerThan cat_t dog_t) 'CxUniverse))
    (is (not (v/ask? kb (list typeLargerThan cat_t dog_t) 'CxUniverse)))))

(tu/deftest-kb a-default-general-claim-leaves-the-contrary-claim-believed
  ;; The whole strict/typical difference, isolated: same vocabulary, same declarations,
  ;; only the strength of the general claim differs.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t typeLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typeLargerThan)
    (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)     ; :default, not monotonic
    (is (integer? (v/assert kb (list typeLargerThan maine_coon_t chihuahua_t) 'CxUniverse)))
    (is (v/ask? kb (list typeLargerThan maine_coon_t chihuahua_t) 'CxUniverse)
        "believed, where the monotonic version defeats it")))

;; ---- order independence ---------------------------------------------------

(defn- believes-converse?
  "State `(P a b)` in a super-context and a sub-context at the two given strengths, in
  the given order, then store the converse in the sub-context and report whether the
  sub-context believes it."
  [kb {:keys [pred a b super sub order]}]
  ;; the declarations below live in CxUniverse, and the asymmetry check reads
  ;; them from the asserting context's ancestor set — so the lattice is wired below it
  (v/assert kb (list 'genlCx super 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx sub super) 'CxUniverse)
  (v/assert kb (list 'asymmetric pred) 'CxUniverse)
  (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
  (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
  (doseq [[where strength] order]
    (v/assert kb (list pred a b) (if (= where :super) super sub) {:strength strength}))
  (v/assert kb (list pred b a) sub)
  (v/ask? kb (list pred b a) sub))

(tu/deftest-kb the-strongest-visible-claim-decides-not-the-first-one-stored
  ;; One sentence, two visible contexts, two strengths.  Every combination of (which
  ;; context holds the monotonic claim) x (which was asserted first) must give the same
  ;; answer, and it must be the strong one: a claim that is known true anywhere the asking
  ;; context can see is a fixed background.
  (doseq [[i strong] (map-indexed vector [:super :sub])
          [j first-where] (map-indexed vector [:super :sub])]
    (tu/with-terms [dog_t cat_t typeLargerThan CxSuper CxSub]
      (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
      (let [strength (fn [w] (if (= w strong) :monotonic :default))
            order    (if (= first-where :super)
                       [[:super (strength :super)] [:sub (strength :sub)]]
                       [[:sub (strength :sub)] [:super (strength :super)]])]
        (is (false? (believes-converse? kb {:pred typeLargerThan :a dog_t :b cat_t
                                            :super CxSuper :sub CxSub
                                            :order order}))
            (str "monotonic in " (name strong) ", " (name first-where) " asserted first ["
                 i j "]: the converse of known-true content loses either way"))))))

(tu/deftest-kb the-supporter-a-fan-answers-with-is-the-content-least-not-the-first
  ;; What licenses a reach along a fact-relation includes the `(transitive R)` the
  ;; closure is taken under, and that licence is **read** rather than stored with the
  ;; claim — `matches-visible` answers it, and `matches-visible` is type-aware.  So a
  ;; sub-predicate's sentex answers the query for it and the matches are a fan rather
  ;; than one sentence: three of them here, all in one context, spelling three different
  ;; claims that the asserting context's name cannot separate.  The handle named is the
  ;; one a recorded justification carries, so it decides what a later retraction
  ;; withdraws — and it has to be a function of the content rather than of which of the
  ;; three the retrieval happened to enumerate first.
  (doseq [flip [false true]]
    (tu/with-terms [tangiblePartOf needs_maintenance Car Engine alphaTransitive betaTransitive]
      (let [subs  [(list alphaTransitive tangiblePartOf) (list betaTransitive tangiblePartOf)]
            fan   (cons (list 'transitive tangiblePartOf) subs)
            least (first (sort-by pr-str fan))
            what  (str "the " (if flip "beta" "alpha") " sub-predicate asserted first")]
        (v/with-deferred-settle kb
          (v/assert kb (list 'genl alphaTransitive 'transitive) 'CxUniverse)
          (v/assert kb (list 'genl betaTransitive 'transitive) 'CxUniverse)
          ;; the plain declaration too: `transitiveInArg` refuses a relation nobody has
          ;; said composes, and a sub-predicate's sentex does not mark the property
          (v/assert kb (list 'transitive tangiblePartOf) 'CxUniverse)
          (doseq [s (if flip (reverse subs) subs)] (v/assert kb s 'CxUniverse))
          (v/assert kb (list tangiblePartOf Engine Car) 'CxUniverse)
          (v/assert kb (list 'transitiveInArgInverse needs_maintenance 1 tangiblePartOf) 'CxUniverse)
          (v/assert kb (list needs_maintenance Car) 'CxUniverse))
        (is (v/ask? kb (list needs_maintenance Engine) 'CxUniverse)
            (str what ": the claim reaches down the part chain"))
        (is (= 3 (count (res/matches-visible kb (list 'transitive tangiblePartOf) 'CxUniverse)))
            (str what ": the licence query is answered by a fan, or this proves nothing"))
        (let [named (into #{} (map #(:sentence (v/sentex kb %)))
                          (:handles (first (inherit/supports-for kb (list needs_maintenance Engine)
                                                                 'CxUniverse))))]
          (is (contains? named least) (str what ": the content-least of the fan is named"))
          (is (= 1 (count (filter named fan)))
              (str what ": and one of them, since one complete reason is the whole of it")))))))

;; ---- the exception re-check trigger ---------------------------------------

(tu/deftest-kb a-genl-edge-among-the-arguments-rechecks-an-exception
  ;; `TransitiveInArgProver` answers a level-6 exception query by walking the *arguments'*
  ;; genl closure, so an edge between two types can flip an exception stated over a
  ;; predicate neither type appears in.  The predicate-keyed re-check cannot see that;
  ;; without the argument-side trigger the firings that predate the edge keep a
  ;; conclusion the firings after it correctly drop.
  (tu/with-terms [dog_t cat_t maine_coon_t chihuahua_t typeLargerThan fitsIn Tiny Other]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl maine_coon_t cat_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
      (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse))
    ;; a chihuahua fits in the box, unless a chihuahua is larger than a maine coon
    (v/assert kb (list 'exceptWhen (list typeLargerThan chihuahua_t maine_coon_t)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list 'and (list chihuahua_t '?x))
                                                          (list fitsIn '?x)))))
              'CxUniverse)
    (v/assert kb (list chihuahua_t Tiny) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list fitsIn Tiny) 'CxUniverse))
        "baseline: the exception does not hold, so the rule fires")

    ;; the edge makes the exception hold, by inheritance from (typeLargerThan dog cat)
    (v/assert kb (list 'genl chihuahua_t dog_t) 'CxUniverse)
    (is (v/ask? kb (list typeLargerThan chihuahua_t maine_coon_t) 'CxUniverse)
        "the exception's query is now answered by argument preservation")
    (is (empty? (v/sentexes-matching kb (list fitsIn Tiny) 'CxUniverse))
        "so the conclusion that predates the edge is withdrawn")

    (v/assert kb (list chihuahua_t Other) 'CxUniverse)
    (is (empty? (v/sentexes-matching kb (list fitsIn Other) 'CxUniverse))
        "and a fresh firing agrees with it")))

(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(tu/deftest-kb a-separated-membership-releases-an-exception-on-an-inherited-membership-in-every-order
  ;; `(down_kind upper)` reaches `(down_kind lower)`, which holds the exception, until
  ;; `(plain_kind lower)` and the separation undercut the `:default` reading.  The two
  ;; arrive in any order around the rule and its premise, and the firing is re-decided.
  (is (= #{[false true]}
         (into #{}
               (for [order (permutations [:sep :member :rule :premise])]
                 (tu/with-terms [down_kind plain_kind upper lower probe_kind fits Thing]
                   (v/assert kb (list 'transitiveInArgInverse down_kind 1 'genl) 'CxUniverse)
                   (v/assert kb (list 'genl lower upper) 'CxUniverse)
                   (v/assert kb (list down_kind upper) 'CxUniverse)
                   (doseq [op order]
                     (case op
                       :sep     (v/assert kb (list 'disjoint down_kind plain_kind) 'CxUniverse
                                          {:strength :monotonic})
                       :member  (v/assert kb (list plain_kind lower) 'CxUniverse)
                       :rule    (v/assert kb (list 'exceptWhen (list down_kind lower)
                                                   (list 'set/defaultRule
                                                         (list 'set/forwardRule
                                                               (list 'implies (list probe_kind '?x)
                                                                     (list fits '?x)))))
                                          'CxUniverse)
                       :premise (v/assert kb (list probe_kind Thing) 'CxUniverse)))
                   [(v/ask? kb (list down_kind lower) 'CxUniverse)
                    (boolean (seq (v/sentexes-matching kb (list fits Thing) 'CxUniverse)))]))))))

(tu/deftest-kb a-separated-membership-undercuts-a-default-reading-where-the-separation-is-seen
  ;; The separation is stated in CxA alone, so CxUniverse reads `(down_kind lower)` and CxA
  ;; reads it undercut by `(plain_kind lower)`.
  (is (= #{[true false]}
         (into #{}
               (for [order (permutations [:sep :member :claim])]
                 (tu/with-terms [down_kind plain_kind upper lower CxA]
                   (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                   (v/assert kb (list 'transitiveInArgInverse down_kind 1 'genl) 'CxUniverse)
                   (v/assert kb (list 'genl lower upper) 'CxUniverse)
                   (doseq [op order]
                     (case op
                       :sep    (v/assert kb (list 'disjoint down_kind plain_kind) CxA)
                       :member (v/assert kb (list plain_kind lower) 'CxUniverse)
                       :claim  (v/assert kb (list down_kind upper) 'CxUniverse)))
                   [(v/ask? kb (list down_kind lower) 'CxUniverse)
                    (v/ask? kb (list down_kind lower) CxA)]))))))

(tu/deftest-kb a-reached-denial-answers-the-negated-goal-and-its-exception-whichever-sentence-arrives-last
  ;; `(not (bigP dog cat))` reaches `(bigP chi mc)` along both positions, and the rule's
  ;; exception asks `(not (bigP chi mc))`.  Each row is `[ask? positive, ask? negated,
  ;; firing believed]`; the row without `:edge` reaches nothing.  Each sentence arrives
  ;; last once, which is the arrival the re-check answers for.
  (let [mono {:strength :monotonic}]
    (doseq [[strength items want]
            [[:monotonic [:edge :deny :decl :rule :premise] [false true false]]
             [:default   [:edge :deny :decl :rule :premise] [false true false]]
             [:monotonic [:deny :decl :rule :premise]       [false false true]]]]
      (is (= #{want}
             (into #{}
                   (for [order (map #(concat (remove #{%} items) [%]) items)]
                     (tu/with-terms [bigP probe_kind fits dog_t cat_t chi_t mc_t Thing]
                       (v/assert kb (list 'genl mc_t cat_t) 'CxUniverse mono)
                       (doseq [op order]
                         (case op
                           :edge    (v/assert kb (list 'genl chi_t dog_t) 'CxUniverse mono)
                           :deny    (v/assert kb (list 'not (list bigP dog_t cat_t)) 'CxUniverse
                                              {:strength strength})
                           :decl    (doseq [n [1 2]]
                                      (v/assert kb (list 'transitiveInArgInverse bigP n 'genl)
                                                'CxUniverse mono))
                           :rule    (v/assert kb (list 'exceptWhen (list 'not (list bigP chi_t mc_t))
                                                       (list 'set/forwardRule
                                                             (list 'implies (list probe_kind '?x)
                                                                   (list fits '?x))))
                                              'CxUniverse)
                           :premise (v/assert kb (list probe_kind Thing) 'CxUniverse)))
                       [(v/ask? kb (list bigP chi_t mc_t) 'CxUniverse)
                        (v/ask? kb (list 'not (list bigP chi_t mc_t)) 'CxUniverse)
                        (boolean (seq (v/sentexes-matching kb (list fits Thing) 'CxUniverse)))]))))
          (str strength " " items)))))

(tu/deftest-kb a-separated-membership-answers-a-denial-only-over-known-true-edges
  ;; `(mid_kind lower)` climbs `(genl mid_kind plain_kind)` to the separation from
  ;; `down_kind`.  The separation undercuts a claim over either edge, and a `:default` edge
  ;; fails the soundness rule a refutation is held to.
  (doseq [[strength want] [[:default false] [:monotonic true]]]
    (tu/with-terms [down_kind plain_kind mid_kind lower]
      (v/assert kb (list 'transitiveInArgInverse down_kind 1 'genl) 'CxUniverse)
      (v/assert kb (list 'disjoint down_kind plain_kind) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl mid_kind plain_kind) 'CxUniverse {:strength strength})
      (v/assert kb (list mid_kind lower) 'CxUniverse)
      (is (= want (v/ask? kb (list 'not (list down_kind lower)) 'CxUniverse))
          (str strength)))))

;; ---- the memo's growth claim, counted -------------------------------------
;;
;; docs/inherit.md, "What one question costs": the reach walk is linear in the claims.
;; `res/matches-visible` is the probe point: a reach over a fact-relation reads it once per
;; node walked (`inherit/fact-reach`).
;;
;; A ratio of **second differences** rather than an exact number: linear growth doubles the
;; step from 4→8 claims to 8→16 and quadratic growth quadruples it, so 3.0 sits between the
;; two with room on either side.  `lein perf`'s `inherit-reach-memo` holds the same claim as
;; a duration, and neither subsumes the other — a count cannot see a slower walk and a
;; duration cannot see a constant.

(defn- visible-reads
  "How many `res/matches-visible` calls `run` makes."
  [run]
  (let [n (atom 0), orig @#'res/matches-visible]
    (with-redefs-fn {#'res/matches-visible (fn [& args] (swap! n inc) (apply orig args))}
      (fn [] (run) @n))))

(defn- preserved-fan!
  "`rel` transitive with `base` a part of every one of `owners`, `pred` preserved along
  `rel` at position 1, and `pred` stated of every owner.  So a goal about `base` has one
  claim per owner and no two of them are comparable — every claim survives, and
  `undercut?` asks for a reach once per *pair* on the way to saying so."
  [kb rel pred base owners]
  (v/with-deferred-settle kb
    (v/assert kb (list 'transitive rel) 'CxUniverse)
    (v/assert kb (list 'transitiveInArgInverse pred 1 rel) 'CxUniverse)
    (doseq [o owners]
      (v/assert kb (list rel base o) 'CxUniverse)
      (v/assert kb (list pred o) 'CxUniverse))))

(defn- reach-reads
  "What `inherit/surviving` costs in visible reads over `n` incomparable claims about one
  term — each size gets its own relation, predicate and term, so the three do not share a
  reach."
  [kb n]
  (tu/with-terms [tangiblePartOf needsWork]
    (let [base   (tu/tmp-ind "Part")
          owners (into [] (repeatedly n #(tu/tmp-ind "Whole")))
          drain  #(doall (inherit/surviving kb (list needsWork base) 'CxUniverse))]
      (preserved-fan! kb tangiblePartOf needsWork base owners)
      (drain)                                  ; warm whatever caches persist between asks
      (is (= n (count (drain))) "one surviving claim per owner, none comparable")
      (visible-reads drain))))

(tu/deftest-kb the-reach-walk-is-linear-in-the-claims-and-not-quadratic
  (let [r4  (reach-reads kb 4)
        r8  (reach-reads kb 8)
        r16 (reach-reads kb 16)]
    (is (< r4 r8 r16) "the reading really does grow with the claims")
    (is (< (/ (double (- r16 r8)) (double (- r8 r4))) 3.0)
        (str "the second difference must double and not quadruple — got "
             r4 " / " r8 " / " r16 " reads at 4 / 8 / 16 claims"))))

(defn- visible-rows
  "How many rows the `res/matches-visible` calls `run` makes return."
  [run]
  (let [n (atom 0), orig @#'res/matches-visible]
    (with-redefs-fn {#'res/matches-visible
                     (fn [& args] (let [r (apply orig args)] (swap! n + (count r)) r))}
      (fn [] (run) @n))))

(tu/deftest-kb the-extent-estimate-counts-the-sub-predicates-the-probe-fans-over
  ;; `typeLargerThan` stores nothing and its sub-predicate stores n facts about terms outside
  ;; the goal's four-tuple product.  The open probe of `typeLargerThan` walks those n facts
  ;; through the sub-predicate fan, so the product's four ground probes are the cheaper
  ;; path at every n.
  (let [rows (fn [n]
               (tu/with-terms [dog_t animal_t cat_t feline_t typeLargerThan muchLargerThan]
                 (v/with-deferred-settle kb
                   (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse)
                   (v/assert kb (list 'genl cat_t feline_t) 'CxUniverse)
                   (v/assert kb (list 'genl muchLargerThan typeLargerThan) 'CxUniverse)
                   (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
                   (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
                   (dotimes [_ n]
                     (v/assert kb (list muchLargerThan (tu/tmp-ind "A") (tu/tmp-ind "B"))
                               'CxUniverse)))
                 (visible-rows
                  #(is (empty? (inherit/claims kb (list typeLargerThan dog_t cat_t) 'CxUniverse))))))]
    (is (= (rows 8) (rows 64)))))

(tu/deftest-kb a-denial-probe-is-priced-at-the-stored-denials
  ;; `bigger` stores 16 positive facts outside the goal's four-tuple product and no
  ;; denial.  The negated probe walks the negative rows alone, so it reads the open probe
  ;; once and probes none of the four tuples.
  (tu/with-terms [dog_t animal_t cat_t feline_t bigger]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse)
      (v/assert kb (list 'genl cat_t feline_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse bigger 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse bigger 2 'genl) 'CxUniverse)
      (dotimes [_ 16]
        (v/assert kb (list bigger (tu/tmp-ind "A") (tu/tmp-ind "B")) 'CxUniverse)))
    (let [probes (atom []), orig @#'res/matches-visible]
      (with-redefs-fn {#'res/matches-visible
                       (fn [& args]
                         (let [s (second args)]
                           (when (and (seq? s) (= 'not (first s)))
                             (swap! probes conj s)))
                         (apply orig args))}
        #(is (empty? (inherit/claims kb (list bigger dog_t cat_t) 'CxUniverse))))
      (is (= [(list 'not (list bigger '?w0 '?w1))] (distinct @probes))))))

(defn- walked-rows
  "`[answer rows]`: what `run` answers (the thrown `ex-data` when it throws one), and how
  many distinct rows it pulls off the open `(pred ?w0 …)` probe.  The first row each probe
  pulls sleeps `sleep-ms`.  Distinct by handle, since `matches-visible` answers through a
  nested call of itself and each row passes both wrappers."
  [pred sleep-ms run]
  (let [seen (atom #{}), orig @#'res/matches-visible
        counted (fn counted [s first?]
                  (lazy-seq
                   (when-let [c (seq s)]
                     (when first? (Thread/sleep (long sleep-ms)))
                     (swap! seen conj (first (first c)))
                     (cons (first c) (counted (rest c) false)))))]
    (with-redefs-fn {#'res/matches-visible
                     (fn [kb sentence & more]
                       (let [r (apply orig kb sentence more)]
                         (if (and (seq? sentence) (= pred (first sentence))
                                  (some #{'?w0} sentence))
                           (counted r true)
                           r)))}
      (fn [] [(try (run) (catch clojure.lang.ExceptionInfo e (ex-data e))) (count @seen)]))))

(tu/deftest-kb an-ask-deadline-stops-the-claim-walk-at-the-row-it-passes-on
  ;; The extent arm is forced, and its first row sleeps past a 10 ms deadline, so every
  ;; later row is read with the deadline passed.  A sleep sets a floor on the clock and no
  ;; ceiling, so the row counts hold on a loaded box.
  (doseq [n [16 128]]
    (tu/with-terms [dog_t cat_t gr_t mc_t typeLargerThan]
      (v/with-deferred-settle kb
        (v/assert kb (list 'genl gr_t dog_t) 'CxUniverse)
        (v/assert kb (list 'genl mc_t cat_t) 'CxUniverse)
        (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
        (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
        (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
        (dotimes [_ n]
          (v/assert kb (list typeLargerThan (tu/tmp-ind "A") (tu/tmp-ind "B")) 'CxUniverse)))
      (binding [inherit/*retrieval* :extent]
        (let [goal (list typeLargerThan gr_t mc_t)
              walk (fn [run] (walked-rows typeLargerThan 20 run))]
          (testing (str "at an extent of " n)
            (is (= [true (inc n)] (walk #(v/ask? kb goal 'CxUniverse)))
                "with no deadline the walk reads the whole extent and finds the claim")
            (let [[refusal rows] (walk #(v/ask? kb goal 'CxUniverse {:max-ms 10}))]
              (is (= :budget-exhausted (:type refusal)))
              (is (<= rows 1)))
            (let [[partial rows] (walk #(v/ask-within kb goal 'CxUniverse {:max-ms 10}))]
              (is (= [:timeout []] [(:status partial) (:results partial)]))
              (is (<= rows 1)))
            (is (= [{}] (first (walk #(loop [p (v/ask-within kb goal 'CxUniverse {:max-ms 10})
                                             acc [], steps 1]
                                        (cond (nil? (:resume p)) (into acc (:results p))
                                              (< steps 10) (recur (v/resume p {:max-ms 10})
                                                                  (into acc (:results p))
                                                                  (inc steps))
                                              :else        :runaway)))))
                "a resume runs the stopped walk to its end, so a resume loop under the same
                 budget terminates with the unbounded answer")))))))

(tu/deftest-kb a-prove-deadline-stops-the-claim-walk-at-the-row-it-passes-on
  ;; The ask witness's fixture, answered as a `prove` leaf on both engines: the extent arm
  ;; is forced and its first row sleeps past a 10 ms deadline.
  (doseq [n [16 128], engine [:dfs :inference]]
    (tu/with-terms [dog_t cat_t gr_t mc_t typeLargerThan]
      (v/with-deferred-settle kb
        (v/assert kb (list 'genl gr_t dog_t) 'CxUniverse)
        (v/assert kb (list 'genl mc_t cat_t) 'CxUniverse)
        (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
        (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
        (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
        (dotimes [_ n]
          (v/assert kb (list typeLargerThan (tu/tmp-ind "A") (tu/tmp-ind "B")) 'CxUniverse)))
      (binding [inherit/*retrieval* :extent
                v/*query-engine*    engine]
        (let [goal   (list typeLargerThan gr_t mc_t)
              walk   (fn [run] (walked-rows typeLargerThan 20 run))
              budget {:max-ms 10 :max-depth 2}]
          (testing (str "at an extent of " n " on the " engine " engine")
            (is (= [[{}] (inc n)] (walk #(v/prove kb goal 'CxUniverse {:max-depth 2})))
                "with no deadline the walk reads the whole extent and finds the claim")
            (is (= [true (inc n)] (walk #(v/provable? kb goal 'CxUniverse {:max-depth 2}))))
            (doseq [[label run] [["prove" #(v/prove kb goal 'CxUniverse budget)]
                                 ["provable?" #(v/provable? kb goal 'CxUniverse budget)]]]
              (let [[refusal rows] (walk run)]
                (is (= :budget-exhausted (:type refusal)) label)
                (is (<= rows 1) label)))
            (let [[partial rows] (walk #(v/prove-within kb goal 'CxUniverse budget))]
              (is (= [:timeout []] [(:status partial) (:results partial)]))
              (is (<= rows 1)))
            (is (= [{}] (first (walk #(loop [p (v/prove-within kb goal 'CxUniverse budget)
                                             acc [], steps 1]
                                        (cond (nil? (:resume p)) (into acc (:results p))
                                              (< steps 10) (recur (v/resume p budget)
                                                                  (into acc (:results p))
                                                                  (inc steps))
                                              :else        :runaway)))))
                "a resume runs the stopped walk to its end, so a resume loop under the same
                 budget terminates with the unbounded answer")))))))

(tu/deftest-kb a-claims-reader-other-than-the-ask-prover-walks-past-the-deadline
  ;; `claims` is also read by the asymmetry check at assert, settle and forward chaining,
  ;; and those walk the whole extent under a deadline already passed.
  (tu/with-terms [dog_t cat_t typeLargerThan]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 2 'genl) 'CxUniverse)
      (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
      (dotimes [_ 16]
        (v/assert kb (list typeLargerThan (tu/tmp-ind "A") (tu/tmp-ind "B")) 'CxUniverse)))
    (binding [inherit/*retrieval* :extent]
      (is (= [1 17]
             (walked-rows typeLargerThan 0
                          #(binding [budget/*deadline* (System/nanoTime)]
                             (count (inherit/claims kb (list typeLargerThan dog_t cat_t)
                                                    'CxUniverse)))))))))
