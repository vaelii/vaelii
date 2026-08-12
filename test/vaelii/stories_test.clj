;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stories-test
  "Connected conjunctive antecedents (rules whose antecedents share variables so
  they join) and the children's stories that use them to derive their morals — over
  the starter KB."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

;; ---- connected conjunctive antecedents in the starter -------------------

(tu/deftest-kb a-part-is-located-where-its-whole-is
  ;; (implies (and (partOf ?part ?whole) (locatedIn ?whole ?place)) (locatedIn ?part ?place))
  ;; joins on ?whole — the Engine is in the Garage because the Car is.
  (testing "the joined rule places the part in the whole's location"
    (is (seq (v/sentexes-matching kb '(locatedIn Engine1 Garage1) 'CxNaturalWorld)))
    ;; Piston1 partOf Engine1, and Engine1's derived location feeds the rule again
    (is (seq (v/sentexes-matching kb '(locatedIn Piston1 Garage1) 'CxNaturalWorld))))
  (testing "the forward conclusion composes with transitive locatedIn"
    ;; locatedIn Engine1 Garage1 (derived) + locatedIn Garage1 House1 ⇒ Engine1 in House1
    (is (v/ask? kb '(locatedIn Engine1 House1) 'CxNaturalWorld))
    (is (v/ask? kb '(locatedIn Piston1 House1) 'CxNaturalWorld))))

(tu/deftest-kb owning-a-whole-entails-owning-its-parts
  ;; (implies (and (owns ?p ?whole) (partOf ?part ?whole)) (owns ?p ?part)) joins on ?whole.
  (testing "the parts of an owned whole are owned — when the facts share a context"
    (is (seq (v/sentexes-matching kb '(owns Tom Roof1) 'CxSocialWorld)))
    (is (seq (v/sentexes-matching kb '(owns Tom Chimney1) 'CxSocialWorld))))
  (testing "but a cross-context binding yields no conclusion — placement needs a common view"
    ;; owns Tom Car1 (CxSocialWorld) joins partOf Engine1 Car1 (CxNaturalWorld); the two
    ;; sibling contexts share no view, so the conclusion has nowhere to be placed.
    (is (empty? (v/sentexes-matching kb '(owns Tom Engine1) 'CxSocialWorld)))
    (is (empty? (v/sentexes-matching kb '(owns Tom Engine1) 'CxNaturalWorld)))))

(tu/deftest-kb joined-antecedents-infer-a-part-type
  ;; partOf now carries argIsa (partOf 2 physical_object), so an untyped part is
  ;; inferred to be a physical_object from how it is used.
  (testing "Roof1 is never typed, but its physical_object-hood is inferable"
    (is (empty? (v/sentexes-matching kb '(physical_object Roof1) '?ctx)))
    (is (v/ask? kb '(physical_object Roof1)))))

;; ---- the stories --------------------------------------------------------

(tu/deftest-kb story-characters-get-their-ontology-types
  (testing "characters slot into the shared type hierarchy"
    (is (v/isa? kb 'LionA 'mammal))
    (is (v/isa? kb 'MouseA 'animal))
    (is (v/isa? kb 'TortoiseA 'reptile))
    (is (v/isa? kb 'AntA 'insect))
    (is (v/isa? kb 'BoyA 'human))
    (is (v/isa? kb 'BoyA 'person))
    (is (v/isa? kb 'BoyA 'mammal))
    (is (v/isa? kb 'BoyA 'liar))
    (is (v/isa? kb 'WolfA 'mammal))))

(tu/deftest-kb lion-and-mouse-derives-a-repaid-kindness
  ;; (spared LionA MouseA) + (freed MouseA LionA) ⇒ (repaidKindness MouseA LionA),
  ;; a rule joined on BOTH actors.
  (testing "the mouse repays the lion's mercy"
    (is (seq (v/sentexes-matching kb '(repaidKindness MouseA LionA) 'CxLionMouse))))
  (testing "not the other way around — the join is directional"
    (is (empty? (v/sentexes-matching kb '(repaidKindness LionA MouseA) 'CxLionMouse)))))

(tu/deftest-kb tortoise-and-hare-derives-the-winner
  ;; a three-antecedent join: raced + persevered(slow) + napped(fast) ⇒ wins(slow,fast).
  (testing "the steady tortoise wins"
    (is (seq (v/sentexes-matching kb '(wins TortoiseA HareA) 'CxTortoiseHare))))
  (testing "the hare does not win"
    (is (empty? (v/sentexes-matching kb '(wins HareA TortoiseA) 'CxTortoiseHare)))))

(tu/deftest-kb ant-and-grasshopper-derives-preparation-pays
  ;; derived facts feed a further join: survivesWinter(ant) + suffersInWinter(hopper)
  ;; ⇒ betterPreparedThan(ant, hopper).
  (testing "the intermediate conclusions are derived"
    (is (seq (v/sentexes-matching kb '(survivesWinter AntA) 'CxAntGrasshopper)))
    (is (seq (v/sentexes-matching kb '(suffersInWinter GrasshopperA) 'CxAntGrasshopper))))
  (testing "and the moral joins them"
    (is (seq (v/sentexes-matching kb '(betterPreparedThan AntA GrasshopperA) 'CxAntGrasshopper)))))

(tu/deftest-kb boy-who-cried-wolf-is-non-monotonic
  ;; belief in a cry is a default that carries its own exception: the rule is
  ;; `(exceptWhen (liar ?x) (set/defaultRule (implies (criesWolf ?x) (believed ?x))))`.
  ;; So for a liar the rule concludes *nothing* — this is undercutting, not
  ;; rebutting, and there is no competing conclusion to arbitrate.
  (testing "the liar's cry is not believed"
    (is (empty? (v/sentexes-matching kb '(believed BoyA) 'CxCriedWolf)))
    (is (seq   (v/sentexes-matching kb '(not (believed BoyA)) 'CxCriedWolf))))
  (testing "the blocked conclusion is never stored — swept, not kept defeated"
    ;; The pre-`exceptWhen` engine derived (believed BoyA), rebutted it with the
    ;; competing rule, and left it stored-but-OUT so it could revive.  A blocked
    ;; justification is simply invalid, so the conclusion is unsupported and the
    ;; existing dependency-directed sweep deletes it (docs/exceptions.md,
    ;; "Garbage collection, not defeat").
    (is (nil? (v/handle-of kb '(believed BoyA) 'CxCriedWolf)))
    (is (empty? (filter #(= '(believed BoyA) (:sentence %))
                        (v/find-sentexes kb 'BoyA)))))
  (testing "yet the absence is explicable, not merely a gap"
    ;; the moral is only demonstrated if the KB can say *why* the boy is not
    ;; believed, and a swept conclusion has no handle to ask about — which is what
    ;; `why-not`'s sentence arity is for.
    (let [wn (v/why-not kb '(believed BoyA) 'CxCriedWolf)]
      (is (= :excepted (:reason wn)))
      (is (= '(liar BoyA) (:exception wn)))))
  (testing "blocking yields nothing to arbitrate — no conflict and no dilemma"
    (is (empty? (v/conflicts kb)))
    (is (empty? (v/contradictions kb))))
  (testing "yet the danger is real: a joined rule with a constant character derives it"
    ;; (approaches WolfA ?victim) + (criesWolf ?victim) ⇒ (inDanger ?victim)
    (is (seq (v/sentexes-matching kb '(inDanger BoyA) 'CxCriedWolf)))
    (is (empty? (v/sentexes-matching kb '(inDanger WolfA) 'CxCriedWolf)))))   ; the constant binds only the victim

(tu/deftest-kb middle-theories-reach-story-characters-but-siblings-stay-isolated
  ;; In the layered spindle a *middle* theory (biology) is seen by every CxWell
  ;; descendant, so it DOES reach story characters — the mortal default lands on the
  ;; lion, placed back in its own leaf.  What stays isolated is a join across sibling
  ;; data contexts (owns/partOf, tested above) and a rule whose type does not match.
  (testing "a middle biology theory reaches a story animal, in that animal's leaf"
    (is (seq (v/sentexes-matching kb '(mortal LionA) 'CxLionMouse))))
  (testing "but a default whose antecedent type does not hold never fires — neither a
            wolf nor a hare is a bird, so the flight default does not touch them"
    (is (empty? (v/sentexes-matching kb '(flies WolfA) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(flies HareA) '?ctx)))))

(tu/deftest-kb story-vocabulary-is-classified-in-the-meta-ontology
  (testing "the new animal types are unary predicates, like every type"
    (doseq [t '[lion mouse hare wolf tortoise ant grasshopper]]
      (is (v/isa? kb t 'unaryPredicate) (str "type " t))))
  (testing "the narrative predicates carry their arity, upholding self-classification"
    (is (v/isa? kb 'spared 'binaryPredicate))
    (is (v/isa? kb 'repaidKindness 'binaryPredicate))
    (is (v/isa? kb 'inDanger 'unaryPredicate))
    (is (v/isa? kb 'criesWolf 'unaryPredicate))))

(tu/deftest-kb every-story-documents-its-moral
  (testing "each story context carries a moral comment"
    (doseq [cx '[CxLionMouse CxTortoiseHare CxAntGrasshopper CxCriedWolf CxFoxCrow]]
      (is (= 1 (count (core-context/comment-of kb cx))) (str "moral for " cx))
      (is (re-find #"moral" (first (core-context/comment-of kb cx))) (str "moral for " cx)))))

;; ---- the story-understanding ontology (vaelii.world-narrative) ---------------

(tu/deftest-kb goal-reasoning-derives-that-an-agent-achieves-its-goal
  (testing "the fox wants the cheese, brings about getting it, and so achieves its goal"
    (is (seq (v/sentexes-matching kb '(achievesGoal FoxF HasCheese) 'CxFoxCrow))))
  (testing "the same schema retrofitted reads the tortoise's win as a goal achieved"
    (is (seq (v/sentexes-matching kb '(achievesGoal TortoiseA WinRace) 'CxTortoiseHare))))
  (testing "the conclusion is isolated to its story leaf, not visible elsewhere"
    (is (empty? (v/sentexes-matching kb '(achievesGoal FoxF HasCheese) 'CxTortoiseHare)))
    (is (empty? (v/sentexes-matching kb '(achievesGoal FoxF HasCheese) 'CxUniverse))))
  (testing "no goal is derived for an agent that wants nothing"
    (is (not (v/ask? kb '(achievesGoal CrowF HasCheese) 'CxFoxCrow))))
  (testing "an agent is responsible for what its action directly causes"
    (is (seq (v/sentexes-matching kb '(responsibleFor FoxF CrowSings) 'CxFoxCrow)))))

(tu/deftest-kb causal-chains-compose-transitively
  (testing "the flattery ultimately causes the fox to get the cheese"
    (is (v/ask? kb '(causes Flatter1 FoxGetsCheese))))
  (testing "causation is directional — the effect does not cause its cause"
    (is (not (v/ask? kb '(causes FoxGetsCheese Flatter1))))))

(tu/deftest-kb temporal-order-composes-and-inverts
  (testing "beforeEvent is transitive across the chain, and directional"
    (is (v/ask? kb '(beforeEvent Flatter1 FoxGetsCheese)))
    (is (not (v/ask? kb '(beforeEvent FoxGetsCheese Flatter1)))))
  (testing "afterEvent inverts a direct beforeEvent link"
    (is (v/ask? kb '(afterEvent CrowSings Flatter1))))
  (testing "and a transitively-derived one — the inverse delegates through the
            engine, so it composes with beforeEvent's transitivity rather than
            answering direct links only"
    (is (v/ask? kb '(afterEvent FoxGetsCheese Flatter1)))))

(tu/deftest-kb a-role-is-inferred-from-a-schema-position-via-argIsa
  (testing "CheeseFalls is never typed, yet its eventhood is inferred from causes' argIsa"
    (is (empty? (v/sentexes-matching kb '(event CheeseFalls) '?ctx)))   ; not stored
    (is (v/ask? kb '(event CheeseFalls))))                  ; but inferred
  (testing "explicit types still compose through genl (an action is an event)"
    (is (v/isa? kb 'Flatter1 'event))                       ; action < event
    (is (v/isa? kb 'FoxF 'agent)))
  (testing "the narrative relations are self-classified"
    (is (v/isa? kb 'causes 'transitivePredicate))
    (is (v/isa? kb 'achievesGoal 'binaryPredicate))
    (is (v/isa? kb 'responsibleFor 'binaryPredicate))))
