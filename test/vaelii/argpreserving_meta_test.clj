;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argpreserving-meta-test
  "The argument-type meta-predicates answer along the `genl` closure on the query
  surface, so `ask` agrees with the generalization `check` already walks internally.
  Before this, a stored `(argIsa petMammal 1 mammal)` was the only thing
  `(ask (argIsa petMammal 1 animal))` could return — nothing — even though
  `(genl mammal animal)` holds and `check` would accept an animal there, closing #20.

  The engine answers it in `provers/MetaConstraintProver`, a bounded closure walk, and
  NOT by declaring the meta-predicates `transitiveInArg` — that would tax every one of
  the KB's very many `argIsa`/`argGenl` lookups (see `resources/kb/CxCore.txt`).  The
  predicate position (1) reaches DOWN `genl` (a constraint on a super binds its
  specializations); an unconditional type reaches UP (a stored subtype answers its
  supertypes — `argIsa`/`argGenl` position 3, `interArgIsa`'s target position 5); and
  `interArgIsa`'s trigger position 3, being an antecedent, is contravariant and reaches
  DOWN.

  The KB here is CxCore alone, so what these tests read is the *shipped* vocabulary
  and not one they stated."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(def ^:private C 'CxCore)

;; ---- argIsa, both directions --------------------------------------------

(tu/deftest-kb argIsa-answers-up-the-genl-chain-via-transitiveInArgInverse
  ;; position 3 is a TYPE: a stored constraint on mammal answers up to animal
  (tu/with-terms [petMammal mammal animal dog]
    (v/assert kb (list 'genl animal 'thing) C)
    (v/assert kb (list 'genl mammal animal) C)
    (v/assert kb (list 'genl dog mammal) C)
    (v/assert kb (list 'argIsa petMammal 1 mammal) C)
    (testing "the literally stored declaration is answerable, and it is stored"
      (is (v/ask? kb (list 'argIsa petMammal 1 mammal) C))
      (is (seq (v/sentexes-matching kb (list 'argIsa petMammal 1 mammal) '?ctx))))
    (testing "the supertype answers even though nobody stored it — the gap #20 names"
      (is (v/ask? kb (list 'argIsa petMammal 1 animal) C))
      (is (empty? (v/sentexes-matching kb (list 'argIsa petMammal 1 animal) '?ctx))
          "answered on demand, never materialized"))
    (testing "and the default context read (unscoped) finds it too"
      (is (v/ask? kb (list 'argIsa petMammal 1 animal))))
    (testing "but the constraint does not descend at position 3 — inverse is up only"
      (is (not (v/ask? kb (list 'argIsa petMammal 1 dog) C))))))

(tu/deftest-kb argIsa-inherits-down-the-predicate-via-transitiveInArg
  ;; position 1 is the PREDICATE: a constraint on a general predicate reaches its
  ;; genl-specializations, and not the other way
  (tu/with-terms [mySuper mySub myOver myType]
    (v/assert kb (list 'genl myType 'thing) C)
    (v/assert kb (list 'genl mySub mySuper) C)
    (v/assert kb (list 'genl mySuper myOver) C)
    (v/assert kb (list 'argIsa mySuper 1 myType) C)
    (testing "a specialization of the constrained predicate inherits the constraint"
      (is (v/ask? kb (list 'argIsa mySub 1 myType) C))
      (is (empty? (v/sentexes-matching kb (list 'argIsa mySub 1 myType) '?ctx))))
    (testing "but a generalization does not — transitiveInArg reaches down, not up"
      (is (not (v/ask? kb (list 'argIsa myOver 1 myType) C))))))

;; ---- argGenl, interArgIsa, arity: the same shape, smoke-tested ----------

(tu/deftest-kb argGenl-answers-up-the-genl-chain-at-position-3
  (tu/with-terms [typeRel mammal animal]
    (v/assert kb (list 'genl animal 'thing) C)
    (v/assert kb (list 'genl mammal animal) C)
    (v/assert kb (list 'argGenl typeRel 1 mammal) C)
    (testing "the stored subtype constraint answers up to the supertype"
      (is (v/ask? kb (list 'argGenl typeRel 1 animal) C))
      (is (empty? (v/sentexes-matching kb (list 'argGenl typeRel 1 animal) '?ctx))))))

(tu/deftest-kb interArgIsa-trigger-narrows-down-target-widens-up
  ;; The conditional constraint's two types have OPPOSITE variance.  The trigger
  ;; (position 3) is the antecedent: `(interArgIsa myRel 1 carnivore 2 meat)` convicts
  ;; every carnivore, so it convicts every lion (a lion is a carnivore) and answers the
  ;; *subtype* trigger — but it says nothing about predators at large, so it does not
  ;; answer the *supertype* trigger.  The target (position 5) is the consequent, an
  ;; ordinary unconditional type: `meat` answers up to `food`.  Widening the trigger up
  ;; (the old, wrong direction) would convict the non-carnivore predators `check` never
  ;; touches — unsound; not answering the narrower lion trigger — incomplete.
  (tu/with-terms [myRel lion carnivore predator meat food]
    (v/assert kb (list 'genl predator 'thing) C)
    (v/assert kb (list 'genl carnivore predator) C)
    (v/assert kb (list 'genl lion carnivore) C)
    (v/assert kb (list 'genl food 'thing) C)
    (v/assert kb (list 'genl meat food) C)
    (v/assert kb (list 'interArgIsa myRel 1 carnivore 2 meat) C)
    (testing "the trigger narrows DOWN — a subtype trigger is answered"
      (is (v/ask? kb (list 'interArgIsa myRel 1 lion 2 meat) C)))
    (testing "the trigger does NOT widen up — a supertype trigger convicts non-carnivores"
      (is (not (v/ask? kb (list 'interArgIsa myRel 1 predator 2 meat) C))))
    (testing "the target widens UP its type"
      (is (v/ask? kb (list 'interArgIsa myRel 1 carnivore 2 food) C)))
    (testing "trigger narrowed and target widened together"
      (is (v/ask? kb (list 'interArgIsa myRel 1 lion 2 food) C)))
    (testing "nothing is materialized"
      (is (empty? (v/sentexes-matching kb (list 'interArgIsa myRel 1 lion 2 meat) '?ctx))))))

(tu/deftest-kb arity-does-not-generalize-down-the-predicate
  ;; arity is deliberately NOT among the generalized meta-predicates.  Unlike a type
  ;; constraint, a sub-predicate may carry a signature of its own — a ternary
  ;; specialization of a binary — so its arity is not answered down `genl` as a fact,
  ;; and answering it would in any case need the forward `(arity ?p 2) ⊢
  ;; (binaryPredicate ?p)` cycle a backward prover cannot fire.  `check`'s
  ;; `inherited-arity` still holds a sub-predicate that declares NOTHING of its own to
  ;; its supers at assert time — a refusal, not an answerable `(arity sub n)`.
  (tu/with-terms [mySuper mySub]
    (v/assert kb (list 'genl mySub mySuper) C)
    (v/assert kb (list 'arity mySuper 2) C)
    (testing "the specialization does not inherit the arity as an answerable fact"
      (is (not (v/ask? kb (list 'arity mySub 2) C))))
    (testing "so the derive cycle concludes no predicate type for it either"
      (is (not (v/ask? kb (list 'binaryPredicate mySub) C))))))
