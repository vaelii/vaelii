;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wff-edge-test
  "The well-formedness checkers that had no tests, and the error *contract*.

  The wff dispatch (the `:wff` column of `vaelii.impl.special`'s table, walked by
  `special/wff-problems`) routes each special predicate to its checker.  `genl` and
  `argIsa` are covered; `genlContext`'s cycle branch, `disjointMetatype`, the six
  predicate properties routed through `prop-problems`, and `inverse` are not — so a
  predicate whose entry loses its `:wff` arm falls through to `[]` and is accepted
  unchecked, with nothing to notice.

  The second half is about how a refusal is *reported*.  The contract is
  that every `ex-info` `assert` throws carries a `:type` — `:naming`
  `:not-well-formed` `:not-ground` `:arg-type` `:disjoint` `:functional` — so a
  caller can discriminate without guessing from which keys happen to be present.
  Six of those eight were asserted nowhere: every test used a bare
  `(thrown? ExceptionInfo ...)`, which passes just as happily when the check
  regresses into throwing for a *different* reason.  `stratification_test` names
  that risk in its own docstring; this holds the rest of the error paths to the same
  bar."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- genlContext: the cycle branch --------------------------------------

(tu/deftest-kb genlContext-rejects-a-context-seeing-itself
  (tu/with-terms [AlphaContext]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'genlContext AlphaContext AlphaContext) 'UniverseContext)))
        "a context that genlContexts itself")))

(tu/deftest-kb genlContext-admits-a-cycle-through-another-context
  ;; Unlike `genl`, a context cycle is a claim rather than a contradiction: it says the
  ;; two contexts see each other, which is what OpenCyc's `genlMt` states of
  ;; BaseKB and UniversalVocabularyMt.  Visibility is reachability, and reachability
  ;; over a cycle is perfectly well defined — see the note atop `wff`.
  (tu/with-terms [AlphaContext BetaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext BetaContext AlphaContext) 'UniverseContext)
    (is (v/sees? kb BetaContext AlphaContext))
    (is (not (v/sees? kb AlphaContext BetaContext)) "before the loop is closed")
    (testing "closing the loop is admitted, and both directions then hold"
      (v/assert kb (list 'genlContext AlphaContext BetaContext) 'UniverseContext)
      (is (v/sees? kb AlphaContext BetaContext))
      (is (v/sees? kb BetaContext AlphaContext)))
    (testing "and each still sees what the other saw"
      (is (v/sees? kb AlphaContext 'UniverseContext))
      (is (v/sees? kb BetaContext 'UniverseContext))
      (is (contains? (v/context-up kb BetaContext) AlphaContext))
      (is (contains? (v/context-up kb AlphaContext) BetaContext))
      (is (contains? (v/context-down kb AlphaContext) BetaContext)))
    (testing "and retracting the back edge restores the one-way answer"
      (v/retract! kb (v/handle-of kb (list 'genlContext AlphaContext BetaContext)
                                  'UniverseContext))
      (is (not (v/sees? kb AlphaContext BetaContext)))
      (is (v/sees? kb BetaContext AlphaContext)))))

(tu/deftest-kb genlContext-rejects-a-non-context-argument
  (tu/with-terms [AlphaContext]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'genlContext AlphaContext 'PlainIndividual) 'UniverseContext))))))

;; ---- the checkers with no tests at all ----------------------------------

(tu/deftest-kb disjointMetatype-must-mark-a-metatype-not-an-individual
  (tu/with-terms [Muffet animalSpecies]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'disjointMetatype Muffet) 'UniverseContext)))
        "an individual is not a metatype")
    (testing "and it takes exactly one argument"
      (is (= :not-well-formed
             (ex-type #(v/assert kb (list 'disjointMetatype animalSpecies 'Extra) 'UniverseContext)))))))

(tu/deftest-kb the-predicate-properties-reject-an-individual-argument
  ;; All six route through `prop-problems`.  A predicate dropped from that `case`
  ;; list would fall through to `[]` and accept anything — this is what notices.
  (tu/with-terms [Muffet]
    (doseq [prop '[transitive symmetric reflexive functional
                   decontextualizedPredicate forcedDecontextualizedPredicate]]
      (is (= :not-well-formed (ex-type #(v/assert kb (list prop Muffet) 'UniverseContext)))
          (str prop " must reject an individual")))))

(tu/deftest-kb the-predicate-properties-take-exactly-one-argument
  (tu/with-terms [partOf otherPred]
    (doseq [prop '[transitive symmetric reflexive functional
                   decontextualizedPredicate forcedDecontextualizedPredicate]]
      (is (= :not-well-formed
             (ex-type #(v/assert kb (list prop partOf otherPred) 'UniverseContext)))
          (str prop " takes one argument")))))

(tu/deftest-kb inverse-relates-two-predicates
  (tu/with-terms [parentOf childOf Muffet]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'inverse Muffet childOf) 'UniverseContext)))
        "an individual in argument 1")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'inverse parentOf Muffet) 'UniverseContext)))
        "an individual in argument 2")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'inverse parentOf) 'UniverseContext)))
        "and it takes two")))

(tu/deftest-kb argIsa-checks-the-shape-of-all-three-arguments
  (tu/with-terms [parentOf person Muffet]
    (is (nil? (ex-type #(v/assert kb (list 'argIsa Muffet 1 person) 'UniverseContext)))
        "argument 1 is not held to a spelling: a function has argument positions like a
         predicate does and is spelled like an individual, so no spelling test separates
         the two — and a constraint on a term that never heads a sentence is inert")
    (is (nil? (ex-type #(v/assert kb (list 'argIsa (list 'RoleFn parentOf) 1 person)
                                  'UniverseContext)))
        "a relation may be denoted by a NAT rather than named, and that is a term too")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'argIsa 7 1 person) 'UniverseContext)))
        "but a number is no kind of term for a relation to be")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'argIsa parentOf 0 person) 'UniverseContext)))
        "the position is 1-based, so 0 is out of range")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'argIsa parentOf 'one person) 'UniverseContext)))
        "and it must be an integer")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'argIsa parentOf 1 Muffet) 'UniverseContext)))
        "argument 3 must be a type, not an individual")
    (testing "a well-formed argIsa is accepted"
      (is (nil? (ex-type #(v/assert kb (list 'argIsa parentOf 1 person) 'UniverseContext)))))))

;; ---- the ex-info :type contract ----------------------------------------

(tu/deftest-kb a-naming-violation-is-typed-naming
  (tu/with-terms [dog Muffet]
    (is (= :naming (ex-type #(v/assert kb (list dog Muffet) 'SomewhereElse)))
        "a context that does not end in Context")))

(tu/deftest-kb a-non-ground-fact-is-typed-not-ground
  (tu/with-terms [mortal]
    (is (= :not-ground (ex-type #(v/assert kb (list mortal '?x) 'UniverseContext))))))

(tu/deftest-kb a-disjointness-violation-is-typed-disjoint
  ;; Everything in one context, like the argIsa test below: the constraint checks
  ;; are context-scoped — disjointness included — and this KB is fresh, so a
  ;; declaration in an unwired UniverseContext would simply be invisible here.
  (tu/with-terms [dog cat Felix]
    (v/assert kb (list 'disjoint dog cat) 'NaturalWorldContext)
    (v/assert kb (list cat Felix) 'NaturalWorldContext)
    (is (= :disjoint (ex-type #(v/assert kb (list dog Felix) 'NaturalWorldContext))))))

(tu/deftest-kb an-argIsa-violation-is-typed-arg-type
  ;; Everything in one context on purpose: the constraint checks are context-scoped,
  ;; and this KB is fresh, so `NaturalWorldContext` has no genlContext edge to
  ;; UniverseContext and a constraint declared there would simply be invisible.
  (tu/with-terms [parentOf person rock Muffet Boulder]
    ;; `checks/args-problem` is open-world: it only bites when the argument is provably a
    ;; `thing`, so an untyped individual can never violate a constraint.  The genl
    ;; edge is what makes Boulder checkable at all.
    (v/assert kb (list 'genl rock 'thing) 'UniverseContext)
    (v/assert kb (list 'argIsa parentOf 1 person) 'UniverseContext)
    (v/assert kb (list rock Boulder) 'UniverseContext)
    (is (= :arg-type
           (ex-type #(v/assert kb (list parentOf Boulder Muffet) 'UniverseContext)))
        "Boulder is a rock, and rock does not reach person through genl")))

;; The values are **numbers**, and that is the point rather than an incidental
;; choice.  A functional clash between two *symbols* is not an error (docs/equality.md):
;; two spellings may denote one thing, so the KB derives `(equals V1 V2)` and merges
;; them instead of refusing the second fact.  A clash the equality closure cannot
;; express is a hard rejection, and numbers are exactly that case: the closure is a
;; partition over symbols, and no merge can make 1980 and 1990 one thing.
;; `equality_test` owns the other half.
(tu/deftest-kb a-functional-violation-is-typed-functional
  (tu/with-terms [birthYearOf Ann]
    (v/assert kb (list 'functional birthYearOf) 'NaturalWorldContext)
    (v/assert kb (list birthYearOf Ann 1980) 'NaturalWorldContext)
    (is (= :functional
           (ex-type #(v/assert kb (list birthYearOf Ann 1990) 'NaturalWorldContext)))
        "a second, different value for the same first argument")))

(tu/deftest-kb a-malformed-special-predicate-is-typed-not-well-formed
  (tu/with-terms [dog Muffet]
    (is (= :not-well-formed (ex-type #(v/assert kb (list 'genl dog Muffet) 'UniverseContext)))
        "genl relates types, and Muffet is an individual")))

(tu/deftest-kb the-error-payload-carries-more-than-the-type
  ;; The diagnostic keys are the whole value of ex-info over a bare throw; a caller
  ;; that reports "argument 2 of parentOf should be a person" needs them.
  (tu/with-terms [parentOf person rock Muffet Boulder]
    (v/assert kb (list 'genl rock 'thing) 'UniverseContext)
    (v/assert kb (list 'argIsa parentOf 2 person) 'UniverseContext)
    (v/assert kb (list rock Boulder) 'UniverseContext)
    (try
      (v/assert kb (list parentOf Muffet Boulder) 'UniverseContext)
      (is false "expected the argIsa constraint to reject this")
      (catch clojure.lang.ExceptionInfo e
        (let [d (ex-data e)]
          (is (= :arg-type (:type d)))
          (is (= (list parentOf Muffet Boulder) (:sentence d)))
          (is (seq (dissoc d :type :sentence))
              "the payload names what was expected where, not just that it failed"))))))

;; ---- a refused rule writes nothing -------------------------------------

(tu/deftest-kb a-rule-refused-for-naming-leaves-no-trace
  ;; The rule path checks before it stores.  This is the rule-shaped twin of the
  ;; conjunct test in assert_soundness_test.
  (tu/with-terms [bird flies]
    (let [before (tu/sentex-ids kb)]
      (is (= :naming
             (ex-type #(v/assert kb (vr/rule-sentence [(list bird '?x)] (list flies '?x))
                                 'SomewhereElse))))
      (is (= before (tu/sentex-ids kb)) "a refused rule stores nothing"))))
