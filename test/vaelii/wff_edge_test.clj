;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wff-edge-test
  "The well-formedness checkers that had no tests, and the error *contract*.

  The wff dispatch (the `:wff` column of `vaelii.impl.special`'s table, walked by
  `special/wff-problems`) routes each special predicate to its checker.  `genl` and
  `arg` are covered; `genlCx`'s cycle branch, `disjoint_metatype`, the six
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
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- genlCx: the cycle branch --------------------------------------

(tu/deftest-kb genlCx-rejects-a-context-seeing-itself
  (tu/with-terms [CxAlpha]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'genlCx CxAlpha CxAlpha) 'CxUniverse)))
        "a context that genlCxs itself")))

(tu/deftest-kb genlCx-rejects-a-cycle-through-another-context
  ;; Like `genl`, a context cycle is refused at assert: `genlCx-problems` reads the
  ;; global `genlCx` closure and refuses an edge whose super already sees its sub, so
  ;; the context hierarchy is a partial order.  The one-way edges below are admitted;
  ;; the edge that would close the loop is not, and nothing it would have changed does.
  ;; See the note atop `wff`.
  (tu/with-terms [CxAlpha CxBeta]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBeta CxAlpha) 'CxUniverse)
    (is (v/sees? kb CxBeta CxAlpha))
    (is (not (v/sees? kb CxAlpha CxBeta)) "one-way before any loop")
    (testing "the edge that would close the loop is refused, with the cycle error type"
      (is (= :not-well-formed
             (ex-type #(v/assert kb (list 'genlCx CxAlpha CxBeta) 'CxUniverse)))))
    (testing "and the refused edge changed nothing: the one-way answer stands"
      (is (not (v/sees? kb CxAlpha CxBeta)))
      (is (v/sees? kb CxBeta CxAlpha))
      (is (v/sees? kb CxAlpha 'CxUniverse))
      (is (v/sees? kb CxBeta 'CxUniverse))
      (is (contains? (v/context-up kb CxBeta) CxAlpha))
      (is (not (contains? (v/context-up kb CxAlpha) CxBeta))))))

(tu/deftest-kb genlCx-rejects-a-non-context-argument
  (tu/with-terms [CxAlpha]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'genlCx CxAlpha 'PlainIndividual) 'CxUniverse))))))

;; ---- the checkers with no tests at all ----------------------------------

(tu/deftest-kb disjoint_metatype-must-mark-a-metatype-not-an-individual
  (tu/with-terms [Muffet animal_species]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'disjoint_metatype Muffet) 'CxUniverse)))
        "an individual is not a metatype")
    (testing "and it takes exactly one argument"
      ;; :naming — disjoint_metatype is snake_case, so a second argument is refused at
      ;; the naming check, upstream of the `wff` arity check
      (is (= :naming
             (ex-type #(v/assert kb (list 'disjoint_metatype animal_species 'Extra) 'CxUniverse)))))))

(tu/deftest-kb the-predicate-properties-reject-an-individual-argument
  ;; All six route through `prop-problems`.  A predicate dropped from that `case`
  ;; list would fall through to `[]` and accept anything — this is what notices.
  (tu/with-terms [Muffet]
    (doseq [prop '[transitive symmetric reflexive functional
                   decontextualized_predicate forced_decontextualized_predicate]]
      (is (= :not-well-formed (ex-type #(v/assert kb (list prop Muffet) 'CxUniverse)))
          (str prop " must reject an individual")))))

(tu/deftest-kb the-predicate-properties-take-exactly-one-argument
  ;; Which entry point refuses it is the spelling's to say.  A snake_case property is a unary
  ;; predicate by its name, so a second argument is a NAMING violation and never reaches
  ;; `prop-problems`; a bare lowercase one claims no arity and is caught by `wff`.
  (tu/with-terms [tangiblePartOf otherPred]
    (doseq [prop '[transitive symmetric reflexive functional
                   decontextualized_predicate forced_decontextualized_predicate]]
      (is (= (if (str/includes? (name prop) "_") :naming :not-well-formed)
             (ex-type #(v/assert kb (list prop tangiblePartOf otherPred) 'CxUniverse)))
          (str prop " takes one argument")))))

(tu/deftest-kb inverse-relates-two-predicates
  (tu/with-terms [parentOf childOf Muffet]
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'inverse Muffet childOf) 'CxUniverse)))
        "an individual in argument 1")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'inverse parentOf Muffet) 'CxUniverse)))
        "an individual in argument 2")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'inverse parentOf) 'CxUniverse)))
        "and it takes two")))

(tu/deftest-kb arg-checks-the-shape-of-all-three-arguments
  (tu/with-terms [parentOf person Muffet]
    (is (nil? (ex-type #(v/assert kb (list 'arg Muffet 1 person) 'CxUniverse)))
        "argument 1 is not held to a spelling: a function has argument positions like a
         predicate does and is spelled like an individual, so no spelling test separates
         the two — and a constraint on a term that never heads a sentence is inert")
    (is (nil? (ex-type #(v/assert kb (list 'arg (list 'RoleFn parentOf) 1 person)
                                  'CxUniverse)))
        "a relation may be denoted by a NAT rather than named, and that is a term too")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'arg 7 1 person) 'CxUniverse)))
        "but a number is no kind of term for a relation to be")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'arg parentOf 0 person) 'CxUniverse)))
        "the position is 1-based, so 0 is out of range")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'arg parentOf 'one person) 'CxUniverse)))
        "and it must be an integer")
    (is (= :not-well-formed
           (ex-type #(v/assert kb (list 'arg parentOf 1 Muffet) 'CxUniverse)))
        "argument 3 must be a type, not an individual")
    (testing "a well-formed arg is accepted"
      (is (nil? (ex-type #(v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)))))))

;; ---- the ex-info :type contract ----------------------------------------

(tu/deftest-kb a-naming-violation-is-typed-naming
  (tu/with-terms [dog Muffet]
    (is (= :naming (ex-type #(v/assert kb (list dog Muffet) 'SomewhereElse)))
        "a context that does not start with Cx")))

(tu/deftest-kb a-non-ground-fact-is-typed-not-ground
  (tu/with-terms [mortal]
    (is (= :not-ground (ex-type #(v/assert kb (list mortal '?x) 'CxUniverse))))))

(tu/deftest-kb a-disjointness-clash-is-a-disjoint-nogood
  ;; Everything in one context, like the arg test below: the constraint checks
  ;; are context-scoped — disjointness included — and this KB is fresh, so a
  ;; declaration in an unwired CxUniverse would simply be invisible here.
  (tu/with-terms [dog cat Felix]
    (v/assert kb (list 'disjoint dog cat) 'CxNaturalWorld)
    (v/assert kb (list cat Felix) 'CxNaturalWorld)
    (v/assert kb (list dog Felix) 'CxNaturalWorld)
    (is (= [:disjoint] (mapv :kind (v/contradictions kb))))))

(tu/deftest-kb an-arg-violation-is-typed-arg-type
  ;; the constraint-only reading: the refusal is the subject
  (tu/without-entailing
   ;; Everything in one context on purpose: the constraint checks are context-scoped,
   ;; and this KB is fresh, so `CxNaturalWorld` has no genlCx edge to
   ;; CxUniverse and a constraint declared there would simply be invisible.
   (tu/with-terms [parentOf person rock Muffet Boulder]
     ;; `checks/args-problem` is open-world: it only bites when the argument is provably a
     ;; `thing`, so an untyped individual can never violate a constraint.  The genl
     ;; edge is what makes Boulder checkable at all.
     (v/assert kb (list 'genl rock 'thing) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     (v/assert kb (list rock Boulder) 'CxUniverse)
     (is (= :arg-type
            (ex-type #(v/assert kb (list parentOf Boulder Muffet) 'CxUniverse)))
         "Boulder is a rock, and rock does not reach person through genl"))))

;; The values are **numbers**, and that is the point rather than an incidental
;; choice.  A functional clash between two *symbols* is not an error (docs/equality.md):
;; two spellings may denote one thing, so the KB derives `(equals V1 V2)` and merges
;; them instead of weighing the second fact.  A clash the equality closure cannot
;; express is a nogood, and numbers are exactly that case: the closure is a
;; partition over symbols, and no merge can make 1980 and 1990 one thing.
;; `equality_test` owns the other half.
(tu/deftest-kb a-functional-clash-is-a-functional-nogood
  (tu/with-terms [birthYearOf Ann]
    (v/assert kb (list 'functional birthYearOf) 'CxNaturalWorld)
    (v/assert kb (list birthYearOf Ann 1980) 'CxNaturalWorld)
    (v/assert kb (list birthYearOf Ann 1990) 'CxNaturalWorld)
    (is (= [:functional] (mapv :kind (v/contradictions kb)))
        "a second, different value for the same first argument")))

(tu/deftest-kb a-malformed-special-predicate-is-typed-not-well-formed
  (tu/with-terms [dog Muffet]
    (is (= :not-well-formed (ex-type #(v/assert kb (list 'genl dog Muffet) 'CxUniverse)))
        "genl relates types, and Muffet is an individual")))

(tu/deftest-kb the-error-payload-carries-more-than-the-type
  ;; the constraint-only reading: the refusal is the subject
  (tu/without-entailing
   ;; The diagnostic keys are the whole value of ex-info over a bare throw; a caller
   ;; that reports "argument 2 of parentOf should be a person" needs them.
   (tu/with-terms [parentOf person rock Muffet Boulder]
     (v/assert kb (list 'genl rock 'thing) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 2 person) 'CxUniverse)
     (v/assert kb (list rock Boulder) 'CxUniverse)
     (try
       (v/assert kb (list parentOf Muffet Boulder) 'CxUniverse)
       (is false "expected the arg constraint to reject this")
       (catch clojure.lang.ExceptionInfo e
         (let [d (ex-data e)]
           (is (= :arg-type (:type d)))
           (is (= (list parentOf Muffet Boulder) (:sentence d)))
           (is (seq (dissoc d :type :sentence))
               "the payload names what was expected where, not just that it failed")))))))

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
