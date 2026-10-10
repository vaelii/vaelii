;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.integer-sign-types-test
  "The four sign-refined integer types of CxCore — `positive_integer`,
  `negative_integer`, `non_negative_integer`, `non_positive_integer` — each a
  `defnSufficient` + `defnNecessary` pair over the computed `integer` / `greaterThan` /
  `lessThan`, so membership of a bare number is decided by evaluation at query time and
  stores nothing (docs/defns.md), and each usable as an argument type."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(def cases
  "Each type, its defining condition, a member and a non-member."
  [['positive_integer     '(and (integer ?x) (greaterThan ?x 0))  1  0]
   ['negative_integer     '(and (integer ?x) (lessThan ?x 0))    -1  0]
   ['non_negative_integer '(and (integer ?x) (greaterThan ?x -1)) 0 -1]
   ['non_positive_integer '(and (integer ?x) (lessThan ?x 1))     0  1]])

(def positive-position-slots
  "Every core argument slot whose value is a one-based position."
  [['genlArg 2]
   ['arg 2]
   ['quotedArg 2]
   ['interArg 2]
   ['interArg 4]
   ['contextArgSubrelation 2]
   ['transitiveInArgInverse 2]
   ['transitiveInArg 2]])

(tu/deftest-kb each-sign-refined-integer-is-a-defn-pair-under-integer
  (doseq [[type condition] cases
          :let [[_ & conjuncts] condition]]
    (testing (str type)
      (is (v/genl? kb type 'integer))
      (is (some? (v/handle-of kb (list 'defnSufficient type condition) 'CxCore)))
      (is (some? (v/handle-of kb (list 'defnNecessary type condition) 'CxCore)))
      (is (nil? (v/handle-of kb (list 'defnIff type condition) 'CxCore)))
      (doseq [conjunct conjuncts]
        (is (some? (v/handle-of kb (list 'implies (list type '?x) conjunct) 'CxCore))
            "membership entails every defining conjunct"))
      (is (= [:naf-not-closed]
             (map :type (v/check kb (list 'implies condition (list type '?x)) 'CxCore)))
          "no conjunct of the condition binds the member, so it expands to no rule"))))

(tu/deftest-kb integer-is-a-computed-kind-check
  (is (v/ask? kb (list 'integer 5) U))
  (is (v/ask? kb (list 'integer -212) U))
  (is (not (v/ask? kb (list 'integer 3.5) U)))
  (is (not (v/ask? kb (list 'integer "str") U)))
  (is (not (v/ask? kb (list 'integer 'foo) U))))

(tu/deftest-kb the-value-kind-of-a-literal-is-computed
  ;; A literal value's kind is its EDN kind, so EvaluableProver answers it the way it
  ;; answers integer, both ways.
  (testing "a literal is a member of its own value kind"
    (is (true? (v/ask? kb (list 'string "foo") U)))
    (is (true? (v/ask? kb (list 'number 7) U)))
    (is (true? (v/ask? kb (list 'number 3.5) U)))
    (is (true? (v/ask? kb (list 'keyword :a) U)))
    (is (true? (v/ask? kb (list 'boolean true) U)))
    (is (true? (v/ask? kb (list 'boolean false) U)))
    (is (true? (v/ask? kb (list 'character \c) U))))
  (testing "and provably not a member of another"
    (is (true? (v/ask? kb (list 'not (list 'number "foo")) U)))
    (is (true? (v/ask? kb (list 'not (list 'string 7)) U)))
    (is (not (v/ask? kb (list 'number "foo") U)))
    (is (not (v/ask? kb (list 'string 7) U))))
  (testing "a symbol is not answered: a constant could denote a number"
    (is (not (v/ask? kb (list 'number 'Muffet) U)) "not proven a number")
    (is (not (v/ask? kb (list 'not (list 'number 'Muffet)) U)) "and not refuted either")))

(tu/deftest-kb sign-types-admit-by-evaluation
  (doseq [[type _ member non-member] cases]
    (is (v/ask? kb (list type member) U) (str member " is a " type))
    (is (not (v/ask? kb (list type non-member) U)) (str non-member " is not a " type)))
  (is (v/ask? kb (list 'non_negative_integer 7) U))
  (is (v/ask? kb (list 'non_positive_integer -4) U))
  (is (not (v/ask? kb (list 'positive_integer -5) U))))

(tu/deftest-kb sign-types-disprove-via-a-failing-necessary
  (tu/with-terms [Fred]
    (doseq [[type _ member non-member] cases]
      (is (v/ask? kb (list 'not (list type non-member)) U) (str non-member " fails " type))
      (is (not (v/ask? kb (list 'not (list type member)) U))
          (str member " is a " type ", so its negation is not provable")))
    (testing "a string, a predicate symbol and an individual each fail (integer ?x)"
      (doseq [x ["str" 'unary_predicate Fred]]
        (is (v/ask? kb (list 'not (list 'positive_integer x)) U))
        (is (not (v/ask? kb (list 'positive_integer x) U)))))))

;; The sign types sit under `integer`, so they are inside `quotedArg`'s syntactic domain,
;; and the check compares a written value's own types (`checks/value-kinds`) against the
;; declared one.
(tu/deftest-kb sign-refined-integers-work-as-argument-types
  (doseq [slot ['arg 'quotedArg]
          [type _ member non-member] cases]
    (tu/with-terms [takesValue]
      (testing (str slot " " type)
        (v/assert kb (list 'unary_predicate takesValue) U)
        (v/assert kb (list slot takesValue 1 type) U)
        (is (integer? (v/assert kb (list takesValue member) U)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list takesValue non-member) U)))))))

(tu/deftest-kb core-integer-constraints-use-the-tightest-sign-type
  (doseq [[pred slot] positive-position-slots]
    (is (some? (v/handle-of kb (list 'arg pred slot 'positive_integer) 'CxCore))
        (str pred " argument " slot " is a one-based position")))
  (is (some? (v/handle-of kb '(arg arity 2 non_negative_integer) 'CxCore))
      "a predicate may have zero arguments, but never a negative arity"))

(tu/deftest-kb arity-is-non-negative-rather-than-positive
  (tu/with-terms [nullary impossible]
    (is (integer? (v/assert kb (list 'arity nullary 0) U)) "zero is a valid arity")
    (is (integer? (v/assert kb (list nullary) U))
        "a declared nullary predicate can be asserted")
    (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list 'arity impossible -1) U))
        "a negative arity is impossible")))

(tu/deftest-kb the-quoted-reading-still-refuses-across-kinds
  (tu/with-terms [needsString needsInteger]
    (v/assert kb (list 'unary_predicate needsString) U)
    (v/assert kb (list 'quotedArg needsString 1 'string) U)
    (is (integer? (v/assert kb (list needsString "Bob") U)) "a string satisfies string")
    (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list needsString 5) U))
        "5 is a number, not a string")
    (v/assert kb (list 'unary_predicate needsInteger) U)
    (v/assert kb (list 'quotedArg needsInteger 1 'integer) U)
    (is (integer? (v/assert kb (list needsInteger -7) U))
        "an unrefined integer position takes either sign")))

(tu/deftest-kb a-refused-sign-refinement-names-the-value-type
  (tu/with-terms [tagPositive]
    (v/assert kb (list 'unary_predicate tagPositive) U)
    (v/assert kb (list 'quotedArg tagPositive 1 'positive_integer) U)
    (let [m (try (v/assert kb (list tagPositive -5) U) nil
                 (catch clojure.lang.ExceptionInfo e (ex-message e)))]
      (is (some? m) "the assert is refused")
      (is (re-find #"negative_integer" (str m))
          (str "the message names the value's own type, not the bare EDN kind: " m)))))
