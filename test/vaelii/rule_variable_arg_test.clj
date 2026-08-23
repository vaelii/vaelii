;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rule-variable-arg-test
  "The argument constraints a rule's own variables carry, checked against each other.

  `args-problem` reads a ground argument, and every argument of a rule is a variable, so
  it passes over all of them vacuously.  Without the arm below, a rule whose binding
  chain feeds an impossible term into a position stores clean and is convicted later,
  one conclusion at a time, by a complaint naming the conclusion and never the rule.
  `checks/check-variable-constraints!` holds the positions a variable stands in to each
  other instead, and refuses `:arg-variable`.

  Two arms, and the second is the one that needs saying: a position is type-level when a
  `genlArg` names it **or** when its predicate is a `typeRelationPredicate`, which says
  it of every position at once.  That second half is what constrains `genl`'s second
  argument, the one position in CxCore's schema carrying no declaration of its own."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil when it does not throw.  Named
  rather than a bare `thrown?` for `arggenl_test`'s reason: an `:arg-variable` refusal
  collapsing into a naming or range-restriction one is exactly the regression a
  type-blind assertion stays green through."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- disjoint-pair
  "Two types the KB has been told share no instance, plus a third unrelated to both.
  Returns `[a b c]`."
  [kb]
  (let [a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type)]
    (doseq [t [a b c]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'disjoint a b) 'CxUniverse)
    [a b c]))

;; ---- two instance constraints on one variable ---------------------------

(tu/deftest-kb a-variable-two-arg-constraints-separate-is-refused
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 b) 'CxUniverse)
    (testing "the antecedent binds ?x an a, the consequent places it where a b belongs"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list q '?x)) 'CxUniverse)))))
    (testing "check predicts the refusal, and writes nothing"
      (let [ps (v/check kb (list 'implies (list p '?x) (list q '?x)) 'CxUniverse)]
        (is (= [:arg-variable] (mapv :type ps)))
        (is (= '?x (:variable (first ps))))
        (is (= #{a b} (set (:expected (first ps)))))))))

(tu/deftest-kb a-variable-two-compatible-arg-constraints-stands
  (let [[a _ c] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 c) 'CxUniverse)
    (testing "nothing separates the two types, so the rule is admissible"
      (is (= [] (v/check kb (list 'implies (list p '?x) (list q '?x)) 'CxUniverse)))
      (is (v/assert kb (list 'implies (list p '?x) (list q '?x)) 'CxUniverse)))))

(tu/deftest-kb the-clash-is-found-inside-one-literal-too
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred)]
    (v/assert kb (list 'arity q 2) 'CxUniverse)
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 2 b) 'CxUniverse)
    (testing "one variable in both positions of a literal is still one term"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list q '?x '?x))
                                 'CxUniverse)))))))

(tu/deftest-kb a-negated-antecedent-constrains-nothing
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred) r (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 b) 'CxUniverse)
    (v/assert kb (list 'arg r 1 a) 'CxUniverse)
    (testing "`(not (q ?x))` says ?x is not a b — which is what its author meant"
      (is (= [] (v/check kb (list 'implies (list 'and (list p '?x) (list 'not (list q '?x)))
                                  (list r '?x))
                         'CxUniverse)))
      (is (v/assert kb (list 'implies (list 'and (list p '?x) (list 'not (list q '?x)))
                             (list r '?x))
                    'CxUniverse)))))

(tu/deftest-kb the-constraint-descends-the-predicate-hierarchy
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred) sub (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 b) 'CxUniverse)
    (v/assert kb (list 'genl sub q) 'CxUniverse)
    (testing "a super-predicate's declaration binds the sub-predicate's tuples here too"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list sub '?x)) 'CxUniverse))))
      (is (re-find (re-pattern (str "declared of " q))
                   (:message (first (v/check kb (list 'implies (list p '?x) (list sub '?x))
                                             'CxUniverse))))))))

;; ---- the type-level half ------------------------------------------------

(tu/deftest-kb a-genlArg-position-asks-for-a-type
  (let [text (tu/tmp-type)
        p (tu/tmp-pred) rel (tu/tmp-pred)]
    (v/assert kb (list 'genl text 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint text 'unaryPredicate) 'CxUniverse)
    (v/assert kb (list 'arg p 1 text) 'CxUniverse)
    (v/assert kb (list 'typeRelationPredicate rel) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 'thing) 'CxUniverse)
    (testing "a variable bound to a text is not a kind, so it cannot fill a kind slot"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list rel '?x)) 'CxUniverse)))))))

(tu/deftest-kb a-typeRelationPredicate-constrains-a-position-no-declaration-names
  (let [text (tu/tmp-type)
        p (tu/tmp-pred) rel (tu/tmp-pred)]
    (v/assert kb (list 'genl text 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint text 'unaryPredicate) 'CxUniverse)
    (v/assert kb (list 'arity rel 2) 'CxUniverse)
    (v/assert kb (list 'arg p 1 text) 'CxUniverse)
    (v/assert kb (list 'typeRelationPredicate rel) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 'thing) 'CxUniverse)   ; position 1 only
    (testing "the relation kind says of position 2 what no genlArg was written for"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list rel (tu/tmp-type) '?x))
                                 'CxUniverse))))
      (is (re-find #"typeRelationPredicate"
                   (:message (first (v/check kb (list 'implies (list p '?x)
                                                      (list rel (tu/tmp-type) '?x))
                                             'CxUniverse))))))))

;; ---- the two forms the issue named --------------------------------------

(tu/deftest-kb the-shipped-schema-refuses-a-string-fed-into-a-type-slot
  (testing "?kind is asked for a kind at both ends — admissible"
    (is (= [] (v/check kb '(implies (arg ?pred ?n ?kind) (genl ?pred ?kind)) 'CxUniverse)))
    (is (v/assert kb '(implies (arg ?pred ?n ?kind) (genl ?pred ?kind)) 'CxUniverse)))
  (testing "?string is a character_string in the antecedent and a kind in the consequent"
    (let [form '(implies (comment ?x ?string) (genl ?x ?string))
          ps   (v/check kb form 'CxUniverse)]
      (is (= [:arg-variable] (mapv :type ps)))
      (is (= '?string (:variable (first ps))))
      (is (= '[character_string unaryPredicate] (:expected (first ps))))
      (is (= :arg-variable (ex-type #(v/assert kb form 'CxUniverse)))))))
