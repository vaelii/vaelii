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
  `genlArg` names it **or** when its predicate is a `type_relation_predicate`, which says
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
    (v/assert kb (list 'disjoint text 'unary_predicate) 'CxUniverse)
    (v/assert kb (list 'arg p 1 text) 'CxUniverse)
    (v/assert kb (list 'type_relation_predicate rel) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 'thing) 'CxUniverse)
    (testing "a variable bound to a text is not a kind, so it cannot fill a kind slot"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list rel '?x)) 'CxUniverse)))))))

(tu/deftest-kb a-typeRelationPredicate-constrains-a-position-no-declaration-names
  (let [text (tu/tmp-type)
        p (tu/tmp-pred) rel (tu/tmp-pred)]
    (v/assert kb (list 'genl text 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint text 'unary_predicate) 'CxUniverse)
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'arg p 1 text) 'CxUniverse)
    (v/assert kb (list 'type_relation_predicate rel) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 'thing) 'CxUniverse)   ; position 1 only
    (testing "the relation kind says of position 2 what no genlArg was written for"
      (is (= :arg-variable
             (ex-type #(v/assert kb (list 'implies (list p '?x) (list rel (tu/tmp-type) '?x))
                                 'CxUniverse))))
      (is (re-find #"type_relation_predicate"
                   (:message (first (v/check kb (list 'implies (list p '?x)
                                                      (list rel (tu/tmp-type) '?x))
                                             'CxUniverse))))))))

;; ---- the two forms the issue named --------------------------------------

(tu/deftest-kb the-shipped-schema-refuses-a-string-fed-into-a-type-slot
  (testing "?kind is asked for a kind at both ends — admissible"
    (is (= [] (v/check kb '(implies (arg ?pred ?n ?kind) (genl ?pred ?kind)) 'CxUniverse)))
    (is (v/assert kb '(implies (arg ?pred ?n ?kind) (genl ?pred ?kind)) 'CxUniverse)))
  (testing "?string is a string in the antecedent and a kind in the consequent"
    (let [form '(implies (comment ?x ?string) (genl ?x ?string))
          ps   (v/check kb form 'CxUniverse)]
      (is (= [:arg-variable] (mapv :type ps)))
      (is (= '?string (:variable (first ps))))
      (is (= '[string unary_predicate] (:expected (first ps))))
      (is (= :arg-variable (ex-type #(v/assert kb form 'CxUniverse)))))))

(tu/deftest-kb the-shipped-schema-refuses-a-function-fed-into-a-type-slot
  ;; The second half CxCore states outright — "A function is a thing, and is not a
  ;; predicate" — now as a fact rather than as prose.  Every type is a unary_predicate,
  ;; so a type-level position asks for a predicate, and the three declarations that
  ;; name a function-valued argument all meet `genl` on a variable no term can fill.
  (doseq [pred '[result genlResult functionCorrespondingPredicate]]
    (testing (str pred " arg 1 is a function, and genl arg 1 is a type")
      (let [form (list 'implies (if (= pred 'functionCorrespondingPredicate)
                                  (list pred '?f '?p 2)
                                  (list pred '?f '?t))
                       (list 'genl '?f (if (= pred 'functionCorrespondingPredicate) '?p '?t)))
            ps   (v/check kb form 'CxUniverse)]
        (is (= [:arg-variable] (mapv :type ps)))
        (is (= '?f (:variable (first ps))))
        (is (= '[function unary_predicate] (:expected (first ps))))
        (is (= :arg-variable (ex-type #(v/assert kb form 'CxUniverse)))))))
  (testing "and the type-valued position of the same literal is unaffected"
    (is (= [] (v/check kb '(implies (result ?f ?t) (genl ?t ?t)) 'CxUniverse)))))

(tu/deftest-kb the-value-kinds-are-one-vocabulary-and-symbol-is-mention-only
  (testing "the disjointness on number carries integer with it"
    ;; `(arg arity 2 non_negative_integer)`, and that type is below integer and number,
    ;; which no relation is
    (let [form '(implies (arity ?p ?n) (genl ?p ?n))
          ps   (v/check kb form 'CxUniverse)]
      (is (= [:arg-variable] (mapv :type ps)))
      (is (= '?n (:variable (first ps))))
      (is (= '[non_negative_integer unary_predicate] (:expected (first ps))))))
  (testing "symbol carries no disjointness, a name being how a predicate is written"
    ;; the deliberate absence, and the one that has to be pinned: `(disjoint symbol
    ;; predicate)` would are indistinguishable from a use-level claim and be false of every predicate name,
    ;; so a variable asked for a symbol at one end and a kind at the other is admissible
    (let [p (tu/tmp-pred)]
      (v/assert kb (list 'arg p 1 'symbol) 'CxUniverse)
      (is (= [] (v/check kb (list 'implies (list p '?x) (list 'genl '?x 'thing))
                         'CxUniverse))))))

;; ---- the other entry point: a rule nobody typed ---------------------------------
;; `check-rule!` is read from two places.  The author's `assert` throws it, which is
;; every test above; a mint reads the same list as a **value** (`checks/rule-violation`)
;; and drops what it cannot admit, because an exception escaping a firing would leave
;; the fixpoint half computed.  Both mint entry points are here: a generator's fill, and a
;; `defn*` fact's companion rule.

(defn- mentioning
  "The stored rules in `ctx` whose sentence names `term` anywhere."
  [kb ctx term]
  (filter #(and (:antecedent %)
                (some #{term} (tree-seq sequential? seq (:sentence %))))
          (v/sentexes-in-context kb ctx)))

(tu/deftest-kb a-generator-mint-that-clashes-is-dropped-and-recorded
  (let [[a b] (disjoint-pair kb)
        marker (tu/tmp-pred) src (tu/tmp-pred) fine (tu/tmp-pred) dst (tu/tmp-pred)]
    (v/assert kb (list 'arg src 1 a) 'CxUniverse)
    (v/assert kb (list 'arg fine 1 b) 'CxUniverse)
    (v/assert kb (list 'arg dst 1 b) 'CxUniverse)
    ;; the generator itself carries no clash: `?p` is a hole, so the antecedent it heads
    ;; declares nothing until a firing grounds it
    (is (v/assert kb (list 'implies (list marker '?p)
                           (list 'implies (list '?p '?x) (list dst '?x)))
                  'CxUniverse)
        "the generator stands — what the fill makes impossible is not visible here")
    (v/clear-violations! kb)
    (testing "a fill whose declaration agrees with the consequent stamps the rule"
      (v/assert kb (list marker fine) 'CxUniverse)
      (is (seq (mentioning kb 'CxUniverse fine)))
      (is (empty? (v/violations kb))))
    (testing "a fill whose declaration contradicts it is dropped, not thrown"
      (v/assert kb (list marker src) 'CxUniverse)
      (is (empty? (mentioning kb 'CxUniverse src)) "nothing was stored for the mint"))
    (testing "and the drop is readable as this check's kind"
      (let [vs (v/violations kb)]
        (is (= [:arg-variable] (mapv :violation vs)))
        (is (= #{a b} (set (:expected (:detail (first vs))))))
        ;; the two types are content and are pinned; the variable's *spelling* is not.
        ;; A mint standardizes its rule apart before storing it, so the name the entry
        ;; carries is the stamped rule's own and not the one the generator was written
        ;; with — naming which is what a consumer needs, spelling it is not.
        (is (re-find #"^\?" (name (:variable (:detail (first vs))))))))))

(tu/deftest-kb a-defn-companion-rule-that-clashes-is-dropped-and-recorded
  ;; the second mint entry point: `defnSufficient` names a membership at both ends, so the two
  ;; argument declarations meet on the `?x` the companion rule carries between them
  (let [[a b] (disjoint-pair kb)
        coll (tu/tmp-pred) cond' (tu/tmp-pred)]
    (v/assert kb (list 'arg cond' 1 a) 'CxUniverse)
    (v/assert kb (list 'arg coll 1 b) 'CxUniverse)
    (v/clear-violations! kb)
    (v/assert kb (list 'defnSufficient coll (list cond' '?x)) 'CxUniverse)
    (is (empty? (mentioning kb 'CxUniverse cond')) "no companion rule was materialized")
    (is (= [:arg-variable] (mapv :violation (v/violations kb))))))

;; ---- the two kinds the arm does not read, and why ------------------------
;; `checks/declaration-queries` reads four constraint kinds; the variable arm reads two.
;; That is a result, not a scope decision: each of the pairings below has a binding both
;; ends accept, so refusing the rule would refuse one that works.  Every test here is a
;; **witness for an absence** — it goes red the moment somebody widens the arm, which is
;; the point of writing it down as a test rather than as a paragraph.

(tu/deftest-kb a-quoted-demand-and-an-instance-demand-are-not-a-clash
  ;; A **compound** satisfies both, and it is the only thing that does: `value-kind`
  ;; declines to answer for one, because what `(MsrFn 5)` denotes is its function's
  ;; business (`result`) rather than its syntax's.  A string value used to be the
  ;; witness here and is not one — `args-problem` types a literal by its kind and
  ;; convicts it, `string` not reaching `predicate`.
  (let [qs (tu/tmp-pred) ap (tu/tmp-pred) f (tu/tmp-ind)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'string) 'CxUniverse)
    (v/assert kb (list 'unary_predicate ap) 'CxUniverse)
    (v/assert kb (list 'arg ap 1 'predicate) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (testing "the rule stands, though the two demands read as contradictory"
      (is (= [] (v/check kb (list 'implies (list qs '?x) (list ap '?x)) 'CxUniverse))))
    (testing "and here is the binding that says why"
      (is (= [] (v/check kb (list qs (list f 5)) 'CxUniverse)))
      (is (= [] (v/check kb (list ap (list f 5)) 'CxUniverse))))
    (testing "a string value is no longer one — the arg side types it and convicts"
      (is (= [:arg-type] (mapv :type (v/check kb (list ap "Bob") 'CxUniverse)))))))

(tu/deftest-kb two-quoted-demands-are-not-a-clash
  ;; two incomparable syntactic kinds still admit the one kind `value-kind` does not
  ;; answer for.  A keyword was the witness until keywords got a name of their own; a
  ;; compound is not going to get one, for the reason above.
  (let [qs (tu/tmp-pred) qi (tu/tmp-pred) f (tu/tmp-ind)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'string) 'CxUniverse)
    (v/assert kb (list 'unary_predicate qi) 'CxUniverse)
    (v/assert kb (list 'quotedArg qi 1 'integer) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (is (= [] (v/check kb (list 'implies (list qs '?x) (list qi '?x)) 'CxUniverse)))
    (testing "no term is both a string and an integer, and a compound is neither"
      (is (= [] (v/check kb (list qs (list f 5)) 'CxUniverse)))
      (is (= [] (v/check kb (list qi (list f 5)) 'CxUniverse))))))

(tu/deftest-kb a-quoted-demand-and-a-type-level-position-are-not-a-clash
  ;; the same `checkable-term?` floor one level up: a literal in a type-level position is
  ;; admitted, so a variable can be a string at one end and fill a kind slot at the other
  (let [qs (tu/tmp-pred)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'string) 'CxUniverse)
    (is (= [] (v/check kb (list 'implies (list qs '?x) (list 'genl '?x 'thing)) 'CxUniverse)))
    (is (= [] (v/check kb '(genl "Bob" thing) 'CxUniverse))
        "which is only true because this is admitted")))

(tu/deftest-kb an-interArg-trigger-is-a-demand-not-a-fact
  ;; the decisive one, and the reason `interArg` cannot join the arm at all: `(arg P i
  ;; T)` does not make argument i a T — an unclassified term satisfies it vacuously — so
  ;; no rule's own bindings entail the trigger, and a conditional constraint that never
  ;; provably fires can convict nothing.
  (let [[u v'] (disjoint-pair kb)
        a      (tu/tmp-type)
        ia     (tu/tmp-pred) trig (tu/tmp-pred) tgt (tu/tmp-pred)
        Unc    (tu/tmp-ind)  Val  (tu/tmp-ind)]
    (v/assert kb (list 'genl a 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate ia) 'CxUniverse)
    (v/assert kb (list 'interArg ia 1 a 2 u) 'CxUniverse)
    (v/assert kb (list 'unary_predicate trig) 'CxUniverse)
    (v/assert kb (list 'arg trig 1 a) 'CxUniverse)
    (v/assert kb (list 'binary_predicate tgt) 'CxUniverse)
    (v/assert kb (list 'arg tgt 2 v') 'CxUniverse)
    (testing "the rule stands, though the interArg target and the arg type are disjoint"
      (is (= [] (v/check kb (list 'implies (list 'and (list trig '?x) (list ia '?x '?y))
                                  (list tgt '?x '?y))
                         'CxUniverse))))
    (testing "and a binding that classifies neither variable satisfies the whole chain"
      (is (= [] (v/check kb (list trig Unc) 'CxUniverse)))
      (is (= [] (v/check kb (list ia Unc Val) 'CxUniverse)))
      (is (= [] (v/check kb (list tgt Unc Val) 'CxUniverse))))))

(tu/deftest-kb an-instance-demand-and-a-subtype-demand-are-not-a-clash
  ;; beyond the `unary_predicate` mapping the arm already makes: a term may be an instance
  ;; of one type and a subtype of another at once, and the meta-ontology depends on it —
  ;; every type in the KB is an instance of unary_predicate.
  (let [d (tu/tmp-type) inst (tu/tmp-pred) sub (tu/tmp-pred) both (tu/tmp-type)]
    (v/assert kb (list 'genl d 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate inst) 'CxUniverse)
    (v/assert kb (list 'arg inst 1 d) 'CxUniverse)
    (v/assert kb (list 'binary_predicate sub) 'CxUniverse)
    (v/assert kb (list 'genlArg sub 1 'thing) 'CxUniverse)
    (is (= [] (v/check kb (list 'implies (list inst '?x) (list sub '?x 'thing)) 'CxUniverse)))
    (testing "one term, both readings"
      (v/assert kb (list d both) 'CxUniverse)
      (v/assert kb (list 'genl both 'thing) 'CxUniverse)
      (is (= [] (v/check kb (list sub both 'thing) 'CxUniverse))))))

(tu/deftest-kb a-variable-functor-carries-no-argument-constraints
  ;; `?pred` names no predicate, so nothing declares its positions.  Reading it as one
  ;; hands `declaration-reader` a match pattern instead of a name and EVERY (arg P n T)
  ;; in the KB comes back, so a variadic rule collects two unrelated predicates' demands
  ;; on one variable — (arg typeToInstancePred 2 instance_relation_predicate) beside
  ;; (genlArg arg1 2 thing) — and is refused for a clash neither declaration is about.
  ;; CxCore ships exactly such a rule.
  (testing "the shipped ist lifting rule checks clean"
    (is (= [] (v/check kb '(set/inertRule
                            (implies (?pred . ?args) (ist CxUniverse (?pred . ?args))))
                       'CxCore))))
  (testing "a bare variadic rule keeps its OWN refusal and loses only the spurious one"
    ;; :not-indexable is the right refusal for a variable functor in an antecedent, and
    ;; it stands; what goes is the :arg-variable clash read off other predicates
    (let [found (v/check kb '(implies (?pred ?a ?b) (?pred ?b ?a)) 'CxUniverse)]
      (is (some #(= :not-indexable (:type %)) found))
      (is (not-any? #(= :arg-variable (:type %)) found))))
  (testing "while a CONCRETE functor still convicts a variable its own positions clash on"
    (tu/with-terms [narrowOf lithe_thing squat_thing A]
      (v/assert kb (list 'genl lithe_thing 'thing) 'CxUniverse)
      (v/assert kb (list 'genl squat_thing 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint lithe_thing squat_thing) 'CxUniverse)
      (v/assert kb (list 'binary_predicate narrowOf) 'CxUniverse)
      (v/assert kb (list 'arg narrowOf 1 lithe_thing) 'CxUniverse)
      (v/assert kb (list 'arg narrowOf 2 squat_thing) 'CxUniverse)
      (let [found (v/check kb (list 'implies (list narrowOf '?x '?x) (list 'thing A))
                           'CxUniverse)]
        (is (some #(= :arg-variable (:type %)) found)
            "a real predicate's own two disjoint positions still convict one variable")))))
