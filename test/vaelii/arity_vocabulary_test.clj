;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arity-vocabulary-test
  "The relation-wide exact/variable arity partition and its documentary floor vocabulary."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.kb :as kb]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- arity-of
  "The arity every reader outside the check reads for `pred` from `context`
  (`kb/relation-arity`): its `(arity P n)` declaration, else its exact-arity class
  membership."
  [kb pred context]
  (kb/relation-arity kb pred context))

(tu/deftest-kb relation-is-the-common-parent
  (is (v/genl? kb 'predicate 'relation))
  (is (v/genl? kb 'function 'relation))
  (is (v/genl? kb 'relation 'thing))
  (is (v/isa? kb 'lessThan 'relation))
  (is (v/isa? kb 'MotherFn 'relation)))

(tu/deftest-kb starter-distinguishes-type-nodes-from-binary-predicate-nodes
  (doseq [mapping '[relationTypeByArity predicateTypeByArity functionTypeByArity]]
    (is (v/isa? kb mapping 'binary_predicate))
    (is (not (v/isa? kb mapping 'unary_predicate)))
    (is (= 2 (arity-of kb mapping 'CxCore))))
  (doseq [type '[thing animal tangible fixed_arity]]
    (is (v/isa? kb type 'unary_predicate)))
  (is (v/genl? kb 'predicateTypeByArity 'relationTypeByArity))
  (is (v/genl? kb 'functionTypeByArity 'relationTypeByArity)))

(tu/deftest-kb the-arity-generator-stamps-the-class-from-one-mapping-fact
  ;; One mapping fact mints one rule, and its conclusions rest on it: the arity concludes
  ;; the class, and retracting the fact withdraws each class it concluded.  No rule
  ;; concludes an arity from a class, since arity is on the forced-monotonic roster.
  (doseq [mapping-first? [true false]]
    (tu/with-terms [four_place_relation classifiedRelation exactOnlyRelation]
      (v/assert kb (list 'genl four_place_relation 'fixed_arity) 'CxCore)
      (let [mapping (list 'relationTypeByArity four_place_relation 4)
            member  (list four_place_relation classifiedRelation)
            h       (if mapping-first?
                      (let [h (v/assert kb mapping 'CxCore)]
                        (v/assert kb member 'CxCore)
                        h)
                      (do (v/assert kb member 'CxCore)
                          (v/assert kb mapping 'CxCore)))
            exact   (v/assert kb (list 'arity exactOnlyRelation 4) 'CxCore)]
        (testing "the arity concludes the class, and the class concludes no arity"
          (is (v/ask? kb (list four_place_relation exactOnlyRelation) 'CxCore))
          (is (empty? (v/sentexes-matching kb (list 'arity classifiedRelation '?n) 'CxCore))))
        (testing "and the class rests on the mapping fact"
          (v/retract! kb h)
          (is (v/ask? kb member 'CxCore) "the asserted membership stands")
          (is (v/ask? kb (list 'arity exactOnlyRelation 4) 'CxCore)
              "the asserted arity stands")
          (is (not (v/ask? kb (list four_place_relation exactOnlyRelation) 'CxCore))
              "while the class it derived goes with the rule that derived it"))
        (v/retract! kb exact)))))

(tu/deftest-kb an-arity-and-its-class-are-each-read-as-the-arity
  ;; The arity concludes the class and the class is read as the arity, so whichever was
  ;; asserted is the only premise and retracting it takes both readings.
  (testing "the arity is the premise"
    (tu/with-terms [pairOf]
      (let [h (v/assert kb (list 'arity pairOf 2) 'CxUniverse)]
        (is (v/isa? kb pairOf 'binary))
        (is (v/isa? kb pairOf 'fixed_arity))
        (v/retract! kb h)
        (is (not (v/isa? kb pairOf 'binary)))
        (is (empty? (v/sentexes-matching kb (list 'arity pairOf '?n) 'CxUniverse))))))
  (testing "the class is the premise"
    (tu/with-terms [chainOf]
      (let [h (v/assert kb (list 'binary chainOf) 'CxUniverse)]
        (is (= 2 (arity-of kb chainOf 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list 'arity chainOf '?n) 'CxUniverse)))
        (v/retract! kb h)
        (is (nil? (arity-of kb chainOf 'CxUniverse)))
        (is (not (v/isa? kb chainOf 'binary))))))
  (testing "an arity no class maps to concludes no class at all"
    (is (v/ask? kb '(arity InstantFn 6) 'CxTime))
    (doseq [type '[unary binary ternary]]
      (is (not (v/isa? kb 'InstantFn type))))))

(tu/deftest-kb exact-arity-and-variable-floors-are-distinct
  (testing "an exact declaration is fixed, not an overloaded floor"
    (is (v/ask? kb '(fixed_arity interArg) 'CxCore))
    (is (not (v/ask? kb '(arityMin interArg 5) 'CxCore))))
  (testing "the four current variable-arity predicates state only their lower bounds"
    (doseq [relation '[functionCorrespondingPredicate greaterThan lessThan termsRelated]]
      (is (some? (v/handle-of kb (list 'arityMin relation 2) 'CxCore))
          (str relation " has an asserted minimum"))
      (is (not (v/isa? kb relation 'binary_predicate))
          (str relation " is not overloaded as exactly binary")))))

(tu/deftest-kb relation-wide-types-own-the-arity-rules
  ;; Three mapping facts, not nine.  The predicate and function members are mapped by
  ;; their genl edges to unary / binary / ternary, and a per-member fact would stamp a
  ;; rule classifying a function of that arity as a predicate.
  (doseq [[type arity] '[[unary 1] [binary 2] [ternary 3]]]
    (is (v/ask? kb (list 'relationTypeByArity type arity) 'CxCore)))
  (doseq [type '[unary_predicate binary_predicate ternary_predicate
                 unary_function binary_function ternary_function]]
    (is (empty? (v/sentexes-matching kb (list 'relationTypeByArity type '?arity) 'CxCore))
        (str type " is mapped by its genl edge rather than by a fact of its own")))
  (is (v/genl? kb 'predicateTypeByArity 'relationTypeByArity)
      "the specialization stays declared for a KB that maps an unshipped arity")
  (is (v/genl? kb 'functionTypeByArity 'relationTypeByArity))
  (is (v/genl? kb 'unary_predicate 'unary))
  (is (v/genl? kb 'binary_predicate 'binary))
  (is (v/genl? kb 'ternary_predicate 'ternary))
  (is (v/genl? kb 'unary_function 'unary))
  (is (v/genl? kb 'binary_function 'binary))
  (is (v/genl? kb 'ternary_function 'ternary))
  (doseq [type '[unary_predicate binary_predicate ternary_predicate]]
    (is (v/genl? kb type 'fixed_arity_predicate)))
  (doseq [type '[unary_function binary_function ternary_function]]
    (is (v/genl? kb type 'fixed_arity_function)))
  (is (v/isa? kb 'parentOf 'fixed_arity_predicate))
  (is (v/isa? kb 'MotherFn 'fixed_arity_function)))

(tu/deftest-kb disjoint-arity-policies-clash-and-the-roster-membership-wins
  ;; `variable_arity` is on the forced-monotonic roster and `fixed_arity` is not, so the
  ;; disjoint pair takes the `:default` `fixed_arity` membership OUT in either order
  (doseq [[first-policy second-policy] '[[fixed_arity variable_arity]
                                         [variable_arity fixed_arity]]]
    (tu/with-terms [candidateRelation]
      (v/assert kb (list first-policy candidateRelation) 'CxUniverse)
      (v/assert kb (list second-policy candidateRelation) 'CxUniverse)
      (is (not (v/ask? kb (list 'fixed_arity candidateRelation) 'CxUniverse))
          (str second-policy " after " first-policy ": fixed_arity is OUT"))
      (is (v/ask? kb (list 'variable_arity candidateRelation) 'CxUniverse))))
  (tu/with-terms [compatiblePredicate]
    (v/assert kb (list 'unary_predicate compatiblePredicate) 'CxUniverse)
    (is (v/assert kb (list 'fixed_arity_predicate compatiblePredicate) 'CxUniverse)
        "a predicate specialization and its fixed policy are compatible")))

(tu/deftest-kb the-arity-policy-clash-is-the-same-clash-in-either-order
  ;; the entailing reading: the derivation is the subject
  (tu/with-entailing
    ;; The clash between an exact class and the variable policy is one contradiction, so
    ;; the write order must not decide which violation names it.  A NARROWING arg
    ;; declaration below the policy classes — (arg fixed_arity_predicate 1 predicate) —
    ;; is what makes it: a relation whose only stated type is variable_arity reaches
    ;; relation and not predicate, so the exact class would be convicted for the
    ;; argument's type rather than for the policy it contradicts.  CxCore declares the position on
    ;; fixed_arity and variable_arity alone for that reason.
    (doseq [[first-class second-class] '[[variable_arity binary_predicate]
                                         [binary_predicate variable_arity]
                                         [variable_arity_predicate unary_predicate]
                                         [variable_arity unary_function]
                                         [unary_function variable_arity]]]
      (tu/with-terms [candidateRelation]
        (v/assert kb (list first-class candidateRelation) 'CxUniverse)
        (is (tu/stored-in-clash? kb (list second-class candidateRelation) 'CxUniverse)
            (str second-class " after " first-class " is stored as a disjoint clash"))))
    (testing "a relation of the wrong kind clashes too, by the genl edges, and the
            :default kind membership loses to the roster one"
      (tu/with-terms [somePredicate]
        (v/assert kb (list 'predicate somePredicate) 'CxUniverse)
        (v/assert kb (list 'unary_function somePredicate) 'CxUniverse)
        (is (not (v/ask? kb (list 'predicate somePredicate) 'CxUniverse)))))
    (testing "and an argument that is no relation at all derives fixed_arity's own type,
            which clashes with the one it holds"
      (tu/with-terms [someIndividual]
        (v/assert kb (list 'person someIndividual) 'CxUniverse)
        (v/assert kb (list 'fixed_arity_predicate someIndividual) 'CxUniverse)
        (is (tu/stored-in-clash? kb (list 'relation someIndividual) 'CxUniverse)
            "the position declared on fixed_arity descends to its specializations")))))

(tu/deftest-kb relation-wide-exact-classes-clash-with-each-other
  (doseq [[first-type second-type] '[[unary binary] [binary unary]
                                     [unary ternary] [ternary unary]
                                     [binary ternary] [ternary binary]]]
    (tu/with-terms [candidateRelation]
      (v/assert kb (list first-type candidateRelation) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list second-type candidateRelation) 'CxUniverse)
          (str second-type " after " first-type " is stored as a disjoint clash"))))
  (tu/with-terms [compatibleRelation]
    (v/assert kb (list 'unary compatibleRelation) 'CxUniverse)
    (is (v/assert kb (list 'fixed_arity compatibleRelation) 'CxUniverse)
        "an exact class and its fixed policy are compatible")))

(tu/deftest-kb fixed-and-variable-arity-have-relation-kind-specializations
  (testing "a predicate carrying an exact arity declaration is classified"
    (is (v/isa? kb 'interArg 'fixed_arity_predicate))
    (is (v/isa? kb 'interArg 'fixed_arity))
    (is (v/isa? kb 'interArg 'relation)))
  (testing "all current variable predicates carry the predicate specialization"
    (doseq [relation '[functionCorrespondingPredicate greaterThan lessThan termsRelated]]
      (is (v/isa? kb relation 'variable_arity_predicate))
      (is (v/isa? kb relation 'variable_arity))
      (is (v/isa? kb relation 'relation))))
  (testing "the function specializations exist without inventing instances"
    (is (v/genl? kb 'fixed_arity_function 'fixed_arity))
    (is (v/genl? kb 'fixed_arity_function 'function))
    (is (v/genl? kb 'variable_arity_function 'variable_arity))
    (is (v/genl? kb 'variable_arity_function 'function)))
  (testing "the shipped functions use their exact relation-wide specializations"
    (doseq [[function type] '[[FatherFn unary_function]
                              [MotherFn unary_function]
                              [YearFn unary_function]
                              [DatetimeFn unary_function]
                              [MonthFn binary_function]
                              [QuantityFn binary_function]
                              [DayFn ternary_function]
                              [QuantityIntervalFn ternary_function]
                              [PredAllExistsFn ternary_function]
                              [PredExistsAllFn ternary_function]
                              [PredExistsInstanceFn ternary_function]
                              [PredInstanceExistsFn ternary_function]]]
      (is (v/isa? kb function type) (str function " is " type)))
    (is (v/isa? kb 'InstantFn 'fixed_arity_function)
        "the six-argument function stays explicitly fixed without minting a named family"))
  (testing "a function may use the relation-wide variable vocabulary"
    (tu/with-terms [RepeatFn]
      (v/assert kb (list 'variable_arity_function RepeatFn) 'CxUniverse)
      (v/assert kb (list 'arityMin RepeatFn 2) 'CxUniverse)
      (is (v/isa? kb RepeatFn 'function))
      (is (v/isa? kb RepeatFn 'variable_arity))
      (is (v/isa? kb RepeatFn 'at_least_binary)))))

(tu/deftest-kb arity-minimum-classifies-relations-generically
  (testing "a minimum of two derives only the binary floor"
    (is (v/isa? kb 'lessThan 'at_least_binary))
    (is (not (v/isa? kb 'lessThan 'at_least_ternary))))
  (testing "a fixed arity of two or more is at least binary too"
    (is (v/isa? kb 'parentOf 'at_least_binary))
    (is (not (v/isa? kb 'parentOf 'at_least_ternary)))
    (is (v/isa? kb 'interArg 'at_least_binary))
    (is (v/isa? kb 'interArg 'at_least_ternary)
        "an arity no exact class maps to reaches the floors through the arity rules"))
  (testing "a unary relation is at neither floor"
    (is (not (v/isa? kb 'person 'at_least_binary))))
  (testing "the ternary floor specializes the binary floor"
    (is (v/genl? kb 'at_least_ternary 'at_least_binary))))

(tu/deftest-kb admits-argnum-answers-the-position-query
  ;; #68: (admitsArgnum R n) is answered at query time from R's declared arity and
  ;; variable-arity mark — not from a finite rule set — so the declared vocabulary now
  ;; carries an answer.
  (is (v/isa? kb 'admitsArgnum 'binary_predicate))
  (is (v/ask? kb '(arg admitsArgnum 1 relation) 'CxCore))
  (is (v/ask? kb '(arg admitsArgnum 2 positive_integer) 'CxCore))
  (testing "a fixed-arity relation admits one through its arity and no higher position"
    (tu/with-terms [ternaryRel]
      (v/assert kb (list 'ternary_predicate ternaryRel) 'CxCore)
      (doseq [n [1 2 3]]
        (is (v/ask? kb (list 'admitsArgnum ternaryRel n) 'CxCore)
            (str "position " n " is admitted")))
      (is (not (v/ask? kb (list 'admitsArgnum ternaryRel 4) 'CxCore))
          "the first position above the arity is not admitted")))
  (testing "a variable-arity relation admits its guaranteed positions and every higher one"
    (doseq [n [1 2 3 212]]                                ; lessThan is variable_arity, arityMin 2
      (is (v/ask? kb (list 'admitsArgnum 'lessThan n) 'CxCore)
          (str "variable-arity position " n " is admitted"))))
  (testing "zero and negative positions never admit"
    (is (not (v/ask? kb '(admitsArgnum lessThan 0) 'CxCore)))
    (is (not (v/ask? kb '(admitsArgnum lessThan -1) 'CxCore))))
  (testing "an unclassified relation's positions stay unknown, not admitted"
    (tu/with-terms [unknownRel]
      (v/assert kb (list 'predicate unknownRel) 'CxCore)
      (is (not (v/ask? kb (list 'admitsArgnum unknownRel 1) 'CxCore))
          "open-world: no declared arity and no variable mark means no proven position"))))

(tu/deftest-kb admits-argnum-and-the-position-census-answer-one-question
  ;; #68 single source: admitsArgnum and checks/arg-position-problem read one decision,
  ;; provers/admits-position?, so a position the constraint census refuses on a relation is
  ;; exactly one admitsArgnum does not prove, and one it allows is one admitsArgnum proves.
  (tu/with-terms [censusRel]
    (v/assert kb (list 'ternary_predicate censusRel) 'CxCore)
    (testing "a position within the arity: the census admits the constraint, the query proves it"
      (is (v/assert kb (list 'arg censusRel 3 'thing) 'CxCore))
      (is (v/ask? kb (list 'admitsArgnum censusRel 3) 'CxCore)))
    (testing "a position past the arity: the census refuses the constraint, the query denies it"
      (let [e (try (v/assert kb (list 'arg censusRel 4 'thing) 'CxCore) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :arg-position (:type (ex-data e)))
            "the constraint census refuses argument 4 of a ternary relation")
        (is (not (v/ask? kb (list 'admitsArgnum censusRel 4) 'CxCore))
            "and admitsArgnum does not prove the position it refused")))))

(tu/deftest-kb admits-argnum-parity-for-functions
  ;; a variable-arity function admits every positive position, like the predicate case; a
  ;; fixed-arity function alone invents no numeric arity, so its positions stay unknown.
  (tu/with-terms [ChainFn PlainFn]
    (v/assert kb (list 'variable_arity_function ChainFn) 'CxCore)
    (v/assert kb (list 'arityMin ChainFn 2) 'CxCore)
    (testing "a variable-arity function admits every positive position"
      (doseq [n [1 2 3 9]]
        (is (v/ask? kb (list 'admitsArgnum ChainFn n) 'CxCore))))
    (v/assert kb (list 'fixed_arity_function PlainFn) 'CxCore)
    (testing "a fixed-arity function invents no numeric arity — its positions stay unknown"
      (is (not (v/ask? kb (list 'admitsArgnum PlainFn 1) 'CxCore))
          "the numeric arity table is predicate-specific, so a function has no proven position"))))

(tu/deftest-kb every-relation-has-exactly-one-arity-policy
  (let [relations  (->> (v/query kb '(relation ?relation) 'CxInference)
                        (map #(get % '?relation))
                        set)
        violations (into (sorted-map)
                         (keep (fn [relation]
                                 (let [fixed?    (v/ask? kb (list 'fixed_arity relation)
                                                         'CxInference)
                                       variable? (v/ask? kb (list 'variable_arity relation)
                                                         'CxInference)]
                                   (when (= fixed? variable?)
                                     [relation {:fixed fixed? :variable variable?}]))))
                         relations)]
    (is (> (count relations) 300)
        "the oracle enumerates the loaded CxInference vocabulary, not an empty fixture")
    (is (empty? violations)
        (str "relations outside the exactly-one arity-policy partition: "
             (pr-str violations)))
    (is (some? (v/handle-of kb '(partition relation fixed_arity variable_arity) 'CxCore))
        "the partition is declared in KB data")))

;; ---- the declarations the merge added to the shipped functions ------------

(tu/deftest-kb the-six-argument-function-declares-every-field
  ;; `(arity InstantFn 6)` and the six `(arg InstantFn N integer)` are assertible at all
  ;; only because the argument vocabulary's first position is `relation` rather than
  ;; `predicate`: a function could carry neither before.  Six is not a relation-wide
  ;; exact class, so `InstantFn` is `fixed_arity_function` by declaration and reaches no
  ;; `unary` / `binary` / `ternary`.
  (is (v/ask? kb '(arity InstantFn 6) 'CxTime))
  (is (v/isa? kb 'InstantFn 'fixed_arity))
  (doseq [type '[unary binary ternary]]
    (is (not (v/isa? kb 'InstantFn type))
        (str "six arguments do not classify InstantFn as " type)))
  (doseq [position (range 1 7)]
    (is (v/ask? kb (list 'arg 'InstantFn position 'integer) 'CxTime)
        (str "field " position " is declared an integer")))
  (testing "and the ternary calendar constructor carries its class, not six arg rows"
    (is (v/isa? kb 'DayFn 'ternary_function))
    (is (= 3 (arity-of kb 'DayFn 'CxTime)))))

(tu/deftest-kb the-relation-wide-declarations-are-what-the-arity-nogoods-read
  ;; The vocabulary is not documentation: a reader decides a tuple against the arity these
  ;; declarations bind, and `variable_arity` is the one exemption from it.
  (testing "an exact class takes a tuple of the wrong length OUT"
    (tu/with-terms [pairOf A B C]
      (v/assert kb (list 'binary_predicate pairOf) 'CxUniverse)
      (v/assert kb (list pairOf A B) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list pairOf A B C) 'CxUniverse))))
  (testing "and the variable policy exempts one, at any length"
    (tu/with-terms [chainOf A B C]
      (v/assert kb (list 'variable_arity_predicate chainOf) 'CxUniverse)
      (v/assert kb (list 'arityMin chainOf 2) 'CxUniverse)
      (is (v/assert kb (list chainOf A B C) 'CxUniverse))
      (is (v/ask? kb (list chainOf A B C) 'CxUniverse)))))

(tu/deftest-kb the-ternary-floor-derives-and-withdraws-with-its-minimum
  ;; No shipped relation states a minimum above two, so the `at_least_ternary`
  ;; rule fires on nothing in CxCore.  It is stated vocabulary either way, and this is
  ;; the case that reads it.
  (tu/with-terms [wideChainOf]
    (v/assert kb (list 'variable_arity_predicate wideChainOf) 'CxUniverse)
    (let [h (v/assert kb (list 'arityMin wideChainOf 4) 'CxUniverse)]
      (is (v/isa? kb wideChainOf 'at_least_ternary))
      (is (v/isa? kb wideChainOf 'at_least_binary)
          "the ternary floor specializes the binary one")
      (v/retract! kb h)
      (is (not (v/isa? kb wideChainOf 'at_least_ternary))
          "the floor rests on the minimum and goes with it")
      (is (not (v/isa? kb wideChainOf 'at_least_binary)))
      (is (v/isa? kb wideChainOf 'variable_arity)
          "the policy was asserted separately and stands"))))

(tu/deftest-kb the-minimum-does-not-become-an-exact-arity
  ;; `arityMin` is documentary: it derives the floors and nothing numeric.  A KB that
  ;; read it as an arity would refuse the chains the policy exists to admit.
  (tu/with-terms [chainOf]
    (v/assert kb (list 'variable_arity_predicate chainOf) 'CxUniverse)
    (v/assert kb (list 'arityMin chainOf 2) 'CxUniverse)
    (is (empty? (v/sentexes-matching kb (list 'arity chainOf '?n) 'CxUniverse)))
    (is (not (v/isa? kb chainOf 'binary)))
    (is (not (v/isa? kb chainOf 'fixed_arity))))
  (testing "and an exact arity does not become a minimum"
    (is (empty? (v/sentexes-matching kb '(arityMin interArg ?n) 'CxCore)))
    (is (v/ask? kb '(arity interArg 5) 'CxCore))))

;; ---- order independence over the shipped generator ------------------------
;;
;; The engine-wide invariant (docs/nmtms.md) asked of this vocabulary: the mapping fact,
;; the `genl` edge that puts a class under `fixed_arity`, the membership and an unrelated
;; exact declaration may arrive in any order, and the beliefs must not move.  Each
;; ordering runs on its own fresh terms, so the orderings cannot contaminate one another
;; and the reading is comparable across them; the `neutral` fixture takes them all away.

(defn- interleavings
  "Every linear extension of `chains`: each chain keeps its own order, and the chains
  interleave freely.  A `retract!` names the handle its own `assert` allocated, so the
  pair is one chain rather than two free ops."
  [chains]
  (let [chains (into [] (remove empty?) chains)]
    (if (empty? chains)
      (list ())
      (for [i (range (count chains))
            tail (interleavings (update chains i rest))]
        (cons (first (nth chains i)) tail)))))

(defn- spread
  "`n` of `orderings`, deterministically: every k-th from the first, and the last.
  `interleavings` returns the ops in their given order first and reversed last, so both
  extremes are always walked."
  [n orderings]
  (let [v (vec orderings)]
    (if (<= (count v) n)
      v
      (conj (into [] (comp (take-nth (quot (count v) (dec n))) (take (dec n))) (pop v))
            (peek v)))))

(defn- one-reading!
  "Run every linear extension of `chains` — `build` returns `[ops observe]` over fresh
  terms — and demand a single distinct reading; with `n`, a `spread` of `n` of them.
  Reports the split, with the index of the first ordering that produced each side, so a
  failure reproduces."
  [label build & [n]]
  (let [orderings (cond->> (interleavings (build :shape)) n (spread n))
        census (reduce (fn [acc [i ops]]
                         (let [[run observe] (build :run)
                               _ (doseq [k ops] ((get run k)))
                               r (observe)]
                           (if (contains? acc r)
                             (update-in acc [r :n] inc)
                             (assoc acc r {:n 1 :at i}))))
                       {}
                       (map-indexed vector orderings))]
    (is (= 1 (count census))
        (str label ": " (count census) " distinct readings across " (count orderings)
             " orderings — "
             (pr-str (sort-by (comp :at val) census))))
    (key (first (sort-by (comp :at val) census)))))

(defn- arity-generator-reads-once
  "The arity generator's four free ops, over `n` of their 24 orderings (all when nil).
  The generator may be handed its mapping fact before or after the class exists, and the
  membership before or after either.  The whole walk costs over a second, so `:default`
  walks a `spread` of it."
  [kb n]
  (let [result
        (one-reading!
         "arity generator"
         (fn [mode]
           (if (= mode :shape)
             [[:genl] [:mapping] [:member] [:unrelated]]
             (let [wide_arity (tu/tmp-type 'wide_arity)
                   chainOf    (tu/tmp-pred 'chainOf)
                   pairOf     (tu/tmp-pred 'pairOf)]
               [{:genl      #(v/assert kb (list 'genl wide_arity 'fixed_arity) 'CxCore)
                 :mapping   #(v/assert kb (list 'relationTypeByArity wide_arity 4) 'CxCore)
                 :member    #(v/assert kb (list wide_arity chainOf) 'CxCore)
                 ;; the SAME arity the mapping fact names, so the converse rule has
                 ;; something to conclude from whenever it is stamped
                 :unrelated #(v/assert kb (list 'arity pairOf 4) 'CxCore)}
                (fn []
                  {:derived-arity (v/ask? kb (list 'arity chainOf 4) 'CxCore)
                   :derived-fixed (v/isa? kb chainOf 'fixed_arity)
                   :no-variable   (v/isa? kb chainOf 'variable_arity)
                   :unrelated-fixed (v/isa? kb pairOf 'fixed_arity)
                   :converse      (v/ask? kb (list wide_arity pairOf) 'CxCore)
                   :conflicts     (count (v/conflicts kb))})])))
         n)]
    (testing "and the one reading is the intended one"
      (is (false? (:derived-arity result)) "the class derives no arity")
      (is (true? (:derived-fixed result)))
      (is (false? (:no-variable result)))
      (is (true? (:unrelated-fixed result)) "an exact arity marks the policy on its own")
      (is (true? (:converse result))
          "and the converse classifies it under the mapped type, in any order")
      (is (zero? (:conflicts result))))))

(tu/deftest-kb the-arity-generator-is-order-independent
  ;; 6 of the 24 orderings, both extremes among them; `…-in-every-ordering` walks all
  (arity-generator-reads-once kb 6))

(tu/deftest-kb ^:slow the-arity-generator-is-order-independent-in-every-ordering
  (arity-generator-reads-once kb nil))

(tu/deftest-kb withdrawing-a-mapping-fact-is-order-independent
  ;; The mapping fact's `retract!` may not precede its own `assert`, so the two are one
  ;; chain; every other op interleaves freely around them.  20 orderings.  What must not
  ;; move is that the stamped rule goes with the fact while the membership stays.
  (let [result
        (one-reading!
         "mapping withdrawal"
         (fn [mode]
           (if (= mode :shape)
             [[:genl :mapping :unmap] [:member] [:exact]]
             (let [wide_arity (tu/tmp-type 'wide_arity)
                   chainOf    (tu/tmp-pred 'chainOf)
                   exactOf    (tu/tmp-pred 'exactOf)
                   handle     (volatile! nil)]
               [{:genl    #(v/assert kb (list 'genl wide_arity 'fixed_arity) 'CxCore)
                 :mapping #(vreset! handle
                                    (v/assert kb (list 'relationTypeByArity wide_arity 4)
                                              'CxCore))
                 :unmap   #(v/retract! kb @handle)
                 :member  #(v/assert kb (list wide_arity chainOf) 'CxCore)
                 :exact   #(v/assert kb (list 'arity exactOf 4) 'CxCore)}
                (fn []
                  {:member-stands (v/ask? kb (list wide_arity chainOf) 'CxCore)
                   :arity-gone    (v/ask? kb (list 'arity chainOf 4) 'CxCore)
                   :mapping-gone  (v/ask? kb (list 'relationTypeByArity wide_arity 4) 'CxCore)
                   :exact-stands  (v/ask? kb (list 'arity exactOf 4) 'CxCore)
                   :conflicts     (count (v/conflicts kb))})]))))]
    (testing "the fact's conclusion goes with it, and nothing else does"
      (is (true? (:member-stands result)) "the membership was asserted and stands")
      (is (false? (:arity-gone result)) "the stamped rule's conclusion is withdrawn")
      (is (false? (:mapping-gone result)))
      (is (true? (:exact-stands result)) "an unrelated exact declaration is untouched")
      (is (zero? (:conflicts result))))))

(tu/deftest-kb the-policy-partition-is-order-independent
  ;; Three compatible classifications over one relation, plus a second relation carrying
  ;; the opposing policy.  24 orderings.  The refusal of the fourth is asked separately
  ;; by `the-arity-policy-clash-reports-the-same-refusal-in-either-order`; what this asks
  ;; is that the *accepted* set settles identically however it arrives.
  (let [result
        (one-reading!
         "policy partition"
         (fn [mode]
           (if (= mode :shape)
             [[:exact] [:class] [:kind] [:other]]
             (let [pairOf  (tu/tmp-pred 'pairOf)
                   chainOf (tu/tmp-pred 'chainOf)]
               [{:exact #(v/assert kb (list 'arity pairOf 2) 'CxCore)
                 :class #(v/assert kb (list 'binary_predicate pairOf) 'CxCore)
                 :kind  #(v/assert kb (list 'instance_relation_predicate pairOf) 'CxCore)
                 :other #(v/assert kb (list 'variable_arity_predicate chainOf) 'CxCore)}
                (fn []
                  {:fixed     (v/isa? kb pairOf 'fixed_arity)
                   :binary    (v/isa? kb pairOf 'binary)
                   :bin-pred  (v/isa? kb pairOf 'binary_predicate)
                   :fixed-pred (v/isa? kb pairOf 'fixed_arity_predicate)
                   :kind-mark (v/isa? kb pairOf 'instance_relation_predicate)
                   :not-var   (v/isa? kb pairOf 'variable_arity)
                   :other-var (v/isa? kb chainOf 'variable_arity)
                   :other-fixed (v/isa? kb chainOf 'fixed_arity)
                   ;; a COUNT, not the sentences: every ordering runs on its own fresh
                   ;; terms, so a reading that carried a name would differ 24 ways for
                   ;; the one reason this test is not about
                   :arity-rows (count (v/sentexes-matching kb (list 'arity pairOf '?n)
                                                           'CxCore))
                   :conflicts (count (v/conflicts kb))})]))))]
    (testing "one arity, one policy, whichever spelling arrived first"
      (is (true? (:fixed result)))
      (is (true? (:binary result)))
      (is (true? (:bin-pred result)))
      (is (true? (:fixed-pred result)))
      (is (true? (:kind-mark result)) "the relation_kind mark lands in any order")
      (is (false? (:not-var result)))
      (is (true? (:other-var result)))
      (is (false? (:other-fixed result)))
      (is (= 1 (:arity-rows result)) "the arity table stays single-valued")
      (is (zero? (:conflicts result))))))

(tu/deftest-kb a-predicate-only-classification-is-order-independent-of-the-arity
  ;; The two spellings in both orders, compared on the whole closure rather than on an
  ;; acceptance.  `instance_relation_predicate` genls `binary_predicate`, so stating the
  ;; mark supplies predicate-hood; CxCore therefore declares no argument position for it,
  ;; and the classification is accepted before the kind has been stated by any other
  ;; route.  A `(arg instance_relation_predicate 1 predicate)` row would demand its own
  ;; conclusion and refuse the arity-first order alone.
  ;;
  ;; This is one predicate's property and not an engine-wide one.  `arg`'s refusal half
  ;; convicts on an absence, so a declaration that NARROWS a type the argument already
  ;; holds is still order-sensitive wherever one is written (docs/argtypes.md, "Three
  ;; directions").  Dropping the row removes a declaration that was redundant with a
  ;; `genl` edge; it does not change that reading.
  (let [closure (fn [t] (into #{} (filter #(v/isa? kb t %))
                              '[relation predicate fixed_arity fixed_arity_predicate
                                binary binary_predicate instance_relation_predicate]))]
    (tu/with-terms [pairOne pairTwo]
      (testing "kind first, then the arity"
        (v/assert kb (list 'instance_relation_predicate pairOne) 'CxUniverse)
        (v/assert kb (list 'arity pairOne 2) 'CxUniverse))
      (testing "arity first, then the kind"
        (v/assert kb (list 'arity pairTwo 2) 'CxUniverse)
        (v/assert kb (list 'instance_relation_predicate pairTwo) 'CxUniverse))
      (testing "the same knowledge settles the same way in either order"
        (is (= (closure pairOne) (closure pairTwo)))
        (is (= '#{relation predicate fixed_arity fixed_arity_predicate
                  binary binary_predicate instance_relation_predicate}
               (closure pairOne))
            "and both reach the kind, the arity and the intersection of the two")))))

(tu/deftest-kb an-arity-alone-leaves-the-relation-kind-open
  ;; the entailing reading: the derivation is the subject
  (tu/with-entailing
    ;; What `(arity R N)` says, and what it does not.  It derives `fixed_arity`, so R is a
    ;; `relation`; it says nothing about predicate or function, because two arguments is a
    ;; shape either kind can have.  The converse the generator stamps stops at the
    ;; relation-wide `binary` for exactly that reason (docs/taxonomy.md).
    ;;
    ;; Leaving the kind open is what lets a later classification decide it.  The
    ;; `(arg fixed_arity 1 relation)` floor the marks inherit derives `relation` of what it
    ;; types, and `(disjoint predicate function)`, which the partition of `relation`
    ;; derives, stores a wrong kind as a clash; neither asks about arrival order.
    (tu/with-terms [pairOf someThing someFn]
      (v/assert kb (list 'arity pairOf 2) 'CxUniverse)
      (testing "the arity places the relation without deciding its kind"
        (is (v/isa? kb pairOf 'relation))
        (is (v/isa? kb pairOf 'fixed_arity))
        (is (not (v/isa? kb pairOf 'predicate)))
        (is (not (v/isa? kb pairOf 'function)))
        (is (v/isa? kb pairOf 'binary) "the converse reaches the relation-wide class")
        (is (not (v/isa? kb pairOf 'binary_predicate)) "and stops short of the kind"))
      (testing "a classification then decides it, and carries the intersection with it"
        (is (v/assert kb (list 'instance_relation_predicate pairOf) 'CxUniverse))
        (is (v/isa? kb pairOf 'predicate))
        (is (v/isa? kb pairOf 'binary_predicate))
        (is (not (v/isa? kb pairOf 'function))))
      (testing "a term outside the relation hierarchy is placed in it, by the inherited floor"
        (v/assert kb (list 'thing someThing) 'CxUniverse)
        (v/assert kb (list 'instance_relation_predicate someThing) 'CxUniverse)
        (is (v/isa? kb someThing 'relation))
        (is (v/isa? kb someThing 'predicate)))
      (testing "and a relation of the wrong kind is stored as the contradiction it is"
        (v/assert kb (list 'function someFn) 'CxUniverse)
        (is (tu/stored-in-clash? kb (list 'instance_relation_predicate someFn) 'CxUniverse)
            "predicate against function, not a missing argument type")))))

;; ---- the exact classes derive downward only ------------------------------

(tu/deftest-kb an-arity-and-a-kind-do-not-derive-the-intersection
  ;; Every `genl` edge on the exact classes runs downward: a binary_predicate is binary
  ;; and is a predicate, and nothing states the converse.  CxCore ships no
  ;; `(defnSufficient binary_predicate (and (arity ?x 2) (predicate ?x)))`, because
  ;; `(predicate ?x)` matches every class membership of every predicate by subsumption,
  ;; once per genl route between the two: the six of them cost 748 justifications and
  ;; 600 ms of a 3.2 s starter load for 36 memberships, and a firing re-derived through a
  ;; route that appeared after it leaves the shipped KB holding justifications that depend
  ;; on arrival order.  What a caller needs from the classification is the arity, and the
  ;; relation-wide class answers that.
  (tu/with-terms [pred2 fn2]
    (v/assert kb (list 'predicate pred2) 'CxCore)
    (v/assert kb (list 'arity pred2 2) 'CxCore)
    (testing "the arity reaches the relation-wide class and the policy"
      (is (v/isa? kb pred2 'binary))
      (is (v/isa? kb pred2 'fixed_arity)))
    (testing "and the kind classes stay where their own memberships put them"
      (is (not (v/isa? kb pred2 'binary_predicate)))
      (is (not (v/isa? kb pred2 'fixed_arity_predicate)))
      (is (not (v/isa? kb pred2 'binary_function))))
    (testing "a function is in the same position"
      (v/assert kb (list 'arity fn2 2) 'CxCore)
      (v/assert kb (list 'function fn2) 'CxCore)
      (is (v/isa? kb fn2 'binary))
      (is (not (v/isa? kb fn2 'binary_function))))))

(tu/deftest-kb every-exact-class-spelling-declares-the-arity-it-names
  ;; `tax/exact-arity-classes` is the membership spelling of an arity, and CxCore
  ;; ships nine classes to write one in.  A reader reads each of them, so a wrong-length
  ;; fact is read OUT whichever spelling its author used — including the function ones,
  ;; which no `(arity R n)` sentex need accompany.
  (doseq [[class arity] '[[unary 1] [binary 2] [ternary 3]
                          [unary_predicate 1] [binary_predicate 2] [ternary_predicate 3]
                          [unary_function 1] [binary_function 2] [ternary_function 3]]]
    (let [spelledRelation (tu/tmp-pred)
          ;; `{:chain? false}`: the membership alone, with no rule to derive the (arity R
          ;; n) table entry from it, which is the state the second spelling exists for
          m               (v/assert kb (list class spelledRelation) 'CxUniverse {:chain? false})]
      (is (tu/stored-in-clash? kb (apply list spelledRelation (repeat (inc arity) 'Tom)) 'CxUniverse)
          (str class " declares arity " arity ", so a " (inc arity) "-argument fact is read OUT"))
      (let [h (v/assert kb (apply list spelledRelation (repeat (inc arity) 'Ann)) 'CxUniverse
                        {:strength :monotonic})
            r (first (filter #(contains? (:nogood %) h) (v/conflicts kb)))]
        (is (= [m] (mapv :handle (:grounds r)))
            (str "and a :monotonic one is a hard clash grounded on the stored " class
                 " membership"))))))

(tu/deftest-kb the-arity-bindings-keep-the-strength-they-were-written-at
  ;; The four spellings are on the forced-monotonic roster (docs/taxonomy.md, "Arity"), so
  ;; a binding goes OUT only by retraction and a nogood it grounds never takes it OUT.
  ;; Neither the record nor the class moves from the strength it was written at.
  (tu/with-terms [boundRel varRel]
    (doseq [s [(list 'binary_predicate boundRel) (list 'arity boundRel 2)
               (list 'variable_arity varRel) (list 'arityMin varRel 2)]]
      (let [h (v/assert kb s 'CxUniverse {:strength :default})]
        (is (= [:default :default] [(:strength (v/sentex kb h)) (v/defeat-class kb h)])
            (pr-str s))))))

(tu/deftest-kb two-related-predicates-bound-to-different-lengths-are-a-hard-clash
  ;; Every member is on the roster, so the pair is reported in `conflicts` and every
  ;; member stays believed, whichever arrived last.
  (tu/with-terms [parentRel fatherRel]
    (let [ss [(list 'binary_predicate parentRel) (list 'ternary_predicate fatherRel)
              (list 'genl fatherRel parentRel)]]
      (doseq [s ss] (v/assert kb s 'CxUniverse))
      (is (= [[:arity-descension #{(first ss) (second ss)}]]
             (into [] (comp (filter #(= :arity-descension (:kind %)))
                            (map (juxt :kind #(into #{} (map :sentence) (:sides %)))))
                   (v/conflicts kb))))
      (is (every? #(v/ask? kb % 'CxUniverse) ss)))))

;; ---- the relation_kind metatype is a classification of BINARY relations ---

(tu/deftest-kb the-relation-kind-marks-are-binary-and-say-so
  ;; `instance_relation_predicate` and `type_relation_predicate` are the two halves of
  ;; the `relation_kind` metatype, and the pairing only means something two-place:
  ;; `partOf` holds between two individuals where `partType` holds between two kinds,
  ;; and `typeToInstancePred` links that pair.  Each mark's own comment writes the
  ;; shape — `(?predicate x y)` and `(?predicate T1 T2)` — so the `genl` edge says it.
  (testing "each mark carries the arity its definition writes"
    (doseq [mark '[instance_relation_predicate type_relation_predicate]]
      (is (v/genl? kb mark 'binary_predicate) (str mark " is a binary_predicate"))
      (is (v/genl? kb mark 'binary))
      (is (v/genl? kb mark 'predicate))))
  (testing "so the mark alone classifies a relation, with no separate arity declaration"
    (tu/with-terms [partOfSomething]
      (v/assert kb (list 'instance_relation_predicate partOfSomething) 'CxUniverse)
      (is (v/isa? kb partOfSomething 'binary_predicate))
      (is (= 2 (arity-of kb partOfSomething 'CxUniverse)))
      (is (v/isa? kb partOfSomething 'fixed_arity))))
  (testing "and every shipped member really is binary"
    (doseq [mark '[instance_relation_predicate type_relation_predicate]]
      (let [members (->> (v/query kb (list mark '?p) 'CxInference)
                         (map #(get % '?p))
                         set)
            wrong   (sort-by pr-str (remove #(v/isa? kb % 'binary_predicate) members))]
        (is (seq members) (str mark " has members to check"))
        (is (empty? wrong)
            (str mark " members that are not binary_predicate: " (pr-str wrong))))))
  (testing "a relation of another arity carries neither mark and types its own arguments"
    ;; the four the merge had marked: a chain and a five-place meta-declaration are not
    ;; the two-place claim `relation_kind` splits, and each already declares every
    ;; position it has
    (doseq [relation '[lessThan greaterThan termsRelated interArg]]
      (is (not (v/isa? kb relation 'instance_relation_predicate))
          (str relation " is not a two-place claim"))
      (is (not (v/isa? kb relation 'type_relation_predicate))))
    (is (v/ask? kb '(arg lessThan 1 number) 'CxCore))
    (is (v/ask? kb '(arg lessThan 2 number) 'CxCore))
    (doseq [position (range 1 6)]
      (is (seq (v/sentexes-matching kb (list 'arg 'interArg position '?t) 'CxCore))
          (str "interArg position " position " is declared")))))

;; ---- arityMin as an enforced floor, not documentary vocabulary -----------

(tu/deftest-kb variable-arity-application-is-floored-at-arity-min
  ;; #68: a variable-arity relation reads a chain of any length at or above the minimum
  ;; arityMin states.  An application shorter than the minimum is an arity nogood, as a
  ;; fixed-arity relation's wrong length is; one at or above it is believed.
  (tu/with-terms [chainRel a b c]
    (v/assert kb (list 'variable_arity_predicate chainRel) 'CxCore)
    (let [floor (v/assert kb (list 'arityMin chainRel 2) 'CxCore)]
      (testing "an application shorter than the minimum is read OUT"
        (is (tu/stored-in-clash? kb (list chainRel a) 'CxCore)))
      (testing "and a :monotonic one is a hard clash grounded on the arityMin declaration"
        (let [h (v/assert kb (list chainRel b) 'CxCore {:strength :monotonic})
              r (first (filter #(contains? (:nogood %) h) (v/conflicts kb)))]
          (is (= [floor] (mapv :handle (:grounds r))))))
      (testing "an application at the minimum is believed"
        (v/assert kb (list chainRel a b) 'CxCore)
        (is (v/ask? kb (list chainRel a b) 'CxCore)))
      (testing "a longer application is believed"
        (v/assert kb (list chainRel a b c) 'CxCore)
        (is (v/ask? kb (list chainRel a b c) 'CxCore))))))

(tu/deftest-kb a-variable-arity-relation-with-no-minimum-keeps-its-exemption
  ;; The floor is the minimum's alone: a variable-arity relation the KB gives no arityMin
  ;; reads a chain of any length, including one argument, as it did before the minimum was
  ;; read.
  (tu/with-terms [freeRel a]
    (v/assert kb (list 'variable_arity_predicate freeRel) 'CxCore)
    (is (v/assert kb (list freeRel a) 'CxCore)
        "a one-argument application of an unfloored variable-arity relation is admitted")))

(tu/deftest-kb a-late-minimum-takes-a-short-fact-stored-before-it-out
  ;; the floor is read at the reader, so the arrival order of the minimum and the short
  ;; application decides nothing
  (tu/with-terms [lateRel a]
    (v/assert kb (list 'variable_arity_predicate lateRel) 'CxCore)
    (v/assert kb (list lateRel a) 'CxCore)             ; one argument, no minimum yet
    (is (v/ask? kb (list lateRel a) 'CxCore) "believed while nothing floors it")
    (v/assert kb (list 'arityMin lateRel 2) 'CxCore)
    (is (not (v/ask? kb (list lateRel a) 'CxCore))
        "and read OUT once the minimum arrives")))

(defn- except-shape
  "CxCore's `relationTypeByArity` rule derives `(unary rel)` from `(arity rel 1)`, both
  `:monotonic` in CxUniverse, and two `:default` binary tuples of `rel` sit in each of two
  readers below it, `hid` and `sib`; `hid` excepts the arity, which withdraws the derived
  membership there through the closure.  With `lo`, `(binary rel)`, `(genl lo rel)` and
  `(arity lo 3)` join it.  `[arity unary tuples-at binary]`, `tuples-at` the tuples by
  reader."
  [kb {:keys [rel lo hid sib]}]
  (let [M  {:strength :monotonic}
        _  (doseq [cx [hid sib]] (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse M))
        bi (when lo
             (v/assert kb (list 'genl lo rel) 'CxUniverse M)
             (v/assert kb (list 'arity lo 3) 'CxUniverse M)
             (v/assert kb (list 'binary rel) 'CxUniverse M))
        ar (v/assert kb (list 'arity rel 1) 'CxUniverse M)
        at (into {} (for [cx [hid sib]]
                      [cx (vec (repeatedly 2 #(v/assert kb (list rel (tu/fresh-term :individual 'Xa)
                                                                 (tu/fresh-term :individual 'Xb))
                                                        cx)))]))]
    (v/assert kb (list 'except (list 'sentexHandle ar)) hid M)
    [ar (v/handle-of kb (list 'unary rel) 'CxUniverse) at bi]))

(tu/deftest-kb a-reader-reads-no-binding-it-withdraws-through-an-except
  (tu/with-terms [rel CxHid CxSib]
    (let [[ar un at] (except-shape kb {:rel rel :hid CxHid :sib CxSib})
          out        (fn [cx] (count (remove #(v/believed? kb % cx) (get at cx))))]
      (is (some? un) "the rule derives the membership")
      (is (not-any? #(v/believed? kb % CxHid) [ar un]) "CxHid believes neither binding")
      (is (every? #(v/believed? kb % CxSib) [ar un]))
      (is (zero? (out CxHid)) "a length the reader does not believe convicts no tuple")
      (is (= 2 (out CxSib)) "the sibling convicts its own")
      (testing "the membership stated as well is believed at CxHid, and convicts again"
        (v/assert kb (list 'unary rel) 'CxUniverse {:strength :monotonic})
        (is (v/believed? kb un CxHid))
        (is (= 2 (out CxHid)))))))

(tu/deftest-kb a-reader-reads-a-descension-pair-through-the-bindings-it-believes
  (tu/with-terms [rel lo CxHid CxSib]
    (let [[_ _ _ bi] (except-shape kb {:rel rel :lo lo :hid CxHid :sib CxSib})
          pairs      (fn [cx] (into #{} (comp (filter #(and (v/sees? kb cx (:context %))
                                                            (v/believed? kb (:id %) cx)))
                                              (map #(into #{} (map second) (rest (:sentence %))))
                                              (filter #(= :arity-descension (decide/placed-kind kb %))))
                                    (v/sentexes-with-functor kb 'contradicts)))]
      (is (some #(contains? % bi) (pairs CxHid))
          "CxHid binds rel to two arguments alone, which differs from lo's three")
      (is (empty? (pairs CxSib)) "the sibling sees two lengths of rel, which bind it to none"))))

;; ---- the arity nogoods are placed --------------------------------------------

(tu/deftest-kb an-arity-nogood-is-placed-with-its-binding-as-a-ground
  ;;   CxUniverse  (arity rel 2) monotonic
  ;;     └─ CxB    (rel Xa Xb Xc) default
  ;;          └─ CxV  (variable_arity rel)
  ;; The tuple's nogood is placed at CxB, justified by the binding; CxV reads `rel` as
  ;; variable-arity, which no length binds, so it believes the tuple.
  (tu/with-terms [rel Xa Xb Xc CxB CxV]
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxV CxB) 'CxUniverse)
    (let [bind (v/assert kb (list 'arity rel 2) 'CxUniverse {:strength :monotonic})
          t    (v/assert kb (list rel Xa Xb Xc) CxB)
          T    [(list rel Xa Xb Xc) CxB]
          placed (fn [] (into #{} (for [f '[contradicts defeat]
                                        s (v/sentexes-with-functor kb f)]
                                    (tu/handle-free kb [(:sentence s) (:context s)]))))]
      (testing "the contradicts and the defeat are stored at CxB, the binding a ground"
        (is (= #{[(list 'contradicts T) CxB] [(list 'defeat T) CxB]} (placed)))
        (let [[c] (v/sentexes-with-functor kb 'contradicts)]
          (is (contains? (set (mapcat :antecedents (v/supporting-justifications kb (:id c)))) bind))))
      (testing "no reader decides the tuple, and the defeat hides it at CxB"
        (is (false? (v/believed? kb t CxB))))
      (testing "a reader that reads no length for the functor believes the tuple"
        (v/assert kb (list 'variable_arity rel) CxV {:strength :monotonic})
        (is (true? (v/believed? kb t CxV)))
        (is (false? (v/believed? kb t CxB))))
      (testing "retracting the binding takes the placed sentexes out"
        (v/retract! kb bind)
        (is (empty? (placed)))
        (is (true? (v/believed? kb t CxB)))))))

(tu/deftest-kb a-second-length-unbinds-the-functor-and-an-except-of-it-binds-it-again
  ;;   CxUniverse  (arity rel 2) (arity rel 3) monotonic   (rel Xa Xb Xc Xd) default
  ;;     └─ CxR    (except (arity rel 3))
  ;; Two lengths leave `rel` unbound in CxUniverse, so nothing is placed there and the
  ;; tuple is believed, in every arrival order.  CxR reads `rel` bound to two, so it reads
  ;; the tuple's nogood and does not believe the tuple.
  (tu/with-terms [rel Xa Xb Xc Xd CxR]
    (v/assert kb (list 'genlCx CxR 'CxUniverse) 'CxUniverse)
    (let [M      {:strength :monotonic}
          ss     {:two   #(v/assert kb (list 'arity rel 2) 'CxUniverse M)
                  :three #(v/assert kb (list 'arity rel 3) 'CxUniverse M)
                  :tuple #(v/assert kb (list rel Xa Xb Xc Xd) 'CxUniverse)}
          orders (for [a (keys ss), b (keys ss), c (keys ss) :when (= 3 (count (hash-set a b c)))] [a b c])
          ;; the two lengths clash with each other as well; only the tuple's nogood counts
          ctrs   (fn [t] (count (filter #(some #{(list 'sentexHandle t)} (rest (:sentence %)))
                                        (v/sentexes-with-functor kb 'contradicts))))]
      (is (= #{[0 true]}
             (into #{} (for [order orders]
                         (let [hs (into {} (map (fn [k] [k ((ss k))])) order)
                               r  [(ctrs (:tuple hs)) (v/believed? kb (:tuple hs) 'CxUniverse)]]
                           (run! #(v/retract! kb (hs %)) (reverse order))
                           r))))
          "unbound in CxUniverse in every order: nothing placed, the tuple believed")
      (let [two   ((:two ss))
            three ((:three ss))
            t     ((:tuple ss))]
        (testing "an except of the second length below binds the functor there"
          (let [ex (v/assert kb (list 'except (list 'sentexHandle three)) CxR M)]
            (is (false? (v/believed? kb t CxR)))
            (is (true? (v/believed? kb t 'CxUniverse)))
            (v/retract! kb ex)
            (is (true? (v/believed? kb t CxR)))))
        (testing "the second length leaving binds the functor in CxUniverse"
          (v/retract! kb three)
          (is (pos? (ctrs t)))
          (is (false? (v/believed? kb t 'CxUniverse))))
        (v/retract! kb two)))))
