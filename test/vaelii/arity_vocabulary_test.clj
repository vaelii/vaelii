;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arity-vocabulary-test
  "The relation-wide exact/variable arity partition and its documentary floor vocabulary."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.host.starter :as starter]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- rule-proof
  "The first answer's proof for `goal` at depth 3, and whether its root is a rule whose
  sentence names every symbol in `names`."
  [kb goal names]
  (let [answer (first (v/query kb goal 'CxUniverse {:max-depth 3 :proof? true}))
        root   (first (:proof answer))
        syms   (set (filter symbol? (tree-seq coll? seq (:sentence root))))]
    {:answer (:bindings answer)
     :cites? (boolean (and (= :rule (:via root)) (every? syms names)))
     :syms   syms}))

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
    (is (= 2 (v/relation-arity kb mapping))))
  (doseq [type '[thing animal tangible fixed_arity]]
    (is (v/isa? kb type 'unary_predicate)))
  (doseq [mapping '[predicateTypeByArity functionTypeByArity]]
    (is (v/ask? kb (list 'termsRelated mapping 'relationTypeByArity) 'CxUniverse))
    (is (not (v/genl? kb mapping 'relationTypeByArity))
        (str mapping " is related to the relation-wide mapping, not a specialization of it"))))

(defn- generated-inert
  "The handle of the inert rule a `kind` mapping generates for `type` at `n`, or nil:
  `(implies (and (kind ?relation) (arity ?relation n)) (type ?relation))`."
  [kb kind type n]
  (v/handle-of kb (list 'set/inertRule
                        (list 'implies
                              (list 'and (list kind '?relation) (list 'arity '?relation n))
                              (list type '?relation)))
               'CxUniverse))

(tu/deftest-kb a-predicate-mapping-generates-an-inert-classification
  ;; The predicate mapping generates an INERT rule guarded by the kind: believed and
  ;; documented, run by neither engine.  Run backward it reached (binary ?r) through
  ;; binary_predicate's genl edge while the converse proves (arity ?r 2) from (binary ?r),
  ;; a cycle every (binary ?r) and (arity ?p ?n) query paid for.  The cover argument is
  ;; the `implicit-arity-class` integrity sweep's, and its findings are stated.
  (tu/with-terms [four_place_predicate fourPlacePredicate]
    (v/assert kb (list 'genl four_place_predicate 'fixed_arity_predicate) 'CxUniverse)
    (v/assert kb (list 'predicateTypeByArity four_place_predicate 4) 'CxUniverse)
    (v/assert kb (list 'predicate fourPlacePredicate) 'CxUniverse)
    (v/assert kb (list 'arity fourPlacePredicate 4) 'CxUniverse)
    (let [h (generated-inert kb 'predicate four_place_predicate 4)]
      (is (some? h) "the mapping generates its rule")
      (when h
        (is (v/in? kb h) "believed")
        (is (= #{} (:engines (v/sentex kb h))) "and run by neither engine")))
    (is (empty? (v/query kb (list four_place_predicate fourPlacePredicate) 'CxUniverse
                         {:max-depth 3}))
        "so the class is not proved from the kind and the arity")
    (is (empty? (v/sentexes-matching kb (list four_place_predicate fourPlacePredicate) 'CxUniverse))
        "and no membership is stored")))

(tu/deftest-kb a-function-mapping-generates-an-inert-classification
  (tu/with-terms [four_place_function fourPlaceFn]
    (v/assert kb (list 'genl four_place_function 'fixed_arity_function) 'CxUniverse)
    (v/assert kb (list 'functionTypeByArity four_place_function 4) 'CxUniverse)
    (v/assert kb (list 'function fourPlaceFn) 'CxUniverse)
    (v/assert kb (list 'arity fourPlaceFn 4) 'CxUniverse)
    (let [h (generated-inert kb 'function four_place_function 4)]
      (is (some? h))
      (when h
        (is (v/in? kb h))
        (is (= #{} (:engines (v/sentex kb h))))))
    (is (empty? (v/query kb (list four_place_function fourPlaceFn) 'CxUniverse {:max-depth 3})))
    (is (empty? (v/sentexes-matching kb (list four_place_function fourPlaceFn) 'CxUniverse)))))

(tu/deftest-kb the-shipped-exact-arity-class-rules-are-inert
  (doseq [[kind type n] '[[predicate unary_predicate 1] [predicate binary_predicate 2]
                          [predicate ternary_predicate 3] [function unary_function 1]
                          [function binary_function 2] [function ternary_function 3]]]
    (let [h (generated-inert kb kind type n)]
      (is (some? h) (str "generated: " type))
      (when h
        (is (v/in? kb h))
        (is (= #{} (:engines (v/sentex kb h))) (str type "'s generated rule runs in neither engine")))))
  (tu/with-terms [undeclaredBinary]
    (v/assert kb (list 'predicate undeclaredBinary) 'CxUniverse)
    (v/assert kb (list 'arity undeclaredBinary 2) 'CxUniverse)
    (is (v/ask? kb (list 'binary undeclaredBinary) 'CxUniverse)
        "the relation-wide class is still concluded forward from the arity")
    (is (empty? (v/query kb (list 'binary_predicate undeclaredBinary) 'CxUniverse {:max-depth 3}))
        "while the predicate class waits for the integrity sweep's finding to be stated")))

(tu/deftest-kb the-starter-states-every-exact-arity-class-its-kinds-and-arities-force
  ;; The predicate and function class rules are applied by kb-integrity's
  ;; implicit-arity-class sweep, not by either engine, so each class the starter's kinds
  ;; and arities force is stated: a relation shipped with its arity and kind and without
  ;; its class is a finding here.
  (doseq [ctx (cons 'CxUniverse (seed/layer-contexts "middle"))]
    (let [relations (into #{}
                          (comp (map #(get % '?r))
                                (filter #(and (symbol? %) (not (sx/variable? %)))))
                          (concat (v/query kb '(predicate ?r) ctx {})
                                  (v/query kb '(function ?r) ctx {})))
          report    (v/kb-integrity kb relations ctx {:categories #{:implicit-arity-class}})]
      (is (< 200 (count relations)) "the sweep reads the shipped relations")
      (is (= :audited (:status report))
          (str ctx ": " (pr-str (mapv (juxt :class :term) (:implicit-arity-class report))))))))

(tu/deftest-kb a-predicate-mapping-does-not-classify-a-function
  ;; A predicateTypeByArity fact is not a relationTypeByArity fact, so the relation-wide
  ;; generator generates nothing for it, and a function of that arity stays out of the
  ;; predicate type.
  (tu/with-terms [four_place_predicate fourPlaceFn]
    (v/assert kb (list 'genl four_place_predicate 'fixed_arity_predicate) 'CxUniverse)
    (v/assert kb (list 'predicateTypeByArity four_place_predicate 4) 'CxUniverse)
    (v/assert kb (list 'function fourPlaceFn) 'CxUniverse)
    (v/assert kb (list 'arity fourPlaceFn 4) 'CxUniverse)
    (is (empty? (v/sentexes-matching kb (list 'relationTypeByArity four_place_predicate '?n)
                                     'CxUniverse)))
    (is (empty? (v/query kb (list four_place_predicate fourPlaceFn) 'CxUniverse {:max-depth 3})))))

(tu/deftest-kb the-arity-generator-generates-the-class-from-one-mapping-fact
  ;; One mapping fact mints one forward rule and one backward converse, and both rest on
  ;; it: the arity concludes the class, the class answers the arity at query time without
  ;; storing one, and retracting the fact withdraws each.
  (doseq [mapping-first? [true false]]
    (tu/with-terms [four_place_relation classifiedRelation exactOnlyRelation]
      (v/assert kb (list 'genl four_place_relation 'fixed_arity) 'CxUniverse)
      (let [mapping (list 'relationTypeByArity four_place_relation 4)
            member  (list four_place_relation classifiedRelation)
            h       (if mapping-first?
                      (let [h (v/assert kb mapping 'CxUniverse)]
                        (v/assert kb member 'CxUniverse)
                        h)
                      (do (v/assert kb member 'CxUniverse)
                          (v/assert kb mapping 'CxUniverse)))
            exact   (v/assert kb (list 'arity exactOnlyRelation 4) 'CxUniverse)]
        (testing "the arity concludes the class, and the class proves the arity backward"
          (is (v/ask? kb (list four_place_relation exactOnlyRelation) 'CxUniverse))
          (let [{:keys [answer cites?]} (rule-proof kb (list 'arity classifiedRelation '?n)
                                                    [four_place_relation 'arity])]
            (is (= {'?n 4} answer))
            (is cites?))
          (is (empty? (v/sentexes-matching kb (list 'arity classifiedRelation '?n) 'CxUniverse))
              "and stores none"))
        (testing "and the class rests on the mapping fact"
          (v/retract! kb h)
          (is (v/ask? kb member 'CxUniverse) "the asserted membership stands")
          (is (v/ask? kb (list 'arity exactOnlyRelation 4) 'CxUniverse)
              "the asserted arity stands")
          (is (not (v/ask? kb (list four_place_relation exactOnlyRelation) 'CxUniverse))
              "while the class it derived goes with the rule that derived it")
          (is (empty? (v/query kb (list 'arity classifiedRelation '?n) 'CxUniverse {:max-depth 3}))
              "and so does the converse"))
        (v/retract! kb exact)))))

(tu/deftest-kb the-generated-relation-wide-classification-is-forward-only
  ;; The generator generates `(arity ?r n) → (T ?r)` beside the backward converse
  ;; `(T ?r) → (arity ?r n)`.  Usable backward too, the pair is a backward cycle with no
  ;; ancestor-goal guard to close it: an open `(binary ?r)` query expands into `(arity ?r 2)`
  ;; and back until the depth bound stops it.  The classification still derives forward,
  ;; and only its backward use is a cycle, so it is generated forward-only.
  (doseq [[t n] '[[unary 1] [binary 2] [ternary 3]]]
    (let [rule (list 'implies (list 'arity '?relation n) (list t '?relation))
          h    (v/handle-of kb rule 'CxUniverse)]
      (is (some? h) (str "the generator generates " (pr-str rule)))
      (is (= #{:forward} (:engines (v/sentex kb h)))
          (str "a backward-walkable classification is the cycle: " (pr-str rule))))))

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
        (is (= 2 (v/relation-arity kb chainOf)))
        (is (= [{'?n 2}] (v/query kb (list 'arity chainOf '?n) 'CxUniverse {:max-depth 3}))
            "the converse proves the arity from the class")
        (is (empty? (v/sentexes-matching kb (list 'arity chainOf '?n) 'CxUniverse))
            "and stores none")
        (v/retract! kb h)
        (is (nil? (v/relation-arity kb chainOf)))
        (is (not (v/isa? kb chainOf 'binary))))))
  (testing "an arity no class maps to concludes no class at all"
    (is (v/ask? kb '(arity InstantFn 6) 'CxUniverse))
    (doseq [type '[unary binary ternary quaternary quinary]]
      (is (not (v/isa? kb 'InstantFn type))))))

(tu/deftest-kb the-converse-keeps-the-membership-strength
  ;; The converse is backward, so the arity it proves is never stored: the membership is
  ;; the only sentex, and it keeps the strength it was written at, :default or
  ;; :monotonic, rather than a forced-monotonic arity being stored beside it.  A kind
  ;; class's member is proved by its own converse or by the relation-wide one through the
  ;; class's genl edge, so the proof cites the row or binary.
  (doseq [[strength row] [[:default 'binary] [:monotonic 'binary]
                          [:default 'binary_predicate] [:monotonic 'binary_function]]]
    (tu/with-terms [someRelation]
      (let [h (v/assert kb (list row someRelation) 'CxUniverse {:strength strength})]
        (let [{:keys [answer cites? syms]} (rule-proof kb (list 'arity someRelation '?n) ['arity])]
          (is (= {'?n 2} answer) (str strength " " row ": the arity is proved"))
          (is (and cites? (some (hash-set row 'binary) syms)) "by a converse"))
        (is (empty? (v/sentexes-matching kb (list 'arity someRelation '?n) 'CxUniverse))
            "no arity is stored")
        (is (= strength (:strength (v/sentex kb h)))
            "and the membership keeps its written strength")))))

(tu/deftest-kb exact-arity-and-variable-floors-are-distinct
  (testing "an exact declaration is fixed, not an overloaded floor"
    (is (v/ask? kb '(fixed_arity interArg) 'CxUniverse))
    (is (not (v/ask? kb '(arityMin interArg 5) 'CxUniverse))))
  (testing "the four current variable-arity predicates state only their lower bounds"
    (doseq [relation '[functionCorrespondingPredicate greaterThan lessThan termsRelated]]
      (is (some? (v/handle-of kb (list 'arityMin relation 2) 'CxUniverse))
          (str relation " has an asserted minimum"))
      (is (not (v/isa? kb relation 'binary_predicate))
          (str relation " is not overloaded as exactly binary")))))

(tu/deftest-kb relation-wide-types-own-the-arity-rules
  ;; Fifteen mapping facts: five relation-wide, and five each for the predicate and
  ;; function classes, whose generators guard the generated rule with the kind.
  (doseq [[type arity] '[[unary 1] [binary 2] [ternary 3] [quaternary 4] [quinary 5]]]
    (is (v/ask? kb (list 'relationTypeByArity type arity) 'CxUniverse)))
  (doseq [[type arity] '[[unary_predicate 1] [binary_predicate 2] [ternary_predicate 3]
                         [quaternary_predicate 4] [quinary_predicate 5]]]
    (is (v/ask? kb (list 'predicateTypeByArity type arity) 'CxUniverse)))
  (doseq [[type arity] '[[unary_function 1] [binary_function 2] [ternary_function 3]
                         [quaternary_function 4] [quinary_function 5]]]
    (is (v/ask? kb (list 'functionTypeByArity type arity) 'CxUniverse)))
  (doseq [type '[unary_predicate binary_predicate ternary_predicate
                 quaternary_predicate quinary_predicate
                 unary_function binary_function ternary_function
                 quaternary_function quinary_function]]
    (is (empty? (v/sentexes-matching kb (list 'relationTypeByArity type '?arity) 'CxUniverse))
        (str type " has no relation-wide mapping, which would classify the other kind")))
  (is (v/genl? kb 'unary_predicate 'unary))
  (is (v/genl? kb 'binary_predicate 'binary))
  (is (v/genl? kb 'ternary_predicate 'ternary))
  (is (v/genl? kb 'unary_function 'unary))
  (is (v/genl? kb 'binary_function 'binary))
  (is (v/genl? kb 'ternary_function 'ternary))
  (is (v/genl? kb 'quaternary_predicate 'quaternary))
  (is (v/genl? kb 'quinary_predicate 'quinary))
  (is (v/genl? kb 'quaternary_function 'quaternary))
  (is (v/genl? kb 'quinary_function 'quinary))
  (doseq [type '[quaternary quinary]]
    (is (v/genl? kb type 'fixed_arity)))
  (doseq [type '[unary_predicate binary_predicate ternary_predicate
                 quaternary_predicate quinary_predicate]]
    (is (v/genl? kb type 'fixed_arity_predicate)))
  (doseq [type '[unary_function binary_function ternary_function
                 quaternary_function quinary_function]]
    (is (v/genl? kb type 'fixed_arity_function)))
  (is (v/isa? kb 'parentOf 'fixed_arity_predicate))
  (is (v/isa? kb 'MotherFn 'fixed_arity_function)))

(defn- conflict-between?
  "Whether `conflicts` reports one nogood whose members are exactly `a` and `b`."
  [kb a b]
  (let [ha (v/handle-of kb a 'CxUniverse)
        hb (v/handle-of kb b 'CxUniverse)]
    (boolean (and ha hb (some #(= #{ha hb} (set (:nogood %))) (v/conflicts kb))))))

(tu/deftest-kb disjoint-arity-policies-are-an-irreducible-conflict
  ;; `fixed_arity` and `variable_arity` are both forced-monotonic, so the
  ;; disjoint pair has no member to defeat: both stay believed and `conflicts` names the
  ;; pair, the same in either order
  (doseq [[first-policy second-policy] '[[fixed_arity variable_arity]
                                         [variable_arity fixed_arity]]]
    (tu/with-terms [candidateRelation]
      (v/assert kb (list first-policy candidateRelation) 'CxUniverse)
      (v/assert kb (list second-policy candidateRelation) 'CxUniverse)
      (is (v/ask? kb (list 'fixed_arity candidateRelation) 'CxUniverse)
          (str second-policy " after " first-policy ": fixed_arity stays believed"))
      (is (v/ask? kb (list 'variable_arity candidateRelation) 'CxUniverse))
      (is (conflict-between? kb (list 'fixed_arity candidateRelation)
                             (list 'variable_arity candidateRelation))
          "and the pair is reported as a conflict")))
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
    ;; argument's type rather than for the policy it contradicts.  CxUniverse declares the
    ;; position on fixed_arity and variable_arity alone for that reason.
    (doseq [[first-class second-class] '[[variable_arity binary_predicate]
                                         [binary_predicate variable_arity]
                                         [variable_arity_predicate unary_predicate]
                                         [variable_arity unary_function]
                                         [unary_function variable_arity]]]
      (tu/with-terms [candidateRelation]
        (v/assert kb (list first-class candidateRelation) 'CxUniverse)
        (is (tu/stored-in-clash? kb (list second-class candidateRelation) 'CxUniverse)
            (str second-class " after " first-class " is stored as a disjoint clash"))))
    (testing "a relation of the wrong kind clashes too, by the genl edges, and two
            forced-monotonic kinds are an irreducible conflict, the same in either order"
      (doseq [[first-kind second-kind] '[[predicate unary_function]
                                         [unary_function predicate]]]
        (tu/with-terms [somePredicate]
          (v/assert kb (list first-kind somePredicate) 'CxUniverse)
          (v/assert kb (list second-kind somePredicate) 'CxUniverse)
          (is (v/ask? kb (list 'predicate somePredicate) 'CxUniverse)
              (str second-kind " after " first-kind ": predicate stays believed"))
          (is (v/ask? kb (list 'unary_function somePredicate) 'CxUniverse))
          (is (conflict-between? kb (list 'predicate somePredicate)
                                 (list 'unary_function somePredicate))
              "and the pair is reported as a conflict"))))
    (testing "and an argument that is no relation at all derives fixed_arity's own type,
            relation, from a forced-monotonic membership, which defeats the :default type it
            clashes with"
      (doseq [[first-type second-type] '[[animal fixed_arity_predicate]
                                         [fixed_arity_predicate animal]]]
        (tu/with-terms [someIndividual]
          (v/assert kb (list first-type someIndividual) 'CxUniverse)
          (v/assert kb (list second-type someIndividual) 'CxUniverse)
          (is (v/ask? kb (list 'relation someIndividual) 'CxUniverse)
              "the position declared on fixed_arity descends to its specializations")
          (is (not (v/ask? kb (list 'animal someIndividual) 'CxUniverse))
              (str second-type " after " first-type ": animal is the loser"))
          (is (= :defeated (:reason (v/why-not kb (list 'animal someIndividual) 'CxUniverse)))))))))

(tu/deftest-kb relation-wide-exact-classes-clash-with-each-other
  (doseq [[first-type second-type] '[[unary binary] [binary unary]
                                     [unary ternary] [ternary unary]
                                     [binary ternary] [ternary binary]
                                     [unary quaternary] [quinary unary]
                                     [binary quinary] [quaternary binary]
                                     [ternary quaternary] [quinary ternary]
                                     [quaternary quinary] [quinary quaternary]]]
    (tu/with-terms [candidateRelation]
      (v/assert kb (list first-type candidateRelation) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list second-type candidateRelation) 'CxUniverse)
          (str second-type " after " first-type " is stored as a disjoint clash"))))
  (tu/with-terms [compatibleRelation]
    (v/assert kb (list 'unary compatibleRelation) 'CxUniverse)
    (is (v/assert kb (list 'fixed_arity compatibleRelation) 'CxUniverse)
        "an exact class and its fixed policy are compatible")))

(tu/deftest-kb four-and-five-argument-relations-have-exact-classes
  (testing "an arity of four or five concludes its relation-wide class"
    (doseq [[type arity] '[[quaternary 4] [quinary 5]]]
      (tu/with-terms [wideRelation]
        (let [h (v/assert kb (list 'arity wideRelation arity) 'CxUniverse)]
          (is (v/isa? kb wideRelation type) (str "arity " arity " concludes " type))
          (is (v/isa? kb wideRelation 'fixed_arity))
          (v/retract! kb h)
          (is (not (v/isa? kb wideRelation type)))))))
  (testing "a membership of a four- or five-argument class is read as the arity"
    (doseq [[type arity] '[[quaternary 4] [quinary 5]
                           [quaternary_predicate 4] [quinary_predicate 5]]]
      (tu/with-terms [wideRelation]
        (let [h (v/assert kb (list type wideRelation) 'CxUniverse)]
          (is (= arity (v/relation-arity kb wideRelation)) (str type " reads as " arity))
          (v/retract! kb h))))
    (doseq [[type arity] '[[quaternary_function 4] [quinary_function 5]]]
      (tu/with-terms [WideFn]
        (let [h (v/assert kb (list type WideFn) 'CxUniverse)]
          (is (= arity (v/relation-arity kb WideFn)) (str type " reads as " arity))
          (is (v/isa? kb WideFn 'function))
          (v/retract! kb h)))))
  (testing "the shipped four- and five-argument predicates carry their kind's class"
    (doseq [[predicate type] '[[calendarDay quaternary_predicate]
                               [measureRangeInUnit quaternary_predicate]
                               [predExistsInstancePlaceholder quaternary_predicate]
                               [predInstanceExistsPlaceholder quaternary_predicate]
                               [interArg quinary_predicate]
                               [predAllExistsPlaceholder quinary_predicate]
                               [predExistsAllPlaceholder quinary_predicate]]]
      (is (v/isa? kb predicate type) (str predicate " is " type))))
  (testing "an arity above five has no named class"
    (is (v/isa? kb 'calendarInstant 'fixed_arity_predicate))
    (is (= 7 (v/relation-arity kb 'calendarInstant)))
    (doseq [type '[unary binary ternary quaternary quinary]]
      (is (not (v/isa? kb 'calendarInstant type))))))

(def ^:private arity-classes
  "The relation-wide classes an arity is read from: the five exact ones and the variable
  policy."
  '[unary binary ternary quaternary quinary variable_arity])

(tu/deftest-kb every-shipped-predicate-declares-an-arity-class
  ;; A predicate is read by its arity, so every shipped one is in an exact class or is
  ;; variable_arity.  A fixed arity above five has no named class, and its fixed_arity
  ;; membership with its (arity P n) stands in for one.
  (testing "every predicate is in an arity class, or is fixed_arity above five arguments"
    (is (empty? (for [term (v/terms kb)
                      :when (and (symbol? term)
                                 (v/isa? kb term 'predicate)
                                 (not-any? #(v/isa? kb term %) arity-classes)
                                 (not (and (v/isa? kb term 'fixed_arity)
                                           (some-> (v/relation-arity kb term) (> 5)))))]
                  term))))
  (testing "every term carrying an argument or arity declaration is a relation"
    (is (empty? (for [[pattern] '[[(arg ?p ?n ?t)] [(genlArg ?p ?n ?t)] [(quotedArg ?p ?n ?t)]
                                  [(arity ?p ?n)] [(arityMin ?p ?n)]]
                      s (v/sentexes-matching kb pattern '?ctx)
                      :let [term (second (:sentence s))]
                      :when (and (symbol? term) (not (v/isa? kb term 'relation)))]
                  term)))))

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
                              [PredExistsInstanceFn ternary_function]
                              [PredInstanceExistsFn ternary_function]
                              [PredAllExistsFn quaternary_function]
                              [PredExistsAllFn quaternary_function]]]
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
    (is (v/isa? kb 'interArg 'at_least_ternary)))
  (testing "a binary_predicate member is at least binary through binary's genl edge"
    ;; doneBy is declared only (binary_predicate doneBy): binary_predicate ⊂ binary ⊂
    ;; at_least_binary
    (is (v/isa? kb 'doneBy 'at_least_binary))
    (is (not (v/isa? kb 'doneBy 'at_least_ternary))))
  (testing "a unary relation is at neither floor"
    (is (not (v/isa? kb 'person 'at_least_binary))))
  (testing "the ternary floor specializes the binary floor"
    (is (v/genl? kb 'at_least_ternary 'at_least_binary))))

(tu/deftest-kb four-and-five-argument-floors-follow-the-ternary-floor
  (testing "each floor specializes the one below it, and each exact class reaches its floor"
    (is (v/genl? kb 'at_least_quaternary 'at_least_ternary))
    (is (v/genl? kb 'at_least_quinary 'at_least_quaternary))
    (is (v/genl? kb 'quaternary 'at_least_quaternary))
    (is (v/genl? kb 'quinary 'at_least_quinary)))
  (testing "a shipped exact arity reaches its floor and no higher one"
    (is (v/isa? kb 'calendarDay 'at_least_quaternary))
    (is (not (v/isa? kb 'calendarDay 'at_least_quinary)))
    (is (v/isa? kb 'interArg 'at_least_quinary))
    (is (not (v/isa? kb 'arg 'at_least_quaternary))))
  (testing "each floor is disjoint from every exact class below it"
    (doseq [[floor below] '[[at_least_binary [unary]]
                            [at_least_ternary [unary binary]]
                            [at_least_quaternary [unary binary ternary]]
                            [at_least_quinary [unary binary ternary quaternary]]]
            class below]
      (is (v/disjoint? kb floor class) (str floor " and " class)))
    (is (not (v/disjoint? kb 'at_least_ternary 'quinary))))
  (testing "an arity above five reaches the five-argument floor through the arity rules"
    (is (v/isa? kb 'calendarInstant 'at_least_quinary)))
  (testing "a minimum of four or five derives the floors up to it"
    (doseq [[minimum floors non-floors] '[[4 [at_least_ternary at_least_quaternary] [at_least_quinary]]
                                          [5 [at_least_quaternary at_least_quinary] []]]]
      (tu/with-terms [longChainOf]
        (v/assert kb (list 'variable_arity_predicate longChainOf) 'CxUniverse)
        (let [h (v/assert kb (list 'arityMin longChainOf minimum) 'CxUniverse)]
          (doseq [floor floors]
            (is (v/isa? kb longChainOf floor) (str "minimum " minimum " derives " floor)))
          (doseq [floor non-floors]
            (is (not (v/isa? kb longChainOf floor)) (str "minimum " minimum " stops below " floor)))
          (v/retract! kb h)
          (is (not (v/isa? kb longChainOf 'at_least_quaternary))))))))

(def ^:private admits-argnum-definition
  "admitsArgnum's defining rules as CxUniverse states them, backward."
  '[(implies (relation ?relation) (admitsArgnum ?relation 1))
    (implies (at_least_binary ?relation) (admitsArgnum ?relation 2))
    (implies (at_least_ternary ?relation) (admitsArgnum ?relation 3))
    (implies (at_least_quaternary ?relation) (admitsArgnum ?relation 4))
    (implies (at_least_quinary ?relation) (admitsArgnum ?relation 5))
    (implies (and (unbounded_arity ?relation) (positive_integer ?position))
             (admitsArgnum ?relation ?position))
    (implies (and (bounded_arity ?relation) (arityMax ?relation ?max) (positive_integer ?position)
                  (not (greaterThan ?position ?max)))
             (admitsArgnum ?relation ?position))
    (implies (and (arity ?relation ?arity) (positive_integer ?position)
                  (not (greaterThan ?position ?arity)))
             (admitsArgnum ?relation ?position))])

(tu/deftest-kb admits-argnum-states-its-definition-as-backward-rules
  (testing "each defining rule is stored in CxUniverse, believed, and run backward only"
    (doseq [r admits-argnum-definition]
      (let [h (v/handle-of kb (list 'set/backwardRule r) 'CxUniverse)]
        (is (some? h) (str "stored: " (pr-str r)))
        (when h
          (is (v/in? kb h))
          (is (= #{:backward} (:engines (v/sentex kb h))))))))
  (testing "and none forward-chains: no admitsArgnum fact is stored"
    (is (empty? (v/sentexes-matching kb '(admitsArgnum ?r ?n) 'CxWell))))
  (testing "while the prover answers as it did"
    (is (v/ask? kb '(admitsArgnum parentOf 2) 'CxWell))
    (is (not (v/ask? kb '(admitsArgnum parentOf 3) 'CxWell)))
    (is (v/ask? kb '(admitsArgnum partition 40) 'CxWell))))

(defn- cited-rules
  "The rule handles a `query` proof tree cites, at any depth."
  [tree]
  (cond (map? tree)        (cond-> (into #{} (mapcat cited-rules) (:because tree))
                             (= :rule (:via tree)) (conj (:rule tree)))
        (sequential? tree) (into #{} (mapcat cited-rules) tree)
        :else              #{}))

(defn- admitted-with-proofs
  "Each answer to the admitsArgnum `goal`, as its bindings mapped to the rule handles its
  proof cites."
  [kb goal]
  (into {} (map (juxt :bindings (comp cited-rules :proof)))
        (v/query kb goal 'CxUniverse {:max-depth 1 :proof? true})))

(tu/deftest-kb admits-argnum-answers-are-justified-by-its-definition-rules
  ;; The prover answers a ground (admitsArgnum R n).  A goal with the relation or the
  ;; position open is answered by the definition rules, and each answer's proof cites the
  ;; rule that derives it.  The six relations below differ in their arity signature.
  (let [[relation-rule binary-rule ternary-rule quaternary-rule quinary-rule unbounded-rule]
        (mapv #(v/handle-of kb (list 'set/backwardRule %) 'CxUniverse) admits-argnum-definition)
        cites? (fn [answers bindings rule] (contains? (get answers bindings #{}) rule))]
    (testing "doneBy, a binary_predicate: 1 through relation, 2 through at_least_binary, no 3"
      (let [answers (admitted-with-proofs kb '(admitsArgnum doneBy ?n))]
        (is (cites? answers '{?n 1} relation-rule))
        (is (cites? answers '{?n 2} binary-rule))
        (is (not (contains? answers '{?n 3}))))
      (is (not (v/ask? kb '(admitsArgnum doneBy 3) 'CxUniverse))))
    (testing "arg, a ternary_predicate: 3 through at_least_ternary, no 4"
      (let [answers (admitted-with-proofs kb '(admitsArgnum arg ?n))]
        (is (cites? answers '{?n 1} relation-rule))
        (is (cites? answers '{?n 2} binary-rule))
        (is (cites? answers '{?n 3} ternary-rule))
        (is (not (contains? answers '{?n 4}))))
      (is (not (v/ask? kb '(admitsArgnum arg 4) 'CxUniverse))))
    (testing "calendarDay, a quaternary_predicate: 4 through at_least_quaternary, no 5"
      (let [answers (admitted-with-proofs kb '(admitsArgnum calendarDay ?n))]
        (is (cites? answers '{?n 3} ternary-rule))
        (is (cites? answers '{?n 4} quaternary-rule))
        (is (not (contains? answers '{?n 5}))))
      (is (not (v/ask? kb '(admitsArgnum calendarDay 5) 'CxUniverse))))
    (testing "interArg, a quinary_predicate: 5 through at_least_quinary, no 6"
      (let [answers (admitted-with-proofs kb '(admitsArgnum interArg ?n))]
        (is (cites? answers '{?n 4} quaternary-rule))
        (is (cites? answers '{?n 5} quinary-rule))
        (is (not (contains? answers '{?n 6}))))
      (is (not (v/ask? kb '(admitsArgnum interArg 6) 'CxUniverse))))
    (testing "functionCorrespondingPredicate, bounded variable arity 2 to 3: 1 and 2"
      (let [answers (admitted-with-proofs kb '(admitsArgnum functionCorrespondingPredicate ?n))]
        (is (cites? answers '{?n 1} relation-rule))
        (is (cites? answers '{?n 2} binary-rule))))
    (testing "different, unbounded variable arity: 2 through at_least_binary, 7 through unbounded_arity"
      (is (cites? (admitted-with-proofs kb '(admitsArgnum different ?n)) '{?n 2} binary-rule))
      (is (cites? (admitted-with-proofs kb '(admitsArgnum ?r 7)) '{?r different} unbounded-rule)))))

(tu/deftest-kb admits-argnum-answers-the-position-query
  ;; #68: (admitsArgnum R n) is answered at query time from R's declared arity and
  ;; variable-arity mark — not from a finite rule set — so the declared vocabulary now
  ;; carries an answer.
  (is (v/isa? kb 'admitsArgnum 'binary_predicate))
  (is (v/ask? kb '(arg admitsArgnum 1 relation) 'CxUniverse))
  (is (v/ask? kb '(arg admitsArgnum 2 positive_integer) 'CxUniverse))
  (testing "a fixed-arity relation admits one through its arity and no higher position"
    (tu/with-terms [ternaryRel]
      (v/assert kb (list 'ternary_predicate ternaryRel) 'CxUniverse)
      (doseq [n [1 2 3]]
        (is (v/ask? kb (list 'admitsArgnum ternaryRel n) 'CxUniverse)
            (str "position " n " is admitted")))
      (is (not (v/ask? kb (list 'admitsArgnum ternaryRel 4) 'CxUniverse))
          "the first position above the arity is not admitted")))
  (testing "a variable-arity relation admits its guaranteed positions and every higher one"
    (doseq [n [1 2 3 212]]                                ; lessThan is variable_arity, arityMin 2
      (is (v/ask? kb (list 'admitsArgnum 'lessThan n) 'CxUniverse)
          (str "variable-arity position " n " is admitted"))))
  (testing "zero and negative positions never admit"
    (is (not (v/ask? kb '(admitsArgnum lessThan 0) 'CxUniverse)))
    (is (not (v/ask? kb '(admitsArgnum lessThan -1) 'CxUniverse))))
  (testing "a relation bound to no length of its own admits through the length it inherits"
    (tu/with-terms [relP relQ Xa Xb Xc]
      (v/assert kb (list 'arity relQ 2) 'CxUniverse)
      (v/assert kb (list 'genl relP relQ) 'CxUniverse)
      (let [t (v/assert kb (list relP Xa Xb Xc) 'CxUniverse)]
        (is (= [true true false] (mapv #(v/ask? kb (list 'admitsArgnum relP %) 'CxUniverse) [1 2 3])))
        (is (false? (v/believed? kb t 'CxUniverse)) "the three-place tuple breaks the length relQ binds"))))
  (testing "an unclassified relation's positions stay unknown, not admitted"
    (tu/with-terms [unknownRel]
      (v/assert kb (list 'predicate unknownRel) 'CxUniverse)
      (is (not (v/ask? kb (list 'admitsArgnum unknownRel 1) 'CxUniverse))
          "open-world: no declared arity and no variable mark means no proven position"))))

(tu/deftest-kb admits-argnum-and-the-position-census-answer-one-question
  ;; #68 single source: admitsArgnum and checks/arg-position-problem read one decision,
  ;; provers/admits-position?, so a position the constraint census refuses on a relation is
  ;; exactly one admitsArgnum does not prove, and one it allows is one admitsArgnum proves.
  (tu/with-terms [censusRel]
    (v/assert kb (list 'ternary_predicate censusRel) 'CxUniverse)
    (testing "a position within the arity: the census admits the constraint, the query proves it"
      (is (v/assert kb (list 'arg censusRel 3 'thing) 'CxUniverse))
      (is (v/ask? kb (list 'admitsArgnum censusRel 3) 'CxUniverse)))
    (testing "a position past the arity: the census refuses the constraint, the query denies it"
      (let [e (try (v/assert kb (list 'arg censusRel 4 'thing) 'CxUniverse) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :arg-position (:type (ex-data e)))
            "the constraint census refuses argument 4 of a ternary relation")
        (is (not (v/ask? kb (list 'admitsArgnum censusRel 4) 'CxUniverse))
            "and admitsArgnum does not prove the position it refused")))))

(tu/deftest-kb admits-argnum-parity-for-functions
  ;; a variable-arity function admits every positive position, like the predicate case; a
  ;; fixed-arity function alone invents no numeric arity, so its positions stay unknown.
  (tu/with-terms [ChainFn PlainFn]
    (v/assert kb (list 'variable_arity_function ChainFn) 'CxUniverse)
    (v/assert kb (list 'arityMin ChainFn 2) 'CxUniverse)
    (testing "a variable-arity function admits every positive position"
      (doseq [n [1 2 3 9]]
        (is (v/ask? kb (list 'admitsArgnum ChainFn n) 'CxUniverse))))
    (v/assert kb (list 'fixed_arity_function PlainFn) 'CxUniverse)
    (testing "a fixed-arity function invents no numeric arity — its positions stay unknown"
      (is (not (v/ask? kb (list 'admitsArgnum PlainFn 1) 'CxUniverse))
          "the numeric arity table is predicate-specific, so a function has no proven position"))))

(tu/deftest-kb admits-argnum-reads-a-variable-arity-release-stated-in-any-context
  (tu/with-terms [CxBelow relP]
    (v/assert kb (list 'genlCx CxBelow 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'arity relP 2) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'variable_arity relP) CxBelow {:strength :monotonic})
    (doseq [cx ['CxUniverse CxBelow]
            n  [1 5]]
      (is (v/ask? kb (list 'admitsArgnum relP n) cx) (str "position " n " at " cx)))))

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
    (is (some? (v/handle-of kb '(partition relation fixed_arity variable_arity) 'CxUniverse))
        "the partition is declared in KB data")))

;; ---- the declarations the merge added to the shipped functions ------------

(tu/deftest-kb the-six-argument-function-declares-every-field
  ;; `(arity InstantFn 6)` and the six `(arg InstantFn N integer)` are assertible at all
  ;; only because the argument vocabulary's first position is `relation` rather than
  ;; `predicate`: a function could carry neither before.  Six is not a relation-wide
  ;; exact class, so `InstantFn` is `fixed_arity_function` by declaration and reaches no
  ;; `unary` / `binary` / `ternary`.
  (is (v/ask? kb '(arity InstantFn 6) 'CxUniverse))
  (is (v/isa? kb 'InstantFn 'fixed_arity))
  (doseq [type '[unary binary ternary]]
    (is (not (v/isa? kb 'InstantFn type))
        (str "six arguments do not classify InstantFn as " type)))
  (doseq [position (range 1 7)]
    (is (v/ask? kb (list 'arg 'InstantFn position 'integer) 'CxUniverse)
        (str "field " position " is declared an integer")))
  (testing "and the ternary calendar constructor carries its class, not six arg rows"
    (is (v/isa? kb 'DayFn 'ternary_function))
    (is (= 3 (v/relation-arity kb 'DayFn)))))

(tu/deftest-kb the-relation-wide-declarations-are-what-the-inert-tuple-test-reads
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

(tu/deftest-kb a-monotonic-instance-relation-membership-binds-two-arguments
  ;; CxUniverse's `(genl instance_relation_predicate binary_predicate)` is :monotonic, so the
  ;; membership binds as `(binary_predicate P)` does; a :default one binds nothing
  (tu/with-terms [likesRel hatesRel A B C]
    (v/assert kb (list 'instance_relation_predicate likesRel) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'instance_relation_predicate hatesRel) 'CxUniverse)
    (is (tu/stored-in-clash? kb (list likesRel A B C) 'CxUniverse))
    (is (not (tu/stored-in-clash? kb (list hatesRel A B C) 'CxUniverse)))))

(defn- class-support
  "The antecedent sentences of each `arityClass` justification of `(C x)` in CxUniverse,
  as a set of sets; nil when `(C x)` is not stored."
  [kb c x]
  (when-some [h (v/handle-of kb (list c x) 'CxUniverse)]
    (into #{} (comp (filter #(= 'arityClass (:informant %)))
                    (map #(into #{} (map (fn [a] (:sentence (v/sentex kb a)))) (:antecedents %))))
          (v/supporting-justifications kb h))))

(tu/deftest-kb a-monotonic-metatype-route-stores-the-class-membership
  ;; The membership and each edge up to the exact class are `:monotonic`, so the engine
  ;; stores `(binary_predicate P)` justified by them, in either arrival order and across
  ;; a recover, and withdraws it when the membership or an edge leaves.
  (tu/with-terms [rel_kind soft_kind likesRel hatesRel fearsRel]
    (let [m    (list rel_kind likesRel)
          edge (list 'genl rel_kind 'binary_predicate)
          want #{#{m edge}}]
      (doseq [order [[m edge] [edge m]]]
        (let [hs (mapv #(v/assert kb % 'CxUniverse {:strength :monotonic}) order)]
          (is (= want (class-support kb 'binary_predicate likesRel)) (pr-str order))
          (v/recover kb)
          (is (= want (class-support kb 'binary_predicate likesRel)) "after a recover")
          (is (= #{m edge}
                 (into #{} (comp (mapcat :because) (map :sentence))
                       (:support (v/why kb (v/handle-of kb (list 'binary_predicate likesRel)
                                                        'CxUniverse)))))
              "why names the membership and the edge")
          (v/retract! kb (peek hs))
          (is (not (v/ask? kb (list 'binary_predicate likesRel) 'CxUniverse))
              (str "withdrawn with " (pr-str (peek order))))
          (v/retract! kb (first hs))))
      (testing "a :default membership or edge derives nothing"
        (v/assert kb (list rel_kind hatesRel) 'CxUniverse)
        (v/assert kb edge 'CxUniverse {:strength :monotonic})
        (v/assert kb (list soft_kind fearsRel) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list 'genl soft_kind 'binary_predicate) 'CxUniverse)
        (is (= [nil nil] (mapv #(class-support kb 'binary_predicate %) [hatesRel fearsRel])))))))

(tu/deftest-kb a-derived-membership-raised-to-monotonic-stores-the-class-membership-in-either-order
  ;; Two forward rules derive `(rel_kind P)`, one from a `:default` premise and one from a
  ;; `:monotonic` one.  With the `:default` firing first, the membership reaches
  ;; `:monotonic` by a relabel, and the class membership is stored as in the other order.
  (tu/with-terms [rel_kind src_kind src2_kind likesRel]
    (let [m     {:strength :monotonic}
          base  [(list 'genl rel_kind 'binary_predicate)
                 (list 'set/forwardRule (list 'implies (list src_kind '?x) (list rel_kind '?x)))
                 (list 'set/forwardRule (list 'implies (list src2_kind '?x) (list rel_kind '?x)))]
          soft  [(list src_kind likesRel) {:strength :default}]
          hard  [(list src2_kind likesRel) m]]
      (doseq [order [[soft hard] [hard soft]]]
        (let [hs (into (mapv #(v/assert kb % 'CxUniverse m) base)
                       (map (fn [[s o]] (v/assert kb s 'CxUniverse o)) order))]
          (is (some? (class-support kb 'binary_predicate likesRel)) (pr-str (map first order)))
          (run! #(v/retract! kb %) (rseq hs)))))))

(tu/deftest-kb a-class-sync-reads-each-class-s-watched-rules-once
  ;; Each class membership the sync places posts its class's re-check trigger, and the sync
  ;; reads the watched rules for one class once however many memberships it places.  The
  ;; edge arriving last makes one sync place the class membership of every relation.
  (let [reads-at (fn [n]
                   (tu/with-terms [rel_kind cond_kind p_in q_out]
                     (let [m     {:strength :monotonic}
                           rels  (repeatedly n #(tu/tmp-pred "likesRel"))
                           calls (atom 0)
                           in?   (atom false)
                           sync  chain/sync-arity-classes!
                           on    reads/watched-rules-on]
                       (v/assert kb (list 'exceptWhen (list cond_kind '?x)
                                          (list 'implies (list p_in '?x) (list q_out '?x)))
                                 'CxUniverse)
                       (doseq [r rels] (v/assert kb (list rel_kind r) 'CxUniverse m))
                       (with-redefs [chain/sync-arity-classes! (fn [kb hs]
                                                                 (reset! in? true)
                                                                 (try (sync kb hs) (finally (reset! in? false))))
                                     reads/watched-rules-on   (fn [idx pred]
                                                                (when @in? (swap! calls inc))
                                                                (on idx pred))]
                         (v/assert kb (list 'genl rel_kind 'binary_predicate) 'CxUniverse m))
                       [(count (filter #(v/handle-of kb (list 'binary_predicate %) 'CxUniverse) rels))
                        @calls])))]
    (let [[[placed2 calls2] [placed6 calls6]] [(reads-at 2) (reads-at 6)]]
      (is (= [2 6] [placed2 placed6]))
      (is (pos? calls2))
      (is (= calls2 calls6)))))

(tu/deftest-kb a-partition-edge-on-the-route-stores-the-class-membership-in-either-order
  ;; `(partition whole_kind a_kind b_kind)` installs `(genl a_kind whole_kind)` with no
  ;; `genl` sentence, so the route reads the partition as the edge's supporter.  Forced to
  ;; the constraint-only reading: the entailing one also mints a `genl` sentence.
  (tu/without-entailing
   (tu/with-terms [whole_kind a_kind b_kind likesRel]
     (let [m    {:strength :monotonic}
           top  (list 'genl whole_kind 'binary_predicate)
           part (list 'partition whole_kind a_kind b_kind)
           mem  (list a_kind likesRel)
           want #{#{mem part top}}]
       (doseq [order [[top mem part] [top part mem]]]
         (let [hs (mapv #(v/assert kb % 'CxUniverse m) order)]
           (is (= want (class-support kb 'binary_predicate likesRel)) (pr-str order))
           (v/retract! kb (v/handle-of kb part 'CxUniverse))
           (is (not (v/ask? kb (list 'binary_predicate likesRel) 'CxUniverse)) "withdrawn with the partition")
           (run! #(v/retract! kb %) (remove #{(v/handle-of kb part 'CxUniverse)} (rseq hs)))))
       (testing "a partition raised to :monotonic"
         (let [hs [(v/assert kb top 'CxUniverse m) (v/assert kb mem 'CxUniverse m)
                   (v/assert kb part 'CxUniverse)]]
           (is (nil? (class-support kb 'binary_predicate likesRel)))
           (v/assert kb part 'CxUniverse m)
           (is (= want (class-support kb 'binary_predicate likesRel)))
           (run! #(v/retract! kb %) (rseq hs))))))))

(tu/deftest-kb the-shipped-disjoint-metatypes-bind-one-argument
  ;; each is a `:monotonic` disjoint_metatype, which reaches unary_predicate through the
  ;; `:monotonic` edges by at_least_metatype, so the position check refuses a second argument
  (doseq [t '[type_type_by_order stuff_type_by_state_of_matter stuff_type_by_substance]]
    (is (= 1 (v/relation-arity kb t)) (str t)))
  (is (= :arg-position
         (:type (ex-data (try (v/assert kb '(arg type_type_by_order 2 thing) 'CxUniverse) nil
                              (catch clojure.lang.ExceptionInfo e e)))))))

(tu/deftest-kb the-ternary-floor-derives-and-withdraws-with-its-minimum
  ;; No shipped relation states a minimum above two, so the `at_least_ternary`
  ;; rule fires on nothing in CxUniverse.  It is stated vocabulary either way, and this is
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
    (is (empty? (v/sentexes-matching kb '(arityMin interArg ?n) 'CxUniverse)))
    (is (v/ask? kb '(arity interArg 5) 'CxUniverse))))

(tu/deftest-kb every-engine-term-s-shape-states-the-length-the-shipped-kb-binds
  ;; an engine term's length is its `:shape` and no KB binding moves it, so a shipped
  ;; `arity` or `arityMin` the shape disagrees with states a length no reader applies
  (let [stated (fn [p q] (into #{} (map #(nth (:sentence %) 2))
                               (v/sentexes-matching kb (list p q '?n) '?ctx)))
        off    (for [[q {:keys [shape]}] (sort-by (comp str first) predicates/entries)
                     :when shape
                     :let [n     (count (:args shape))
                           tail? (boolean (or (:optional shape) (:variadic shape)))
                           exact (stated 'arity q)
                           floor (stated 'arityMin q)]
                     :when (or (and (seq exact) (or tail? (not= #{n} exact)))
                               (and (seq floor) (or (not tail?) (not= #{n} floor))))]
                 [q shape exact floor])]
    (is (= [] (vec off)))))

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
               [{:genl      #(v/assert kb (list 'genl wide_arity 'fixed_arity) 'CxUniverse)
                 :mapping   #(v/assert kb (list 'relationTypeByArity wide_arity 4) 'CxUniverse)
                 :member    #(v/assert kb (list wide_arity chainOf) 'CxUniverse)
                 ;; the SAME arity the mapping fact names, so the converse rule has
                 ;; something to conclude from whenever it is generated
                 :unrelated #(v/assert kb (list 'arity pairOf 4) 'CxUniverse)}
                (fn []
                  {:derived-arity (v/ask? kb (list 'arity chainOf 4) 'CxUniverse)
                   :derived-fixed (v/isa? kb chainOf 'fixed_arity)
                   :no-variable   (v/isa? kb chainOf 'variable_arity)
                   :unrelated-fixed (v/isa? kb pairOf 'fixed_arity)
                   :converse      (v/ask? kb (list wide_arity pairOf) 'CxUniverse)
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
  ;; move is that the generated rule goes with the fact while the membership stays.
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
               [{:genl    #(v/assert kb (list 'genl wide_arity 'fixed_arity) 'CxUniverse)
                 :mapping #(vreset! handle
                                    (v/assert kb (list 'relationTypeByArity wide_arity 4)
                                              'CxUniverse))
                 :unmap   #(v/retract! kb @handle)
                 :member  #(v/assert kb (list wide_arity chainOf) 'CxUniverse)
                 :exact   #(v/assert kb (list 'arity exactOf 4) 'CxUniverse)}
                (fn []
                  {:member-stands (v/ask? kb (list wide_arity chainOf) 'CxUniverse)
                   :arity-gone    (v/ask? kb (list 'arity chainOf 4) 'CxUniverse)
                   :mapping-gone  (v/ask? kb (list 'relationTypeByArity wide_arity 4) 'CxUniverse)
                   :exact-stands  (v/ask? kb (list 'arity exactOf 4) 'CxUniverse)
                   :conflicts     (count (v/conflicts kb))})]))))]
    (testing "the fact's conclusion goes with it, and nothing else does"
      (is (true? (:member-stands result)) "the membership was asserted and stands")
      (is (false? (:arity-gone result)) "the generated rule's conclusion is withdrawn")
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
               [{:exact #(v/assert kb (list 'arity pairOf 2) 'CxUniverse)
                 :class #(v/assert kb (list 'binary_predicate pairOf) 'CxUniverse)
                 :kind  #(v/assert kb (list 'instance_relation_predicate pairOf) 'CxUniverse)
                 :other #(v/assert kb (list 'variable_arity_predicate chainOf) 'CxUniverse)}
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
                                                           'CxUniverse))
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
  ;; mark supplies predicate-hood; CxUniverse therefore declares no argument position for it,
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
    ;; shape either kind can have.  The converse the generator generates stops at the
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

(tu/deftest-kb an-arity-and-a-kind-leave-the-kind-class-to-the-sweep
  ;; The guarded predicate and function rules are inert, so the kind class of a relation
  ;; with an arity is neither proved at query time nor stored: the relation reaches the
  ;; relation-wide class forward, and the kind class is the `implicit-arity-class`
  ;; integrity finding its author states.  Forced to the entailing reading: `(arg arity 1
  ;; fixed_arity)` refuses `(arity P 2)` for a P nothing else classifies under the
  ;; constraint-only reading.
  (tu/with-entailing
    (tu/with-terms [pred2 fn2 rel2]
      (v/assert kb (list 'predicate pred2) 'CxUniverse)
      (v/assert kb (list 'arity pred2 2) 'CxUniverse)
      (testing "the arity reaches the relation-wide class and the policy"
        (is (v/isa? kb pred2 'binary))
        (is (v/isa? kb pred2 'fixed_arity)))
      (testing "a predicate is not proved binary_predicate, and nothing is stored"
        (is (empty? (v/query kb (list 'binary_predicate pred2) 'CxUniverse {:max-depth 3})))
        (is (empty? (v/sentexes-matching kb (list 'binary_predicate pred2) 'CxUniverse)))
        (is (empty? (v/query kb (list 'binary_function pred2) 'CxUniverse {:max-depth 3}))))
      (testing "nor is a function proved binary_function"
        (v/assert kb (list 'arity fn2 2) 'CxUniverse)
        (v/assert kb (list 'function fn2) 'CxUniverse)
        (is (v/isa? kb fn2 'binary))
        (is (empty? (v/query kb (list 'binary_function fn2) 'CxUniverse {:max-depth 3})))
        (is (empty? (v/query kb (list 'binary_predicate fn2) 'CxUniverse {:max-depth 3}))))
      (testing "and the integrity sweep names each missing kind class"
        (is (= '#{[binary_predicate 2] [binary_function 2]}
               (into #{} (map (juxt :class :arity))
                     (:implicit-arity-class
                      (v/kb-integrity kb #{pred2 fn2} 'CxUniverse
                                      {:categories #{:implicit-arity-class}}))))))
      (testing "while a binary relation of neither kind is binary and no kind class"
        (v/assert kb (list 'relation rel2) 'CxUniverse)
        (v/assert kb (list 'arity rel2 2) 'CxUniverse)
        (is (v/isa? kb rel2 'binary))
        (is (empty? (v/query kb (list 'binary_predicate rel2) 'CxUniverse {:max-depth 3})))
        (is (empty? (v/query kb (list 'binary_function rel2) 'CxUniverse {:max-depth 3})))))))

(tu/deftest-kb every-exact-class-spelling-declares-the-arity-it-names
  ;; `tax/exact-arity-classes` is the membership spelling of an arity, and CxUniverse
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
                        {:strength :monotonic})]
        (is (= {:reason :inert :binding {:length arity :via spelledRelation :grounds [m]}}
               (select-keys (v/why-not kb h) [:reason :binding]))
            (str "and a :monotonic one is inert, its binding the stored " class
                 " membership"))))))

(tu/deftest-kb the-arity-bindings-keep-the-strength-they-were-written-at
  ;; The four spellings are forced-monotonic (docs/taxonomy.md, "Arity"), so
  ;; a binding goes OUT only by retraction and a nogood it grounds never takes it OUT.
  ;; Neither the record nor the class moves from the strength it was written at.
  (tu/with-terms [boundRel varRel]
    (doseq [s [(list 'binary_predicate boundRel) (list 'arity boundRel 2)
               (list 'variable_arity varRel) (list 'arityMin varRel 2)]]
      (let [h (v/assert kb s 'CxUniverse {:strength :default})]
        (is (= [:default :default] [(:strength (v/sentex kb h)) (v/defeat-class kb h)])
            (pr-str s))))))

(tu/deftest-kb two-related-predicates-bound-to-different-lengths-are-a-hard-clash
  ;; Every member is forced-monotonic, so the pair is reported in `conflicts` and every
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
  ;; `tangiblePartOf` holds between two individuals where `partType` holds between two kinds,
  ;; and `typeToInstancePred` links that pair.  Each mark's own comment writes the
  ;; shape — `(?predicate x y)` and `(?predicate T1 T2)` — so the `genl` edge says it.
  (testing "each mark carries the arity its definition writes"
    (doseq [mark '[instance_relation_predicate type_relation_predicate]]
      (is (v/genl? kb mark 'binary_predicate) (str mark " is a binary_predicate"))
      (is (v/genl? kb mark 'binary))
      (is (v/genl? kb mark 'predicate))))
  (testing "so a :monotonic mark alone binds a relation's length, with no separate arity declaration"
    (tu/with-terms [partOfSomething]
      (v/assert kb (list 'instance_relation_predicate partOfSomething) 'CxUniverse
                {:strength :monotonic})
      (is (v/isa? kb partOfSomething 'binary_predicate))
      (is (= 2 (v/relation-arity kb partOfSomething)))
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
    (is (v/ask? kb '(arg lessThan 1 number) 'CxUniverse))
    (is (v/ask? kb '(arg lessThan 2 number) 'CxUniverse))
    (doseq [position (range 1 6)]
      (is (seq (v/sentexes-matching kb (list 'arg 'interArg position '?t) 'CxUniverse))
          (str "interArg position " position " is declared")))))

;; ---- arityMin as an enforced floor, not documentary vocabulary -----------

(tu/deftest-kb variable-arity-application-is-floored-at-arity-min
  ;; #68: a variable-arity relation reads a chain of any length at or above the minimum
  ;; arityMin states.  An application shorter than the minimum is inert, as a fixed-arity
  ;; relation's wrong length is; one at or above it is believed.
  (tu/with-terms [chainRel a b c]
    (v/assert kb (list 'variable_arity_predicate chainRel) 'CxUniverse)
    (let [floor (v/assert kb (list 'arityMin chainRel 2) 'CxUniverse)]
      (testing "an application shorter than the minimum is read OUT"
        (is (tu/stored-in-clash? kb (list chainRel a) 'CxUniverse)))
      (testing "and a :monotonic one is inert, its binding the arityMin declaration"
        (let [h (v/assert kb (list chainRel b) 'CxUniverse {:strength :monotonic})]
          (is (= {:min 2 :via chainRel :grounds [floor]} (:binding (v/why-not kb h))))))
      (testing "an application at the minimum is believed"
        (v/assert kb (list chainRel a b) 'CxUniverse)
        (is (v/ask? kb (list chainRel a b) 'CxUniverse)))
      (testing "a longer application is believed"
        (v/assert kb (list chainRel a b c) 'CxUniverse)
        (is (v/ask? kb (list chainRel a b c) 'CxUniverse))))))

(tu/deftest-kb a-variable-arity-relation-with-no-minimum-keeps-its-exemption
  ;; The floor is the minimum's alone: a variable-arity relation the KB gives no arityMin
  ;; reads a chain of any length, including one argument, as it did before the minimum was
  ;; read.
  (tu/with-terms [freeRel a]
    (v/assert kb (list 'variable_arity_predicate freeRel) 'CxUniverse)
    (is (v/assert kb (list freeRel a) 'CxUniverse)
        "a one-argument application of an unfloored variable-arity relation is admitted")))

(tu/deftest-kb a-late-minimum-takes-a-short-fact-stored-before-it-out
  ;; the floor is read at the reader, so the arrival order of the minimum and the short
  ;; application decides nothing
  (tu/with-terms [lateRel a]
    (v/assert kb (list 'variable_arity_predicate lateRel) 'CxUniverse)
    (v/assert kb (list lateRel a) 'CxUniverse)             ; one argument, no minimum yet
    (is (v/ask? kb (list lateRel a) 'CxUniverse) "believed while nothing floors it")
    (v/assert kb (list 'arityMin lateRel 2) 'CxUniverse)
    (is (not (v/ask? kb (list lateRel a) 'CxUniverse))
        "and read OUT once the minimum arrives")))

(defn- except-shape
  "CxUniverse's `relationTypeByArity` rule derives `(unary rel)` from `(arity rel 1)`, both
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

(tu/deftest-kb an-except-of-a-binding-leaves-the-length-bound
  ;; The except hides the binding sentences at CxHid, and a relation's length stays bound
  ;; at every context, so the tuples there are inert as the sibling's are.
  (tu/with-terms [rel CxHid CxSib]
    (let [[ar un at] (except-shape kb {:rel rel :hid CxHid :sib CxSib})
          out        (fn [cx] (count (remove #(v/believed? kb % cx) (get at cx))))]
      (is (some? un) "the rule derives the membership")
      (is (not-any? #(v/believed? kb % CxHid) [ar un]) "CxHid believes neither binding")
      (is (every? #(v/believed? kb % CxSib) [ar un]))
      (is (= [2 2] [(out CxHid) (out CxSib)]))
      (is (= #{:inert} (into #{} (map #(:reason (v/why-not kb %))) (mapcat val at)))))))

(tu/deftest-kb a-descension-pair-is-one-contradicts-in-cxuniverse
  ;; `lo` binds three below `rel`, bound to two: one `contradicts` between the two
  ;; bindings is stored in CxUniverse, believed at every reader below it whatever the
  ;; except hides, and no `defeat` is placed.
  (tu/with-terms [rel lo CxHid CxSib]
    (let [[_ _ _ bi] (except-shape kb {:rel rel :lo lo :hid CxHid :sib CxSib})
          lo3        (v/handle-of kb (list 'arity lo 3) 'CxUniverse)
          placed     (into [] (filter #(= #{bi lo3} (into #{} (map second) (rest (:sentence %)))))
                           (v/sentexes-with-functor kb 'contradicts))]
      (is (= ['CxUniverse] (mapv :context placed)))
      (is (every? #(v/believed? kb (:id (first placed)) %) ['CxUniverse CxHid CxSib]))
      (is (not-any? #(some #{(list 'sentexHandle bi) (list 'sentexHandle lo3)} (rest (:sentence %)))
                    (v/sentexes-with-functor kb 'defeat))))))

;; ---- a tuple that breaks its binding is inert ------------------------------

(tu/deftest-kb a-tuple-that-breaks-its-binding-is-inert-and-nothing-is-placed
  ;;   CxUniverse  (arity rel 2) monotonic
  ;;     └─ CxB    (rel Xa Xb Xc) default
  ;;          └─ CxV  (variable_arity rel)
  ;; The tuple is held in the `:out` forced set at every context, and `why-not` names the
  ;; binding.  A relation's length reads the same at every context, so the
  ;; `variable_arity` stated in CxV releases `rel` at CxB too.
  (tu/with-terms [rel Xa Xb Xc CxB CxV]
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxV CxB) 'CxUniverse)
    (let [bind   (v/assert kb (list 'arity rel 2) 'CxUniverse {:strength :monotonic})
          t      (v/assert kb (list rel Xa Xb Xc) CxB)
          placed (fn [] (into [] (comp (mapcat #(v/sentexes-with-functor kb %))
                                       (filter #(some #{(list 'sentexHandle t)} (rest (:sentence %)))))
                              '[contradicts defeat]))]
      (is (empty? (placed)))
      (is (= [false false] [(v/believed? kb t CxB) (v/believed? kb t CxV)]))
      (let [{r :reason {:keys [length via grounds]} :binding} (v/why-not kb t)]
        ;; the rule that derives `(binary rel)` from the arity adds a second ground
        (is (= [:inert 2 rel true] [r length via (contains? (set grounds) bind)])))
      (testing "a variable_arity stated below releases the functor at every context"
        (let [va (v/assert kb (list 'variable_arity rel) CxV {:strength :monotonic})]
          (is (= [true true] [(v/believed? kb t CxV) (v/believed? kb t CxB)]))
          (v/retract! kb va)
          (is (false? (v/believed? kb t CxB)))))
      (testing "retracting the binding makes the tuple believed"
        (v/retract! kb bind)
        (is (true? (v/believed? kb t CxB)))
        (is (empty? (placed)))))))

(tu/deftest-kb a-breaking-tuple-is-inert-in-either-order-at-either-strength-and-after-a-recover
  (tu/with-terms [rel Xa Xb Xc]
    (doseq [strength [:default :monotonic]
            order    [[:binding :tuple] [:tuple :binding]]]
      (let [ss {:binding #(v/assert kb (list 'arity rel 2) 'CxUniverse {:strength :monotonic})
                :tuple   #(v/assert kb (list rel Xa Xb Xc) 'CxUniverse {:strength strength})}
            hs (into {} (map (fn [k] [k ((ss k))])) order)
            at (pr-str strength order)]
        (is (= :inert (:reason (v/why-not kb (:tuple hs)))) at)
        (v/recover kb)
        (is (= :inert (:reason (v/why-not kb (:tuple hs)))) (str at " after a recover"))
        (run! #(v/retract! kb (hs %)) (reverse order))))))

(tu/deftest-kb an-engine-term-s-binding-holds-none-of-its-tuples-inert
  ;; `genl`'s length is its shape, so a third-length binding the settle stores for it off a
  ;; `:monotonic` metatype route moves nothing; `assert` refuses `(arity genl 3)`
  (tu/with-terms [low_kind high_kind kindrel]
    (let [m {:strength :monotonic}
          k (v/assert kb (list kindrel 'genl) 'CxUniverse m)
          r (v/assert kb (list 'genl kindrel 'ternary_predicate) 'CxUniverse m)
          e (v/assert kb (list 'genl low_kind high_kind) 'CxUniverse)]
      (is (some? (v/handle-of kb '(ternary_predicate genl) 'CxUniverse)))
      (is (v/believed? kb e 'CxUniverse))
      (run! #(v/retract! kb %) [e r k]))))

(def ^:private unseen-binding-rows
  "`[binding-strength order]`: the binding's strength and the arrival order of the three
  writes in `a-binding-the-reader-does-not-see-convicts-its-tuple-through-its-copy`."
  [[:monotonic [:edge :binding :tuple]]
   [:monotonic [:tuple :edge :binding]]
   [:default   [:edge :binding :tuple]]
   [:default   [:tuple :edge :binding]]])

(tu/deftest-kb a-binding-the-reader-does-not-see-convicts-its-tuple-through-its-copy
  ;;   CxUniverse    (rel Xa Xb Xc) default
  ;;     └─ CxWell
  ;;          └─ CxA  (arity rel 2)
  ;; CxUniverse does not see CxA, a data context below CxWell.  core.txt declares
  ;; `(decontextualized_predicate arity)`, so the binding has a copy in CxUniverse, and the
  ;; tuple is not believed there.
  (doseq [[strength order] unseen-binding-rows]
    (tu/with-terms [rel Xa Xb Xc CxA]
      (let [tuple (list rel Xa Xb Xc)
            ss    {:edge    #(v/assert kb (list 'genlCx CxA 'CxWell) 'CxUniverse)
                   :binding #(v/assert kb (list 'arity rel 2) CxA {:strength strength})
                   :tuple   #(v/assert kb tuple 'CxUniverse)}
            hs    (into {} (map (fn [k] [k ((ss k))])) order)
            row   [strength order]]
        (is (some? (v/handle-of kb (list 'arity rel 2) 'CxUniverse)) (str row " the copy"))
        (is (false? (v/believed? kb (:tuple hs) 'CxUniverse)) (str row))
        (v/retract! kb (:binding hs))
        (is (nil? (v/handle-of kb (list 'arity rel 2) 'CxUniverse))
            (str row " retracting the binding removes the copy"))
        (is (true? (v/believed? kb (:tuple hs) 'CxUniverse)) (str row))
        (run! #(v/retract! kb (hs %)) [:tuple :edge]))))
  (testing "a recover rebuilds the copy, and the tuple stays OUT at CxUniverse"
    (tu/with-terms [rel Xa Xb Xc Xd CxA]
      (let [hs [(v/assert kb (list 'genlCx CxA 'CxWell) 'CxUniverse)
                (v/assert kb (list 'arity rel 2) CxA {:strength :monotonic})
                (v/assert kb (list rel Xa Xb Xc) 'CxUniverse)]]
        (is (= [false false false]
               (mapv :loser (tu/recovered-readings kb false [(list rel Xa Xb Xc) 'CxUniverse]
                                                   #(v/assert % (list rel Xa Xd) 'CxUniverse)))))
        (run! #(v/retract! kb %) (rseq hs))))))

(tu/deftest-kb a-second-length-unbinds-the-functor-at-every-context
  ;;   CxUniverse  (arity rel 2) (arity rel 3) monotonic   (rel Xa Xb Xc Xd) default
  ;;     └─ CxR    (except (arity rel 3))
  ;; Two lengths leave `rel` unbound at every context, CxR included, so the tuple is
  ;; believed in every arrival order, and the two lengths are one `contradicts` in
  ;; CxUniverse.
  (tu/with-terms [rel Xa Xb Xc Xd CxR]
    (v/assert kb (list 'genlCx CxR 'CxUniverse) 'CxUniverse)
    (let [M      {:strength :monotonic}
          ss     {:two   #(v/assert kb (list 'arity rel 2) 'CxUniverse M)
                  :three #(v/assert kb (list 'arity rel 3) 'CxUniverse M)
                  :tuple #(v/assert kb (list rel Xa Xb Xc Xd) 'CxUniverse)}
          orders (for [a (keys ss), b (keys ss), c (keys ss) :when (= 3 (count (hash-set a b c)))] [a b c])]
      (is (= #{true}
             (into #{} (for [order orders]
                         (let [hs (into {} (map (fn [k] [k ((ss k))])) order)
                               r  (v/believed? kb (:tuple hs) 'CxUniverse)]
                           (run! #(v/retract! kb (hs %)) (reverse order))
                           r)))))
      (let [two   ((:two ss))
            three ((:three ss))
            t     ((:tuple ss))]
        (testing "an except of the second length below leaves the functor unbound there"
          (let [ex (v/assert kb (list 'except (list 'sentexHandle three)) CxR M)]
            (is (true? (v/believed? kb t CxR)))
            (v/retract! kb ex)))
        (is (= 1 (count (filter #(= #{two three} (into #{} (map second) (rest (:sentence %))))
                                (v/sentexes-with-functor kb 'contradicts)))))
        (testing "the second length leaving binds the functor at every context"
          (v/retract! kb three)
          (is (= [false false] [(v/believed? kb t 'CxUniverse) (v/believed? kb t CxR)])))
        (v/retract! kb two)))))

(tu/deftest-kb a-binding-the-sentence-alone-shows-is-wrong-is-refused
  ;; `try-assert` refuses as `assert` does, and the spelling half follows the `:naming`
  ;; policy, so a KB with its own spelling conventions stores it
  ;; `with-terms` lowercases a base, so the camelCase relation is spelled here; no row
  ;; stores it
  (tu/with-terms [warm_t rel]
    ;; [binding refused-type]: what `assert` and `check` answer for a binding the
    ;; sentence alone decides, against an engine term's shape and against the bound
    ;; relation's spelling; nil where the binding agrees
    (doseq [[s refused] (let [likesRel (symbol (str rel "Of"))]
                          [[(list 'arity 'genl 3)              :length-against-shape]
                           [(list 'arity 'arg 2)               :length-against-shape]
                           [(list 'arity 'partition 3)         :length-against-shape]
                           [(list 'arityMin 'partition 4)      :length-against-shape]
                           [(list 'ternary_predicate 'genl)    :length-against-shape]
                           [(list 'variable_arity 'partition)  nil]
                           [(list 'arityMin 'partition 2)      nil]
                           [(list 'arity 'genl 2)              nil]
                           [(list 'binary_predicate warm_t)    :length-against-spelling]
                           [(list 'arityMin warm_t 2)          :length-against-spelling]
                           [(list 'arity likesRel 1)           :length-against-spelling]
                           [(list 'unary_predicate likesRel)   :length-against-spelling]
                           [(list 'arity warm_t 1)             nil]
                           [(list 'arityMin likesRel 1)        nil]
                           [(list 'variable_arity warm_t)      nil]])
            :let [thrown (fn [write k] (try (write k s 'CxUniverse) nil
                                            (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))]]
      (testing (pr-str s)
        (is (= refused (:type (first (v/check kb s 'CxUniverse)))) "check reports it")
        (when refused
          (is (= [refused refused] [(thrown v/assert kb) (thrown v/try-assert kb)]))
          (is (nil? (v/handle-of kb s 'CxUniverse)) "nothing stored")
          (is (= (when (= refused :length-against-shape) [refused])
                 (some->> (v/check (assoc kb :naming :off) s 'CxUniverse) seq (mapv :type)))
              "the spelling half reads the naming policy"))))))

(defn- missing-args
  "The `:missing-arg` findings as `context` reads the starter, as a set of
  `[predicate missing-positions]`."
  [kb context]
  (into #{} (map (juxt :predicate :missing))
        (:missing-arg (v/kb-integrity kb #{} context {:categories #{:missing-arg}
                                                      :max-results 10000}))))

(def ^:private open-positions
  "The starter's argument positions no declaration types yet, each awaiting a ruling on
  its type: the quoted example of the three example predicates and every position of
  termsRelated.  ontology_test's undeclared-positions gives the reason the fixed-arity
  ones among them stay open."
  '#{[positiveExample [2]] [negativeExample [2]] [borderlineExample [2]]
     [termsRelated [1 2 :rest]]})

(tu/deftest-kb every-starter-position-is-typed-but-the-open-ones
  ;; A middle context's relation and type carry their arity mark in CxUniverse, where the
  ;; declarations typing them are not visible, so the audit from CxUniverse also reports
  ;; those.  Read from CxTra and from CxSocialExtension, which between them see every
  ;; middle context that declares one, each such finding clears; what both still report
  ;; is a position no declaration types.
  (let [universe (missing-args kb 'CxUniverse)
        open     (set/intersection (missing-args kb 'CxTra)
                                   (missing-args kb 'CxSocialExtension))]
    (is (= open-positions open))
    (is (set/subset? open universe))
    (is (= 41 (count (set/difference universe open)))
        "the middle-context relations and types cleared from their own context")))
