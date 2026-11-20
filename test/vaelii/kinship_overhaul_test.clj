;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kinship-overhaul-test
  "One common kinship vocabulary with independently classified blood and chosen readings."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- load-kinship-fixture! [kb]
  (tu/load-starter! kb)
  (doseq [sentence '[;; edges stated before the generic marks of the predicates they relate
                     (binary_predicate testEarlyNarrowKinshipOf)
                     (binary_predicate testEarlyMiddleKinshipOf)
                     (binary_predicate testEarlyBroadKinshipOf)
                     (genl testEarlyNarrowKinshipOf testEarlyMiddleKinshipOf)
                     (genl testEarlyMiddleKinshipOf testEarlyBroadKinshipOf)
                     (generic_kinship_predicate testEarlyNarrowKinshipOf)
                     (generic_kinship_predicate testEarlyMiddleKinshipOf)
                     (generic_kinship_predicate testEarlyBroadKinshipOf)
                     (generic_kinship_predicate testMiddleKinshipOf)
                     (binary_predicate testMiddleKinshipOf)
                     (generic_kinship_predicate testKinshipSequenceOf)
                     (variable_arity_predicate testKinshipSequenceOf)
                     (arityMin testKinshipSequenceOf 3)
                     (generic_kinship_predicate testNarrowKinshipOf)
                     (binary_predicate testNarrowKinshipOf)
                     (generic_kinship_predicate testBroadKinshipOf)
                     (binary_predicate testBroadKinshipOf)
                     (binary_predicate testBloodLeafOf)
                     (genl testBloodLeafOf bloodRelativeOf)
                     (binary_predicate testChosenLeafOf)
                     (genl testChosenLeafOf chosenKinOf)]]
    (v/assert kb sentence 'CxUniverse {:strength :monotonic}))
  kb)

(use-fixtures :once (tu/loaded load-kinship-fixture!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)
(def ^:private K 'CxKinship)
(def ^:private kinds '[time_invariant_relation time_agnostic_relation time_varying_relation])

(defn- proves? [kb sentence context]
  (v/query? kb sentence context {:max-depth 5}))

(defn- kinds-of [kb predicate]
  (set (filter #(v/ask? kb (list % predicate) U) kinds)))

(defn- blood [predicate] (list 'BloodKinFn predicate))
(defn- chosen [predicate] (list 'ChosenKinFn predicate))

(tu/deftest-kb qualified-predicates-have-distinct-rigidity-kinds
  (doseq [predicate '[kinOf parentOf childOf motherOf fatherOf siblingOf
                      grandparentOf ancestorOf birthDate birthYearOf olderThan]]
    (testing (str predicate)
      (is (true? (v/ask? kb (list 'generic_kinship_predicate predicate) U)))
      (is (= #{'time_agnostic_relation} (kinds-of kb predicate)))
      (is (not (v/ask? kb (list 'eternal_predicate predicate) U))))
    (testing (str "blood " predicate)
      (is (true? (v/ask? kb (list 'blood_kinship_predicate (blood predicate)) U)))
      (is (true? (v/ask? kb (list 'eternal_predicate (blood predicate)) U)))
      (is (= #{'time_invariant_relation} (kinds-of kb (blood predicate)))))
    (testing (str "chosen " predicate)
      (is (true? (v/ask? kb (list 'chosen_kinship_predicate (chosen predicate)) U)))
      (is (= #{'time_varying_relation} (kinds-of kb (chosen predicate)))))
    (is (not (v/ask? kb (list 'generic_kinship_predicate (blood predicate)) U)))
    (is (not (v/ask? kb (list 'generic_kinship_predicate (chosen predicate)) U)))))

(tu/deftest-kb branch-specializations-get-their-stronger-classification
  (is (true? (v/ask? kb '(blood_kinship_predicate testBloodLeafOf) U)))
  (is (true? (v/ask? kb '(eternal_predicate testBloodLeafOf) U)))
  (is (true? (v/ask? kb '(chosen_kinship_predicate testChosenLeafOf) U)))
  (is (true? (v/ask? kb '(time_varying_relation testChosenLeafOf) U)))
  (is (not (v/ask? kb '(generic_kinship_predicate testBloodLeafOf) U)))
  (is (not (v/ask? kb '(generic_kinship_predicate testChosenLeafOf) U))))

(tu/deftest-kb constructors-have-corresponding-predicates-and-named-roots
  (is (true? (v/ask? kb '(functionCorrespondingPredicate BloodKinFn bloodKinPredicateOf 2) U)))
  (is (true? (v/ask? kb '(functionCorrespondingPredicate ChosenKinFn chosenKinPredicateOf 2) U)))
  (is (true? (v/ask? kb '(rewriteOf bloodRelativeOf (BloodKinFn kinOf)) U)))
  (is (true? (v/ask? kb '(rewriteOf chosenKinOf (ChosenKinFn kinOf)) U)))
  (is (true? (v/ask? kb '(covering kinOf bloodRelativeOf chosenKinOf) U)))
  (is (true? (v/ask? kb '(bloodKinPredicateOf siblingOf (BloodKinFn siblingOf)) U)))
  (is (true? (v/ask? kb '(chosenKinPredicateOf siblingOf (ChosenKinFn siblingOf)) U))))

(tu/deftest-kb constructor-lifting-stays-on-the-unqualified-hierarchy
  (doseq [constructor [blood chosen]]
    (is (true? (v/ask? kb (list 'genl (constructor 'siblingOf) (constructor 'kinOf)) U)))
    (is (true? (v/ask? kb (list 'genl (constructor 'siblingOf) 'siblingOf) U))))
  (let [formulas (v/query kb '(natFormula ?term ?expression) U)
        by-term (into {} (map (juxt '?term '?expression) formulas))
        qualified? #(and (sequential? %) (#{'BloodKinFn 'ChosenKinFn} (first %)))
        rule-count #(count (filter :antecedent (v/sentexes-in-context kb U)))
        before [(count formulas) (rule-count)]]
    (is (seq formulas) "the check inspected minted expressions")
    (is (pos? (second before)) "the fixed-point check counts actual stored rules")
    (is (not-any? (fn [[_ expression]]
                    (and (qualified? expression)
                         (qualified? (get by-term (second expression)))))
                  by-term)
        "no constructor input names another constructed kinship predicate")
    (dotimes [_ 3]
      (v/ask? kb '(genl (BloodKinFn siblingOf) bloodRelativeOf) U))
    (is (= before [(count (v/query kb '(natFormula ?term ?expression) U)) (rule-count)])
        "repeated reads preserve the saturated formula and rule counts")))

(tu/deftest-kb generated-lifts-follow-late-source-edges-and-their-retraction
  (doseq [constructor [blood chosen]]
    (is (not (v/ask? kb (list 'genl (constructor 'testNarrowKinshipOf)
                              (constructor 'testBroadKinshipOf)) K))))
  (let [edge (v/assert kb '(genl testNarrowKinshipOf testBroadKinshipOf) K)]
    (doseq [constructor [blood chosen]]
      (is (true? (v/ask? kb (list 'genl (constructor 'testNarrowKinshipOf)
                                  (constructor 'testBroadKinshipOf)) K))))
    (v/retract! kb edge)
    (doseq [constructor [blood chosen]]
      (is (not (v/ask? kb (list 'genl (constructor 'testNarrowKinshipOf)
                                (constructor 'testBroadKinshipOf)) K))))))

(tu/deftest-kb constructor-rules-preserve-exact-arity-and-minimum-arity
  (doseq [constructor [blood chosen]]
    (is (true? (v/ask? kb (list 'arity (constructor 'siblingOf) 2) U))))
  (doseq [constructor [blood chosen]]
    (is (true? (v/ask? kb (list 'arityMin (constructor 'testKinshipSequenceOf) 3) U)))))

(tu/deftest-kb qualified-variable-policies-enforce-the-copied-minimum
  (tu/with-terms [Ann Bob Cal Dee]
    (doseq [constructor [blood chosen]]
      (let [predicate (constructor 'testKinshipSequenceOf)
            refusal (try (v/try-assert kb (list predicate Ann Bob) U) nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :arity (:violation refusal)))
        (doseq [arguments [[Ann Bob Cal] [Ann Bob Cal Dee]]]
          (let [sentence (apply list predicate arguments)
                h (v/try-assert kb sentence U)]
            (is (true? (v/in? kb h)))
            (is (true? (v/ask? kb sentence U)))))))))

(tu/deftest-kb contradictory-qualified-metadata-is-not-hidden-by-review-records
  (doseq [[sentence violation] [['(arity (BloodKinFn siblingOf) 1) :functional]
                                ['(unary_predicate (BloodKinFn siblingOf)) :disjoint]]]
    (let [refusal (try (v/try-assert kb sentence U) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :definitional-clash (:type refusal)))
      (is (= violation (:violation refusal)))))
  (is (true? (v/ask? kb '(arity (BloodKinFn siblingOf) 2) U))))

(tu/deftest-kb qualified-siblings-imply-the-common-predicate-but-not-each-other
  (tu/with-terms [Ann Bob Cal Dee Elm Fox]
    (v/assert kb (list (blood 'siblingOf) Ann Bob) K)
    (v/assert kb (list (chosen 'siblingOf) Cal Dee) K)
    (v/assert kb (list 'siblingOf Elm Fox) K)
    (is (true? (v/ask? kb (list 'siblingOf Ann Bob) K)))
    (is (true? (v/ask? kb (list 'siblingOf Cal Dee) K)))
    (is (not (proves? kb (list (chosen 'siblingOf) Ann Bob) K)))
    (is (not (proves? kb (list (blood 'siblingOf) Cal Dee) K)))
    (doseq [constructor [blood chosen]]
      (is (not (proves? kb (list (constructor 'siblingOf) Elm Fox) K))))))

(tu/deftest-kb ordinary-blood-parenthood-supports-genetic-overlap-but-common-kinship-does-not
  (tu/with-terms [Ann Bob Cal Dee]
    (v/assert kb (list (blood 'parentOf) Ann Bob) K)
    (v/assert kb (list 'parentOf Cal Dee) K)
    (is (true? (v/ask? kb (list 'sharesGenesWith Ann Bob) K)))
    (is (true? (v/ask? kb (list 'sharesGenesWith Bob Ann) K)))
    (is (not (proves? kb (list 'sharesGenesWith Cal Dee) K)))
    (is (not (proves? kb (list 'bloodRelativeOf Cal Dee) K)))
    (is (not (proves? kb (list 'chosenKinOf Cal Dee) K)))))

(tu/deftest-kb chimerism-blocks-the-default-without-denying-genetic-overlap
  (tu/with-terms [Ann Bob]
    (v/assert kb (list (blood 'parentOf) Ann Bob) K)
    (is (true? (v/ask? kb (list 'sharesGenesWith Ann Bob) K)))
    (v/assert kb (list 'genetic_chimera Bob) K)
    (is (not (proves? kb (list 'sharesGenesWith Ann Bob) K)))
    (is (not (proves? kb (list 'not (list 'sharesGenesWith Ann Bob)) K)))))

(tu/deftest-kb an-ordinary-shared-blood-parent-proves-siblings
  (tu/with-terms [Mother Ann Bob]
    (v/assert kb (list (blood 'motherOf) Ann Mother) K)
    (v/assert kb (list (blood 'motherOf) Bob Mother) K)
    (is (true? (v/ask? kb (list 'siblingOf Ann Bob) K)))
    (is (true? (v/ask? kb (list (blood 'siblingOf) Ann Bob) K)))
    (is (true? (v/ask? kb (list 'sharesGenesWith Ann Bob) K)))))

(tu/deftest-kb gestational-only-origination-stays-open-with-an-ordinary-blood-control
  (tu/with-terms [Carrier GeneticParent Ann]
    (v/assert kb (list 'surrogateMotherOf Ann Carrier) 'CxWell)
    (v/assert kb (list 'gestationalOnlyParentOf Carrier Ann) 'CxWell)
    (v/assert kb (list (blood 'parentOf) GeneticParent Ann) 'CxWell)
    (is (true? (v/query? kb (list 'originatorOf GeneticParent Ann) 'CxWell {:max-depth 5})))
    (is (not (v/query? kb (list 'originatorOf Carrier Ann) 'CxWell {:max-depth 5})))
    (is (not (v/query? kb (list 'not (list 'originatorOf Carrier Ann)) 'CxWell {:max-depth 5})))))

(tu/deftest-kb a-shared-gestational-carrier-is-not-a-sibling-or-genetic-proof
  (tu/with-terms [Carrier Ann Bob GeneticMotherAnn GeneticFatherAnn GeneticMotherBob GeneticFatherBob]
    (doseq [sentence [(list 'surrogateMotherOf Ann Carrier)
                      (list 'surrogateMotherOf Bob Carrier)
                      (list 'gestationalOnlyParentOf Carrier Ann)
                      (list 'gestationalOnlyParentOf Carrier Bob)
                      (list (blood 'motherOf) Ann GeneticMotherAnn)
                      (list (blood 'fatherOf) Ann GeneticFatherAnn)
                      (list (blood 'motherOf) Bob GeneticMotherBob)
                      (list (blood 'fatherOf) Bob GeneticFatherBob)]]
      (v/assert kb sentence K))
    (is (true? (v/ask? kb (list (blood 'motherOf) Ann Carrier) K)))
    (is (true? (v/ask? kb (list (blood 'parentOf) Carrier Ann) K)))
    (doseq [predicate ['siblingOf (blood 'siblingOf) 'sharesGenesWith]]
      (is (not (proves? kb (list predicate Ann Bob) K)) (str predicate " has no proof from the carrier"))
      (is (not (proves? kb (list 'not (list predicate Ann Bob)) K)) "absence of proof is not a negative"))
    (is (not (proves? kb (list 'sharesGenesWith Carrier Ann) K)))
    (is (true? (v/ask? kb (list 'sharesGenesWith GeneticMotherAnn Ann) K)))))

(tu/deftest-kb chosen-siblings-start-in-2020-without-a-2019-blood-or-common-proof
  (tu/with-terms [Carrier Ann Bob CxFamily]
    (v/assert kb (list 'genlCx CxFamily 'CxWell) U)
    (doseq [sentence [(list 'surrogateMotherOf Ann Carrier)
                      (list 'surrogateMotherOf Bob Carrier)
                      (list 'gestationalOnlyParentOf Carrier Ann)
                      (list 'gestationalOnlyParentOf Carrier Bob)]]
      (v/assert kb sentence CxFamily))
    (let [y2019 (list 'CxTimeFn CxFamily '(DatetimeFn "2019"))
          y2020 (list 'CxTimeFn CxFamily '(DatetimeFn "2020"))]
      (v/assert kb (list (chosen 'siblingOf) Ann Bob) y2020)
      (is (true? (v/ask? kb (list (chosen 'siblingOf) Ann Bob) y2020)))
      (is (true? (v/ask? kb (list 'siblingOf Ann Bob) y2020)))
      (doseq [predicate ['siblingOf (chosen 'siblingOf)]]
        (is (= :unknown (:verdict (v/argue kb (list predicate Ann Bob) y2019 {:max-depth 5}))))
        (is (not (proves? kb (list 'not (list predicate Ann Bob)) y2019))))
      (doseq [context [y2019 y2020]
              predicate [(blood 'siblingOf) 'sharesGenesWith]]
        (is (not (proves? kb (list predicate Ann Bob) context)))))))

(tu/deftest-kb common-bounds-do-not-turn-plants-into-persons-or-constructs-into-organisms
  (tu/with-terms [FernParent FernChild FirstPerson SecondPerson CxFamily]
    (v/assert kb (list 'genlCx CxFamily 'CxTra) U)
    (doseq [sentence [(list 'plant FernParent) (list 'plant FernChild)
                      (list (blood 'parentOf) FernParent FernChild)
                      (list 'construct FirstPerson) (list 'construct SecondPerson)
                      (list (chosen 'parentOf) FirstPerson SecondPerson)]]
      (v/assert kb sentence CxFamily))
    (is (true? (v/ask? kb (list 'kinOf FernParent FernChild) CxFamily)))
    (is (not (v/ask? kb (list 'person FernParent) CxFamily)))
    (is (not (v/ask? kb (list 'person FernChild) CxFamily)))
    (is (true? (v/ask? kb (list 'parentOf FirstPerson SecondPerson) CxFamily)))
    (is (not (v/ask? kb (list 'organism FirstPerson) CxFamily)))
    (is (not (v/ask? kb (list 'organism SecondPerson) CxFamily)))
    (is (true? (v/query? kb (list 'originatorOf FernParent FernChild) CxFamily {:max-depth 5})))))

(tu/deftest-kb genetic-and-gestational-mothers-remain-distinct-and-the-function-does-not-choose
  (tu/with-terms [Ann GeneticMother Carrier]
    (doseq [sentence [(list (blood 'motherOf) Ann GeneticMother)
                      (list 'surrogateMotherOf Ann Carrier)
                      (list 'gestationalOnlyParentOf Carrier Ann)]]
      (v/assert kb sentence K))
    (v/assert kb (list 'comment (list 'MotherFn Ann) "An unresolved mother name") K)
    (is (true? (v/ask? kb (list (blood 'motherOf) Ann GeneticMother) K)))
    (is (true? (v/ask? kb (list (blood 'motherOf) Ann Carrier) K)))
    (is (true? (v/ask? kb (list 'different GeneticMother Carrier) K)))
    (is (not (v/ask? kb (list 'functional 'motherOf) K)))
    (is (not (v/ask? kb (list 'functional (blood 'motherOf)) K)))
    (doseq [mother [GeneticMother Carrier]]
      (is (not (proves? kb (list 'equals (list 'MotherFn Ann) mother) K))))
    (is (empty? (v/contradictions kb)))))

;; ---- hierarchy lifting reads the genl edges in any order ----

(def ^:private constructors '[BloodKinFn ChosenKinFn])

(defn- lifted
  "The `genl` edges among `predicates` each constructor lifts, read at `context`."
  [kb predicates context]
  (set (for [constructor constructors spec predicates general predicates
             :when (and (not= spec general)
                        (v/ask? kb (list 'genl (list constructor spec) (list constructor general)) context))]
         [constructor spec general])))

(defn- lifted-chain
  "What each constructor lifts from the edges `[spec general]`, read transitively."
  [edges]
  (let [closure (loop [pairs (set edges)]
                  (let [more (into pairs (for [[a b] pairs [c d] pairs :when (= b c)] [a d]))]
                    (if (= more pairs) pairs (recur more))))]
    (set (for [constructor constructors [spec general] closure] [constructor spec general]))))

(tu/deftest-kb lifted-edges-agree-when-edges-precede-the-generic-marks
  (let [predicates '[testEarlyNarrowKinshipOf testEarlyMiddleKinshipOf testEarlyBroadKinshipOf]]
    (is (= (lifted-chain '[[testEarlyNarrowKinshipOf testEarlyMiddleKinshipOf]
                           [testEarlyMiddleKinshipOf testEarlyBroadKinshipOf]])
           (lifted kb predicates U)))))

(tu/deftest-kb lifted-edges-agree-when-the-generic-marks-precede-edges
  (let [predicates '[testNarrowKinshipOf testMiddleKinshipOf testBroadKinshipOf]]
    (is (empty? (lifted kb predicates K)) "nothing lifts before the edges")
    (v/assert kb '(genl testNarrowKinshipOf testMiddleKinshipOf) K)
    (v/assert kb '(genl testMiddleKinshipOf testBroadKinshipOf) K)
    (is (= (lifted-chain '[[testNarrowKinshipOf testMiddleKinshipOf]
                           [testMiddleKinshipOf testBroadKinshipOf]])
           (lifted kb predicates K)))
    (is (empty? (lifted kb predicates U)) "the lift stays in the context of its edges")))

(tu/deftest-kb retracting-one-edge-leaves-the-lift-of-a-kb-built-without-it
  (let [predicates '[testNarrowKinshipOf testMiddleKinshipOf testBroadKinshipOf]]
    (v/assert kb '(genl testNarrowKinshipOf testMiddleKinshipOf) K)
    (let [without (lifted kb predicates K)
          edge (v/assert kb '(genl testMiddleKinshipOf testBroadKinshipOf) K)]
      (is (= (lifted-chain '[[testNarrowKinshipOf testMiddleKinshipOf]]) without))
      (is (= (lifted-chain '[[testNarrowKinshipOf testMiddleKinshipOf]
                             [testMiddleKinshipOf testBroadKinshipOf]])
             (lifted kb predicates K)))
      (v/retract! kb edge)
      (is (= without (lifted kb predicates K))))))

;; ---- the generated lift rules follow the genl edges ----

(defn- ground? [form] (not-any? #(and (symbol? %) (= \? (first (name %)))) (flatten (list form))))

(defn- lift-rules
  "The distinct stored ground rules concluding a `genl` from a constructed kinship
  predicate, each as `[antecedent consequent context]`, the minted constants spelled
  through their `natFormula`."
  [kb]
  (let [formula (into {} (map (juxt '?term '?expression)) (v/query kb '(natFormula ?term ?expression) U))
        spell #(get formula % %)
        qualified? #(and (sequential? %) (some #{(first %)} constructors))]
    (set (for [context (v/contexts kb)
               sentex (v/sentexes-in-context kb context)
               :let [antecedent (:antecedent sentex)
                     [functor spec general :as consequent] (:consequent sentex)]
               :when (and antecedent (= 'genl functor) (qualified? (spell spec))
                          (ground? antecedent) (ground? consequent))]
           [antecedent (list 'genl (spell spec) (spell general)) context]))))

(defn- lifting-rule?
  "Does the rule `sentence` conclude, at some level, the `genl` between two readings one
  constructor makes of two variables: an authored lift rule, or a generator of them."
  [sentence]
  (boolean (some #(and (sequential? %) (= 'genl (first %)) (= 3 (count %))
                       (let [[_ a b] %]
                         (and (sequential? a) (sequential? b) (some #{(first a)} constructors)
                              (= (first a) (first b)) (ground? (first a))
                              (not (ground? (second a))) (not (ground? (second b))))))
                 (tree-seq sequential? seq sentence))))

(tu/deftest-kb generated-lift-rules-follow-the-genl-edges
  (let [generic (set (map '?p (v/query kb '(generic_kinship_predicate ?p) U)))
        rules (lift-rules kb)
        edge? (fn [[[[functor spec general] :as antecedent] _ context]]
                (and (= 1 (count antecedent)) (= 'genl functor) (generic spec) (generic general)
                     (not= spec general) (true? (v/ask? kb (list 'genl spec general) context))))
        edges (count (for [s (v/sentexes-with-functor kb 'genl {:believed? true})
                           :let [[_ spec general] (:sentence s)]
                           :when (and (generic spec) (generic general) (not= spec general))]
                       s))
        lifts (filter #(lifting-rule? (:sentence %)) (v/chain-report kb))]
    (is (= 2 (count lifts)) "one lift rule or generator per constructor")
    (is (= (* (count constructors) edges) (reduce + (map :placed lifts)))
        (str "the lift places one firing per genl edge between generic predicates and"
             " constructor, so its work follows the edges and not the pairs"))
    (is (empty? rules)
        (str "the lift generates no ground rule, so no rule count grows with the pairs; "
             (count (remove edge? rules)) " of " (count rules) " read no genl edge between"
             " two distinct generic predicates"))))
