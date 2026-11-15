;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kinship-overhaul-test
  "One common kinship vocabulary with independently classified genetic and chosen readings."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- load-kinship-fixture! [kb]
  (tu/load-starter! kb)
  (doseq [sentence '[(unqualified_kinship_predicate testKinshipSequenceOf)
                     (variable_arity_predicate testKinshipSequenceOf)
                     (arityMin testKinshipSequenceOf 3)
                     (unqualified_kinship_predicate testNarrowKinshipOf)
                     (binary_predicate testNarrowKinshipOf)
                     (unqualified_kinship_predicate testBroadKinshipOf)
                     (binary_predicate testBroadKinshipOf)
                     (binary_predicate testGeneticLeafOf)
                     (genl testGeneticLeafOf geneticRelativeOf)
                     (binary_predicate testChosenLeafOf)
                     (genl testChosenLeafOf chosenKinOf)
                     ;; declared only as inputs: nothing names their readings
                     (unqualified_kinship_predicate testNewKinOf)
                     (binary_predicate testNewKinOf)
                     (unqualified_kinship_predicate testNewSymmetricKinOf)
                     (binary_predicate testNewSymmetricKinOf)
                     (symmetric testNewSymmetricKinOf)]]
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

(defn- genetic [predicate] (list 'GeneticKinFn predicate))
(defn- chosen [predicate] (list 'ChosenKinFn predicate))

(tu/deftest-kb qualified-predicates-have-distinct-rigidity-kinds
  (doseq [predicate '[kinOf parentOf childOf motherOf fatherOf siblingOf
                      grandparentOf ancestorOf]]
    (testing (str predicate)
      (is (true? (v/ask? kb (list 'unqualified_kinship_predicate predicate) U)))
      (is (= #{'time_agnostic_relation} (kinds-of kb predicate)))
      (is (not (v/ask? kb (list 'eternal_predicate predicate) U))))
    (testing (str "genetic " predicate)
      (is (true? (v/ask? kb (list 'genetic_kinship_predicate (genetic predicate)) U)))
      (is (true? (v/ask? kb (list 'eternal_predicate (genetic predicate)) U)))
      (is (= #{'time_invariant_relation} (kinds-of kb (genetic predicate)))))
    (testing (str "chosen " predicate)
      (is (true? (v/ask? kb (list 'chosen_kinship_predicate (chosen predicate)) U)))
      (is (= #{'time_varying_relation} (kinds-of kb (chosen predicate)))))
    (is (not (v/ask? kb (list 'unqualified_kinship_predicate (genetic predicate)) U)))
    (is (not (v/ask? kb (list 'unqualified_kinship_predicate (chosen predicate)) U)))))

(tu/deftest-kb birth-and-age-are-eternal-and-not-kinship
  (doseq [predicate '[birthDate birthYearOf olderThan]]
    (testing (str predicate)
      (is (true? (v/ask? kb (list 'eternal_predicate predicate) U)))
      (is (not (v/ask? kb (list 'unqualified_kinship_predicate predicate) U))))))

(tu/deftest-kb branch-specializations-get-their-stronger-classification
  (is (true? (v/ask? kb '(genetic_kinship_predicate testGeneticLeafOf) U)))
  (is (true? (v/ask? kb '(eternal_predicate testGeneticLeafOf) U)))
  (is (true? (v/ask? kb '(chosen_kinship_predicate testChosenLeafOf) U)))
  (is (true? (v/ask? kb '(time_varying_relation testChosenLeafOf) U)))
  (is (not (v/ask? kb '(unqualified_kinship_predicate testGeneticLeafOf) U)))
  (is (not (v/ask? kb '(unqualified_kinship_predicate testChosenLeafOf) U))))

(tu/deftest-kb constructors-have-corresponding-predicates-and-named-roots
  (is (true? (v/ask? kb '(functionCorrespondingPredicate GeneticKinFn geneticVersionOf 2) U)))
  (is (true? (v/ask? kb '(functionCorrespondingPredicate ChosenKinFn chosenVersionOf 2) U)))
  (is (true? (v/ask? kb '(rewriteOf geneticRelativeOf (GeneticKinFn kinOf)) U)))
  (is (true? (v/ask? kb '(rewriteOf chosenKinOf (ChosenKinFn kinOf)) U)))
  (is (true? (v/ask? kb '(covering kinOf geneticRelativeOf chosenKinOf) U)))
  (is (true? (v/ask? kb '(geneticVersionOf siblingOf (GeneticKinFn siblingOf)) U)))
  (is (true? (v/ask? kb '(chosenVersionOf siblingOf (ChosenKinFn siblingOf)) U))))

(tu/deftest-kb constructor-lifting-stays-on-the-unqualified-hierarchy
  (doseq [constructor [genetic chosen]]
    (is (true? (v/ask? kb (list 'genl (constructor 'siblingOf) (constructor 'kinOf)) U)))
    (is (true? (v/ask? kb (list 'genl (constructor 'siblingOf) 'siblingOf) U))))
  (let [formulas (v/query kb '(natFormula ?term ?expression) U)
        by-term (into {} (map (juxt '?term '?expression) formulas))
        qualified? #(and (sequential? %) (#{'GeneticKinFn 'ChosenKinFn} (first %)))
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
      (v/ask? kb '(genl (GeneticKinFn siblingOf) geneticRelativeOf) U))
    (is (= before [(count (v/query kb '(natFormula ?term ?expression) U)) (rule-count)])
        "repeated reads preserve the saturated formula and rule counts")))

(tu/deftest-kb generated-lifts-follow-late-source-edges-and-their-retraction
  (doseq [constructor [genetic chosen]]
    (is (not (v/ask? kb (list 'genl (constructor 'testNarrowKinshipOf)
                              (constructor 'testBroadKinshipOf)) K))))
  (let [edge (v/assert kb '(genl testNarrowKinshipOf testBroadKinshipOf) K)]
    (doseq [constructor [genetic chosen]]
      (is (true? (v/ask? kb (list 'genl (constructor 'testNarrowKinshipOf)
                                  (constructor 'testBroadKinshipOf)) K))))
    (v/retract! kb edge)
    (doseq [constructor [genetic chosen]]
      (is (not (v/ask? kb (list 'genl (constructor 'testNarrowKinshipOf)
                                (constructor 'testBroadKinshipOf)) K))))))

(tu/deftest-kb constructor-rules-preserve-exact-arity-and-minimum-arity
  (doseq [constructor [genetic chosen]]
    (is (true? (v/ask? kb (list 'arity (constructor 'siblingOf) 2) U))))
  (doseq [constructor [genetic chosen]]
    (is (true? (v/ask? kb (list 'arityMin (constructor 'testKinshipSequenceOf) 3) U)))))

(defn- derived-only?
  "Is `sentence` believed in `context` (CxUniverse by default), with every sentex stating
  it derived and none a premise?"
  ([kb sentence] (derived-only? kb sentence U))
  ([kb sentence context]
   (let [handles (map :id (v/sentexes-matching kb sentence context))]
     (and (true? (v/ask? kb sentence context))
          (seq handles)
          (not-any? #(v/premise? kb %) handles)))))

(tu/deftest-kb qualified-readings-take-their-exact-class-from-their-input
  (doseq [constructor [genetic chosen]
          predicate '[parentOf childOf motherOf fatherOf siblingOf grandparentOf ancestorOf
                      testNarrowKinshipOf]]
    (let [derived? (derived-only? kb (list 'binary_predicate (constructor predicate)))]
      (is derived? (pr-str (constructor predicate)))))
  (doseq [constructor [genetic chosen]]
    (let [classed? (v/ask? kb (list 'binary_predicate (constructor 'testKinshipSequenceOf)) U)]
      (is (not classed?) "a variable-arity input gives no exact class"))))

(tu/deftest-kb qualified-readings-keep-their-inputs-symmetry
  (doseq [constructor [genetic chosen]
          predicate '[siblingOf kinOf]]
    (let [sentence (list 'symmetric (constructor predicate))
          derived? (derived-only? kb sentence)]
      (is derived? (pr-str sentence))))
  (doseq [named '[geneticRelativeOf chosenKinOf]]
    (let [symmetric? (v/ask? kb (list 'symmetric named) U)]
      (is (true? symmetric?) (str named " is the symmetric reading of kinOf"))))
  (doseq [constructor [genetic chosen]]
    (let [symmetric? (v/ask? kb (list 'symmetric (constructor 'parentOf)) U)]
      (is (not symmetric?) "an input that is not symmetric gives no symmetric reading"))))

(tu/deftest-kb qualified-variable-policies-enforce-the-copied-minimum
  (tu/with-terms [Ann Bob Cal Dee]
    (doseq [constructor [genetic chosen]]
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
  (doseq [[sentence violation] [['(arity (GeneticKinFn siblingOf) 1) :functional]
                                ['(unary_predicate (GeneticKinFn siblingOf)) :disjoint]]]
    (let [refusal (try (v/try-assert kb sentence U) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :definitional-clash (:type refusal)))
      (is (= violation (:violation refusal)))))
  (is (true? (v/ask? kb '(arity (GeneticKinFn siblingOf) 2) U))))

(tu/deftest-kb qualified-siblings-imply-the-common-predicate-but-not-each-other
  (tu/with-terms [Ann Bob Cal Dee Elm Fox]
    (v/assert kb (list (genetic 'siblingOf) Ann Bob) K)
    (v/assert kb (list (chosen 'siblingOf) Cal Dee) K)
    (v/assert kb (list 'siblingOf Elm Fox) K)
    (is (true? (v/ask? kb (list 'siblingOf Ann Bob) K)))
    (is (true? (v/ask? kb (list 'siblingOf Cal Dee) K)))
    (is (not (proves? kb (list (chosen 'siblingOf) Ann Bob) K)))
    (is (not (proves? kb (list (genetic 'siblingOf) Cal Dee) K)))
    (doseq [constructor [genetic chosen]]
      (is (not (proves? kb (list (constructor 'siblingOf) Elm Fox) K))))))

(tu/deftest-kb ordinary-genetic-parenthood-supports-genetic-overlap-but-common-kinship-does-not
  (tu/with-terms [Ann Bob Cal Dee]
    (v/assert kb (list (genetic 'parentOf) Ann Bob) K)
    (v/assert kb (list 'parentOf Cal Dee) K)
    (is (true? (v/ask? kb (list 'sharesGenesWith Ann Bob) K)))
    (is (true? (v/ask? kb (list 'sharesGenesWith Bob Ann) K)))
    (is (not (proves? kb (list 'sharesGenesWith Cal Dee) K)))
    (is (not (proves? kb (list 'geneticRelativeOf Cal Dee) K)))
    (is (not (proves? kb (list 'chosenKinOf Cal Dee) K)))))

(tu/deftest-kb chimerism-is-orthogonal-to-every-folk-species-and-class
  (doseq [[classifier named] '{folk_species [human oak] folk_biological_class [mammal arachnid]}
          :let [found (set (keep #(let [kind (get % '?kind)] (when (symbol? kind) kind))
                                 (v/query kb (list classifier '?kind) U {:max-depth 2})))]]
    (is (seq found) (str classifier " has bindings"))
    (doseq [kind named]
      (is (contains? found kind) (str classifier " finds " kind)))
    (doseq [kind found]
      (let [orthogonal? (v/ask? kb (list 'orthogonal 'genetic_chimera kind) U)]
        (is (true? orthogonal?) (str classifier " " kind)))))
  (doseq [kind '[animal butterfly caterpillar invertebrate plant vertebrate]]
    (let [orthogonal? (v/ask? kb (list 'orthogonal 'genetic_chimera kind) U)]
      (is (true? orthogonal?) (str kind)))))

(tu/deftest-kb chimerism-blocks-the-default-without-denying-genetic-overlap
  (tu/with-terms [Ann Bob]
    (v/assert kb (list (genetic 'parentOf) Ann Bob) K)
    (is (true? (v/ask? kb (list 'sharesGenesWith Ann Bob) K)))
    (v/assert kb (list 'genetic_chimera Bob) K)
    (is (not (proves? kb (list 'sharesGenesWith Ann Bob) K)))
    (is (not (proves? kb (list 'not (list 'sharesGenesWith Ann Bob)) K)))))

(tu/deftest-kb an-ordinary-shared-genetic-parent-proves-siblings
  (tu/with-terms [Mother Ann Bob]
    (v/assert kb (list (genetic 'motherOf) Ann Mother) K)
    (v/assert kb (list (genetic 'motherOf) Bob Mother) K)
    (is (true? (v/ask? kb (list 'siblingOf Ann Bob) K)))
    (is (true? (v/ask? kb (list (genetic 'siblingOf) Ann Bob) K)))
    (is (true? (v/ask? kb (list 'sharesGenesWith Ann Bob) K)))))

(tu/deftest-kb a-shared-genetic-parent-proves-genetic-siblings-over-a-default-denial
  (tu/with-terms [Parent Ann Bob]
    (doseq [child [Ann Bob]]
      (v/assert kb (list (genetic 'parentOf) Parent child) K {:strength :monotonic}))
    (v/assert kb (list 'not (list (genetic 'siblingOf) Ann Bob)) K)
    (is (true? (v/ask? kb (list (genetic 'siblingOf) Ann Bob) K)))
    (is (not (v/ask? kb (list 'not (list (genetic 'siblingOf) Ann Bob)) K)))))

(tu/deftest-kb gestational-only-origination-stays-open-with-an-ordinary-genetic-control
  (tu/with-terms [Carrier GeneticParent Ann]
    (v/assert kb (list 'surrogateMotherOf Ann Carrier) 'CxWell)
    (v/assert kb (list 'gestationalOnlyParentOf Carrier Ann) 'CxWell)
    (v/assert kb (list (genetic 'parentOf) GeneticParent Ann) 'CxWell)
    (is (true? (v/query? kb (list 'originatorOf GeneticParent Ann) 'CxWell {:max-depth 5})))
    (is (not (v/query? kb (list 'originatorOf Carrier Ann) 'CxWell {:max-depth 5})))
    (is (not (v/query? kb (list 'not (list 'originatorOf Carrier Ann)) 'CxWell {:max-depth 5})))))

(tu/deftest-kb a-shared-gestational-carrier-is-not-a-sibling-or-genetic-proof
  (tu/with-terms [Carrier Ann Bob GeneticMotherAnn GeneticFatherAnn GeneticMotherBob GeneticFatherBob]
    (doseq [sentence [(list 'surrogateMotherOf Ann Carrier)
                      (list 'surrogateMotherOf Bob Carrier)
                      (list 'gestationalOnlyParentOf Carrier Ann)
                      (list 'gestationalOnlyParentOf Carrier Bob)
                      (list (genetic 'motherOf) Ann GeneticMotherAnn)
                      (list (genetic 'fatherOf) Ann GeneticFatherAnn)
                      (list (genetic 'motherOf) Bob GeneticMotherBob)
                      (list (genetic 'fatherOf) Bob GeneticFatherBob)]]
      (v/assert kb sentence K))
    (doseq [predicate ['siblingOf (genetic 'siblingOf) 'sharesGenesWith]]
      (is (not (proves? kb (list predicate Ann Bob) K)) (str predicate " has no proof from the carrier"))
      (is (not (proves? kb (list 'not (list predicate Ann Bob)) K)) "absence of proof is not a negative"))
    (is (not (proves? kb (list 'sharesGenesWith Carrier Ann) K)))
    (is (true? (v/ask? kb (list 'sharesGenesWith GeneticMotherAnn Ann) K)))))

(tu/deftest-kb a-carrier-who-is-also-a-chosen-parent-proves-siblings
  (tu/with-terms [Carrier Ann Bob]
    (doseq [sentence [(list 'gestationalOnlyParentOf Carrier Ann)
                      (list (chosen 'parentOf) Carrier Ann)
                      (list (chosen 'parentOf) Carrier Bob)]]
      (v/assert kb sentence K))
    (is (true? (v/ask? kb (list 'siblingOf Ann Bob) K)))))

(tu/deftest-kb chosen-siblings-start-in-2020-without-a-2019-genetic-or-common-proof
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
              predicate [(genetic 'siblingOf) 'sharesGenesWith]]
        (is (not (proves? kb (list predicate Ann Bob) context)))))))

(tu/deftest-kb common-bounds-do-not-turn-plants-into-persons-or-constructs-into-organisms
  (tu/with-terms [FernParent FernChild FirstPerson SecondPerson CxFamily]
    (v/assert kb (list 'genlCx CxFamily 'CxTra) U)
    (doseq [sentence [(list 'plant FernParent) (list 'plant FernChild)
                      (list (genetic 'parentOf) FernParent FernChild)
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

(tu/deftest-kb a-gestational-carrier-is-no-parent-or-mother-by-carrying
  (tu/with-terms [Ann Carrier]
    (doseq [sentence [(list 'surrogateMotherOf Ann Carrier)
                      (list 'gestationalOnlyParentOf Carrier Ann)]]
      (v/assert kb sentence K))
    (is (true? (v/ask? kb '(eternal_predicate gestationalOnlyParentOf) U)))
    (is (true? (v/ask? kb '(eternal_predicate surrogateMotherOf) U)))
    (is (not (v/ask? kb '(genetic_kinship_predicate gestationalOnlyParentOf) U)))
    (is (not (v/ask? kb '(genetic_kinship_predicate surrogateMotherOf) U)))
    (doseq [sentence [(list 'motherOf Ann Carrier) (list (genetic 'motherOf) Ann Carrier)
                      (list 'parentOf Carrier Ann) (list (genetic 'parentOf) Carrier Ann)
                      (list 'kinOf Carrier Ann)]]
      (is (not (proves? kb sentence K)) (str sentence " has no proof from carrying")))))

(tu/deftest-kb two-genetic-mothers-remain-distinct-and-the-function-does-not-choose
  (tu/with-terms [Ann FirstMother SecondMother]
    (doseq [sentence [(list (genetic 'motherOf) Ann FirstMother)
                      (list (genetic 'motherOf) Ann SecondMother)]]
      (v/assert kb sentence K))
    (v/assert kb (list 'comment (list 'MotherFn Ann) "An unresolved mother name") K)
    (is (true? (v/ask? kb (list (genetic 'motherOf) Ann FirstMother) K)))
    (is (true? (v/ask? kb (list (genetic 'motherOf) Ann SecondMother) K)))
    (is (not (v/same-class? kb FirstMother SecondMother)))
    (is (not (v/ask? kb (list 'functional 'motherOf) K)))
    (is (not (v/ask? kb (list 'functional (genetic 'motherOf)) K)))
    (doseq [mother [FirstMother SecondMother]]
      (is (not (proves? kb (list 'equals (list 'MotherFn Ann) mother) K))))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb a-reading-named-by-a-plain-symbol-gets-its-inputs-copied-properties
  ;; The copy rules read the correspondence, not the term's syntax. So a genetic reading
  ;; the KB names by a plain symbol, never as a GeneticKinFn application, is classed,
  ;; given its input's arity and made symmetric as one written as an application is.
  (tu/with-terms [testGeneticSiblingOf]
    (v/assert kb (list 'geneticVersionOf 'siblingOf testGeneticSiblingOf) K)
    (doseq [sentence [(list 'binary_predicate testGeneticSiblingOf)
                      (list 'arity testGeneticSiblingOf 2)
                      (list 'symmetric testGeneticSiblingOf)]]
      (is (true? (v/ask? kb sentence K)) (pr-str sentence)))))

(tu/deftest-kb a-later-unqualified-predicate-gets-its-readings-reified
  ;; The fixture declares testNewKinOf and testNewSymmetricKinOf as inputs and nothing
  ;; names (GeneticKinFn testNewKinOf) or its chosen twin. GeneticKinFn and ChosenKinFn
  ;; are eagerly_reifiable_function members, so each reading is reified, and the copy
  ;; rules read it through geneticVersionOf and chosenVersionOf.
  (doseq [constructor [genetic chosen]
          input '[testNewKinOf testNewSymmetricKinOf]
          sentence [(list 'reify (constructor input))
                    (list 'binary_predicate (constructor input))
                    (list 'arity (constructor input) 2)
                    (list 'genl (constructor input) input)]]
    (is (true? (v/ask? kb sentence U)) (pr-str sentence)))
  (doseq [constructor [genetic chosen]]
    (is (true? (v/ask? kb (list 'symmetric (constructor 'testNewSymmetricKinOf)) U)))
    (is (not (v/ask? kb (list 'symmetric (constructor 'testNewKinOf)) U)))))
