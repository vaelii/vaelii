;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.meta-test
  "The vocabulary context and meta-level features over the starter schema (with
  the test-world beneath it):

    * the context topology — CxUniverse ⊏ middle ⊏ CxWell;
    * the predicate meta-ontology — predicates classified by arity and by the
      algebraic properties their metadata declares (each mark is itself a
      binary_predicate type, so the property is the classification);
    * decontextualized_predicate — a fact stated in one context deduced into
      CxUniverse and thereby visible everywhere."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.walk :as walk]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.except :as exc]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb the-context-topology-universe-middle-well
  (testing "middle rides between Universe and Well"
    (is (seq (v/sentexes-matching kb '(genlCx CxBiology CxUniverse) '?ctx)))
    (is (seq (v/sentexes-matching kb '(genlCx CxWell CxBiology) '?ctx))))
  (testing "there is no direct Well→Universe edge, but Universe is transitively visible from Well"
    (is (empty? (v/sentexes-matching kb '(genlCx CxWell CxUniverse) '?ctx)))
    (is (tax/sees? (reasoning/taxonomy kb) 'CxWell 'CxUniverse)))
  (testing "the upper vocabulary is visible from CxUniverse and the data contexts"
    (is (v/ask? kb '(binary_predicate genl) 'CxUniverse))
    (is (v/ask? kb '(binary_predicate parentOf) 'CxNaturalWorld)))
  (testing "the upper ontology is stored in CxUniverse, and data in the data contexts"
    (is (seq   (v/sentexes-matching kb '(genl dog mammal) 'CxUniverse)))
    (is (seq   (v/sentexes-matching kb '(human Tom) 'CxNaturalWorld)))))

(tu/deftest-kb predicates-classified-by-arity
  (testing "unary — every type, and one-place properties"
    (is (v/isa? kb 'dog 'unary_predicate))
    (is (v/isa? kb 'thing 'unary_predicate))
    (is (v/isa? kb 'awake 'unary_predicate)))
  (testing "binary and ternary"
    (is (v/isa? kb 'parentOf 'binary_predicate))
    (is (v/isa? kb 'genl 'binary_predicate))
    (is (v/isa? kb 'arg 'ternary_predicate)))
  (testing "everything classified is a predicate, hence a thing"
    (is (v/isa? kb 'parentOf 'predicate))
    (is (v/isa? kb 'dog 'predicate))
    (is (v/isa? kb 'parentOf 'thing)))
  (testing "negatives"
    (is (not (v/isa? kb 'dog 'binary_predicate)))
    (is (not (v/isa? kb 'siblingOf 'unary_predicate)))))

(tu/deftest-kb an-asserted-arity-concludes-the-class-and-a-class-is-read-as-the-arity
  (testing "arity is itself a binary predicate"
    (is (v/isa? kb 'arity 'binary_predicate)))
  (testing "no rule concludes an arity from a class: arity is on the forced-monotonic roster"
    (is (empty? (v/sentexes-matching kb '(arity dog 1) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(arity parentOf 2) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(arity arg 3) '?ctx))))
  (testing "every reader of an arity reads the exact-class membership, the same at every context"
    (is (= 2 (:arity (v/describe kb 'parentOf 'CxUniverse))))
    (is (= 2 (:arity (v/describe kb 'siblingOf 'CxUniverse))))        ; symmetric -> binary
    (is (= 3 (:arity (v/describe kb 'arg 'CxUniverse))))
    (is (= 2 (:arity (v/describe kb 'parentOf 'CxBiology)))
        "a declaration in CxUniverse binds the length a middle context reads")
    (is (v/ask? kb '(admitsArgnum parentOf 2) 'CxNaturalWorld))
    (is (not (v/ask? kb '(admitsArgnum parentOf 3) 'CxNaturalWorld))))
  (testing "an asserted arity concludes the relation-wide class, not the kind"
    (tu/with-terms [fooRelation]
      (v/assert kb (list 'arity fooRelation 2) 'CxUniverse)
      (is (v/isa? kb fooRelation 'binary) "the converse reaches the relation-wide class")
      (is (not (v/isa? kb fooRelation 'binary_predicate))
          "two arguments is a shape a function has too, so the kind stays open")
      (is (not (v/isa? kb fooRelation 'predicate)))
      (is (v/isa? kb fooRelation 'relation))
      (is (v/isa? kb fooRelation 'fixed_arity))
      (is (seq (v/sentexes-matching kb (list 'fixed_arity fooRelation) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'binary fooRelation) 'CxUniverse)))))
  (testing "the fixed policy is justified by the arity fact and the rule"
    (tu/with-terms [barRelation]
      (v/assert kb (list 'arity barRelation 3) 'CxUniverse)
      (let [h (v/handle-of kb (list 'fixed_arity barRelation) 'CxUniverse)
            rule (v/handle-of kb '(implies (arity ?relation ?arity)
                                           (fixed_arity ?relation)) 'CxUniverse)]
        (is (some? h))
        (is (some? rule))
        (is (some (fn [d]
                    (and (= rule (:informant d))
                         (some #(= (list 'arity barRelation 3)
                                   (:sentence (v/sentex kb %)))
                               (:antecedents d))))
                  (v/supporting-justifications kb h)))
        (is (v/isa? kb barRelation 'ternary))
        (is (not (v/isa? kb barRelation 'ternary_predicate)))))))

(tu/deftest-kb arity-conclusions-retract-with-their-declarations
  (testing "asserting the arity keeps the arity, the class and the policy believed"
    (tu/with-terms [binaryRelation]
      (let [h (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)]
        (is (seq (v/sentexes-matching kb (list 'arity binaryRelation 2) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list 'fixed_arity binaryRelation) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list 'binary binaryRelation) 'CxUniverse)))
        (testing "and retracting the sole premise collapses the whole cycle"
          (v/retract! kb h)
          (is (empty? (v/sentexes-matching kb (list 'binary binaryRelation) 'CxUniverse)))
          (is (empty? (v/sentexes-matching kb (list 'fixed_arity binaryRelation) 'CxUniverse)))
          (is (empty? (v/sentexes-matching kb (list 'arity binaryRelation 2) 'CxUniverse)))))))
  (testing "a specialized predicate witness keeps its type, arity, and predicate policy"
    (tu/with-terms [qPred]
      (let [h (v/assert kb (list 'unary_predicate qPred) 'CxUniverse)]
        (is (v/isa? kb qPred 'unary))
        (is (v/isa? kb qPred 'fixed_arity_predicate))
        (is (= 1 (:arity (v/describe kb qPred 'CxUniverse))))
        (testing "and retracting it takes the arity with the class"
          (v/retract! kb h)
          (is (nil? (:arity (v/describe kb qPred 'CxUniverse)))))))))

(tu/deftest-kb algebraic-predicate-types-classify-a-predicate
  ;; (symmetric siblingOf) etc. are the marks the provers read AND, since each mark is a
  ;; type — (genl symmetric binary_predicate) in CxUniverse — the classification itself: the
  ;; property IS the membership, with no derived (…Predicate) twin between them.
  (testing "the mark is a membership in the property type"
    (is (v/isa? kb 'siblingOf 'symmetric))
    (is (v/isa? kb 'marriedTo 'symmetric))
    (is (v/isa? kb 'ancestorOf 'transitive))
    (is (v/isa? kb 'tangiblePartOf 'transitive))
    (is (v/isa? kb 'birthYearOf 'functional)))
  (testing "and inherit binary_predicate / predicate through genl"
    (is (v/isa? kb 'siblingOf 'binary_predicate))
    (is (v/isa? kb 'ancestorOf 'predicate)))
  (testing "the mark is stated in CxUniverse, so it is visible from every data context"
    (is (seq (v/sentexes-matching kb '(symmetric siblingOf) 'CxUniverse)))
    (is (v/ask? kb '(symmetric siblingOf) 'CxSocialWorld))))

(tu/deftest-kb algebraic-predicate-types-answer-and-enumerate
  (testing "membership is answered directly from the stored mark"
    (is (v/ask? kb '(symmetric siblingOf)))
    (is (v/ask? kb '(transitive ancestorOf)))
    (is (v/ask? kb '(functional birthYearOf)))
    (is (not (v/ask? kb '(symmetric parentOf)))))
  (testing "and enumerated"
    ;; the domain relations and orthogonal are the symmetric marks, decontextualized like
    ;; the other algebraic marks, so they answer the enumeration wherever CxUniverse is
    ;; seen.  seeAlso is NOT among them — it is a directional cross-reference, not
    ;; symmetric.  The social relations (CxSocial and CxSocialExtension) are among them:
    ;; their marks are stated in CxUniverse like the rest, and ?ctx is open.
    (is (= '#{siblingOf marriedTo friendOf orthogonal siblingDisjointException
              relativeOf romanticPartnerOf coworkerOf roommateOf
              nestingPartnerOf chosenSiblingOf}
           (set (map #(get % '?p) (v/ask kb '(symmetric ?p) '?ctx)))))
    ;; `genl` and `genlCx` are in the enumeration because core.txt asserts (transitive genl)
    ;; / (transitive genlCx) outright.  They *are* transitive; answering them from cached
    ;; closures instead of the generic prover is an implementation choice, not a difference
    ;; in what they mean — and saying so is what lets them be named as the relation an
    ;; argument position is preserved along (docs/inherit.md).  The declaration is held out
    ;; of the :transitive prop machinery (the closure-relations skip-set), so it stays a
    ;; queryable classification without routing them to the generic prover — which is why
    ;; they do not appear in `(props kb :transitive)`.
    ;; `heavierThan` / `tallerThan` / `olderThan` are the instance-level strict orders,
    ;; transitive beside `typeLargerThan`'s type-level claim: two stated comparisons compose
    ;; into the third off the closure, which is the route a KB that weighed nothing has.
    ;; `greaterInMagnitudeThan` is the fourth, over quantities rather than objects.
    ;; `instantBefore` / `instantAfter` are the point algebra's strict orders, transitive
    ;; so a forward join reads a narrative's consecutive links as one ordering.
    (is (= '#{ancestorOf partOf permanentPartOf tangiblePartOf subSituationOf properPartOf properTangiblePartOf
              properSubSituationOf properPartOfRegion properSubintervalOf locatedIn typeLargerThan instantBefore instantAfter
              causes beforeEvent genl genlCx
              heavierThan tallerThan olderThan greaterInMagnitudeThan}
           (set (map #(get % '?p) (v/ask kb '(transitive ?p) '?ctx)))))
    (is (not (v/has-prop? kb :transitive 'genl)))))

(tu/deftest-kb genlcx-is-a-forced-decontextualized-predicate
  (testing "a genlCx edge is forced to live in CxUniverse, wherever asserted"
    (is (seq   (v/sentexes-matching kb '(genlCx CxBiology CxUniverse) 'CxUniverse)))
    (is (empty? (v/sentexes-matching kb '(genlCx CxBiology CxUniverse) 'CxBiology)))))

;; ---- forced_monotonic_predicate: the roster no default reaches ----------------------

(defn- predicate-spelled
  "A fresh predicate spelled camelCase, which a predicate `genl` needs: `tu/with-terms`
  folds a predicate temp to bare lowercase, the spelling a type shares."
  [base]
  (gensym (str "tmp" base)))

(tu/deftest-kb a-default-write-of-each-roster-group-keeps-its-strength
  (tu/with-terms [CxLow parentOf dog_kind cat_kind bird_kind Ann Bob Cal Dan]
    (let [fatherOf (predicate-spelled "FatherOf")
          kinOf    (predicate-spelled "KinOf")
          fact     (v/assert kb (list parentOf Ann Bob) CxLow)
          rows     [["a relation mark" (list 'functional parentOf)             'CxUniverse]
                    ["predicate genl"  (list 'genl fatherOf kinOf)             'CxUniverse]
                    ["a declaration"   (list 'disjoint dog_kind cat_kind)      'CxUniverse]
                    ["except"          (list 'except (sx/sentex-handle fact))  CxLow]
                    ["equality"        (list 'sameAs Cal Dan)                  CxLow]]]
      (doseq [[group s c] rows]
        (testing group
          (is (= :default (v/defeat-class kb (v/assert kb s c)))))))
    (testing "and so does a genl between types"
      (is (= :default (v/defeat-class kb (v/assert kb (list 'genl bird_kind cat_kind) 'CxUniverse)))))
    (testing "a genlCx edge is read :monotonic, so it caps no firing's class"
      (is (= :monotonic (v/defeat-class kb (v/assert kb (list 'genlCx CxLow 'CxUniverse) 'CxUniverse)))))))

(tu/deftest-kb a-late-declaration-leaves-the-premises-before-it-at-their-strength
  (tu/with-terms [likes Ann Bob Cal]
    (let [hs (mapv #(v/assert kb (list likes Ann %) 'CxUniverse) [Bob Cal Ann])]
      (is (= [:default :default :default] (mapv #(v/defeat-class kb %) hs)))
      (v/assert kb (list 'forced_monotonic_predicate likes) 'CxUniverse)
      (is (= [:default :default :default] (mapv #(v/defeat-class kb %) hs))))))

(defn- inert?
  "Is handle `h` stored, not believed, and reported `:inert` by `why-not`."
  [kb h]
  (and (some? (v/sentex kb h)) (not (v/in? kb h)) (= :inert (:reason (v/why-not kb h)))))

(tu/deftest-kb a-denial-of-a-roster-literal-is-stored-inert-in-either-order
  (tu/with-terms [CxLow parentOf dog_kind cat_kind likes Ann Bob Cal Dan]
    (let [fatherOf (predicate-spelled "FatherOf")
          kinOf    (predicate-spelled "KinOf")]
      (testing "beside the literal it denies, which keeps its belief"
        (doseq [s [(list 'genlCx CxLow 'CxUniverse)
                   (list 'functional parentOf)
                   (list 'genl fatherOf kinOf)
                   (list 'disjoint dog_kind cat_kind)
                   (list 'sameAs Ann Bob)]]
          (let [h (v/assert kb s 'CxUniverse)]
            (is (empty? (v/check kb (list 'not s) 'CxUniverse)) (pr-str s))
            (is (inert? kb (v/assert kb (list 'not s) 'CxUniverse)) (pr-str s))
            (is (v/in? kb h) (pr-str s)))))
      (testing "a genl between types is not on the roster, and its denial is believed"
        (is (v/in? kb (v/assert kb (list 'not (list 'genl dog_kind cat_kind)) 'CxUniverse))))
      (testing "a declaration arriving after a stored denial makes it inert"
        (let [d (v/assert kb (list 'not (list likes Cal Dan)) 'CxUniverse)]
          (is (v/in? kb d))
          (v/assert kb (list 'forced_monotonic_predicate likes) 'CxUniverse)
          (is (inert? kb d))
          (is (= d (v/assert kb (list 'not (list likes Cal Dan)) 'CxUniverse))
              "the declaration arriving first stores the same record"))))))

(tu/deftest-kb why-not-of-an-inert-denial-names-the-literal-and-what-puts-it-on-the-roster
  (tu/with-terms [dog_kind cat_kind likes Cal Dan]
    (testing "a literal the engine's own roster holds, beside the literal it denies"
      (let [s (list 'disjoint dog_kind cat_kind)
            h (v/assert kb s 'CxUniverse)
            d (v/assert kb (list 'not s) 'CxUniverse)]
        (is (= {:sentence s :handle h :believed? true
                :roster {:predicate 'disjoint :kind :forced-monotonic :global? true
                         :declarations [(v/handle-of kb '(forced_monotonic_predicate disjoint)
                                                     'CxUniverse)]}}
               (:denies (v/why-not kb d))))))
    (testing "a literal a declaration puts on the roster, with no literal stored"
      (let [decl (v/assert kb (list 'forced_monotonic_predicate likes) 'CxUniverse)
            d    (v/assert kb (list 'not (list likes Cal Dan)) 'CxUniverse)]
        (is (= {:sentence (list likes Cal Dan) :handle nil :believed? false
                :roster {:predicate likes :kind :forced-monotonic :global? false
                         :declarations [decl]}}
               (:denies (v/why-not kb d))))))))

(defn- forced-entries
  "The `:forced-conclusion` entries `violations` reads about a conclusion in `context`,
  or about the stored spelling of `s` there."
  ([kb context] (forced-entries kb nil context))
  ([kb s context]
   (let [stored (when s (or (some->> (v/handle-of kb s context) (v/sentex kb) :sentence) s))]
     (filterv #(and (= :forced-conclusion (:violation %)) (= context (:context %))
                    (or (nil? s) (= stored (:sentence %))))
              (v/violations kb)))))

(defn- concluded?
  "`[believed? reported?]`: is `s` believed at `context` (default `CxUniverse`), and does
  `violations` read a `:forced-conclusion` entry about it."
  ([kb s] (concluded? kb s 'CxUniverse))
  ([kb s context]
   [(v/ask? kb s context) (boolean (seq (forced-entries kb s context)))]))

(tu/deftest-kb a-rule-concludes-a-roster-literal-only-from-roster-antecedents
  (tu/with-terms [strict_kind flies_kind bird_kind parentOf siblingOf Tweety]
    (testing "a non-roster antecedent: the rule is stored, and its firing is dropped and reported"
      (v/assert kb (list 'set/forwardRule (list 'implies (list strict_kind '?p) (list 'asymmetric '?p)))
                'CxUniverse)
      (v/assert kb (list strict_kind parentOf) 'CxUniverse)
      (is (= [false true] (concluded? kb (list 'asymmetric parentOf)))))
    (testing "roster antecedents: the conclusion is believed at its antecedents' class"
      (let [r (v/assert kb (list 'set/forwardRule
                                 (list 'implies (list 'anti_transitive '?p) (list 'irreflexive '?p)))
                        'CxUniverse)]
        (is (= :default (v/defeat-class kb r)) "the rule keeps the strength it was written at")
        (v/assert kb (list 'anti_transitive siblingOf) 'CxUniverse {:strength :monotonic})
        (is (= [true false] (concluded? kb (list 'irreflexive siblingOf))))
        (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list 'irreflexive siblingOf)
                                                          'CxUniverse))))))
    (testing "a declaration arriving after a firing drops it, as arriving first does"
      (v/assert kb (list 'set/forwardRule (list 'implies (list bird_kind '?x) (list flies_kind '?x)))
                'CxUniverse)
      (v/assert kb (list bird_kind Tweety) 'CxUniverse)
      (is (v/ask? kb (list flies_kind Tweety) 'CxUniverse))
      (v/assert kb (list 'forced_monotonic_predicate flies_kind) 'CxUniverse)
      (is (= [false true] (concluded? kb (list flies_kind Tweety)))))))

(defn- definitional-rule
  "A forward rule concluding `(orthogonal ?s made)` from the membership `(trigger ?s)`
  and the further antecedents `more`, each over `?s`."
  [trigger made & more]
  (list 'set/forwardRule
        (list 'implies (apply list 'and (list trigger '?s) more) (list 'orthogonal '?s made))))

(tu/deftest-kb why-not-names-the-conviction-of-a-void-firing
  (tu/with-terms [trigger_kind made_kind species_kind]
    (let [r (v/assert kb (definitional-rule trigger_kind made_kind) 'CxUniverse)]
      (v/assert kb (list trigger_kind species_kind) 'CxUniverse)
      (let [h (v/handle-of kb (list 'orthogonal species_kind made_kind) 'CxUniverse)
            w (v/why-not kb h)]
        (is (some? h) "the firing is stored")
        (is (= :forced-conclusion (:reason w)))
        (is (= [[r [trigger_kind]]] (mapv (juxt :informant :off-roster) (:convicted w))))))))

(tu/deftest-kb the-forced-conclusion-report-names-the-antecedents-off-the-roster
  (tu/with-terms [trigger_kind other_kind made_kind rival_kind species_kind]
    (v/assert kb (definitional-rule trigger_kind made_kind (list other_kind '?s)
                   (list 'disjoint '?s rival_kind))
              'CxUniverse)
    (doseq [s [(list trigger_kind species_kind) (list other_kind species_kind)
               (list 'disjoint species_kind rival_kind)]]
      (v/assert kb s 'CxUniverse))
    (let [vs (forced-entries kb (list 'orthogonal species_kind made_kind) 'CxUniverse)]
      (is (= [#{trigger_kind other_kind}] (mapv (comp set :off-roster :detail) vs))
          "disjoint is on the roster and is not named")
      (is (every? #(and (str/includes? % (str trigger_kind)) (str/includes? % (str other_kind)))
                  (map (comp :message :detail) vs))))))

(tu/deftest-kb a-forced-trigger-keeps-its-strength-and-its-conclusion-takes-it
  (tu/with-terms [trigger_kind made_kind species_kind]
    (v/assert kb (list 'forced_monotonic_predicate trigger_kind) 'CxUniverse)
    (v/assert kb (definitional-rule trigger_kind made_kind) 'CxUniverse)
    (let [t (v/assert kb (list trigger_kind species_kind) 'CxUniverse)
          c (list 'orthogonal species_kind made_kind)]
      (is (= :default (v/defeat-class kb t)))
      (is (= [true false] (concluded? kb c)))
      (is (= :default (v/defeat-class kb (v/handle-of kb c 'CxUniverse))))
      (v/retract! kb t)
      (is (nil? (v/handle-of kb c 'CxUniverse)) "retracting the trigger sweeps the conclusion"))))

(tu/deftest-kb forcing-a-trigger-moves-the-verdict-not-the-class
  ;; [forced? rival strength] -> [trigger believed? rival believed? conclusion believed?
  ;; hard clash?]; the trigger keeps class :default in every row
  (doseq [[forced? rival-strength expected]
          [[false :default   [true  true  false false]]   ; a dilemma
           [false :monotonic [false true  false false]]   ; the trigger loses
           [true  :default   [true  false true  false]]   ; the rival loses
           [true  :monotonic [true  true  true  true]]]]  ; a hard clash
    (tu/with-terms [trigger_kind rival_kind made_kind species_kind]
      (let [why (str "forced " forced? ", rival " rival-strength)
            c   (list 'orthogonal species_kind made_kind)]
        (when forced? (v/assert kb (list 'forced_monotonic_predicate trigger_kind) 'CxUniverse))
        (v/assert kb (list 'disjoint trigger_kind rival_kind) 'CxUniverse {:strength :monotonic})
        (v/assert kb (definitional-rule trigger_kind made_kind) 'CxUniverse)
        (let [t (v/assert kb (list trigger_kind species_kind) 'CxUniverse)
              v (v/assert kb (list rival_kind species_kind) 'CxUniverse {:strength rival-strength})]
          (is (= expected [(v/ask? kb (list trigger_kind species_kind) 'CxUniverse)
                           (v/ask? kb (list rival_kind species_kind) 'CxUniverse)
                           (v/ask? kb c 'CxUniverse)
                           (boolean (some #(= #{t v} (set (:nogood %))) (v/conflicts kb)))])
              why)
          (is (= :default (v/defeat-class kb t)) why)))))
  (testing "a denial of a forced trigger is inert, and the trigger and its consequences stand"
    (doseq [forced? [false true]]
      (tu/with-terms [trigger_kind made_kind species_kind qq]
        (when forced? (v/assert kb (list 'forced_monotonic_predicate trigger_kind) 'CxUniverse))
        (v/assert kb (definitional-rule trigger_kind made_kind) 'CxUniverse)
        (v/assert kb (list 'set/forwardRule (list 'implies (list trigger_kind '?s) (list qq '?s)))
                  'CxUniverse)
        (let [t (list trigger_kind species_kind)
              d (v/assert kb (list 'not t) 'CxUniverse {:strength :monotonic})]
          (v/assert kb t 'CxUniverse)
          (is (= [forced? forced? forced? forced?]
                 [(inert? kb d) (v/ask? kb t 'CxUniverse) (v/ask? kb (list qq species_kind) 'CxUniverse)
                  (v/ask? kb (list 'orthogonal species_kind made_kind) 'CxUniverse)])
              (str "forced " forced?)))))))

;; ---- a declaration forces its predicate where it is seen ----------------------------

(defn- orders
  "Every ordering of `xs`."
  [xs]
  (if (empty? xs) [()] (for [x xs, more (orders (remove #{x} xs))] (cons x more))))

(defn- sampled
  "The first and the last of `orders`, each write's reverse of the other: the sample a
  sweep's twin at `:default` runs."
  [orders]
  [(first orders) (last orders)])

(defn- roster-reading
  "Assert the `fixed` writes, then the `writes` (`{key [sentence context strength]}`) in
  `order`, and with `retract` retract that write last.  Answers `{key [believed? …]}`,
  each `ask?` of `asked` at the context `ctxs` names under that key."
  [kb ctxs {:keys [fixed writes order asked retract]}]
  (doseq [[s c st] (concat fixed (map writes order))]
    (v/assert kb s c {:strength (or st :default)}))
  (when retract
    (let [[s c] (writes retract)] (v/retract! kb (v/handle-of kb s c))))
  (into {} (for [[k c] ctxs] [k (mapv #(v/ask? kb % c) asked)])))

(defn- scoped-contexts
  "CxA and CxB under CxU under CxUniverse, each edge `:monotonic`."
  [cu ca cb]
  (for [[sub super] [[cu 'CxUniverse] [ca cu] [cb cu]]]
    [(list 'genlCx sub super) 'CxUniverse :monotonic]))

(defn- declaration-seen-reading
  "[trigger rival conclusion] in each order `pick` keeps: CxA sees the declaration, so
  the rival loses and the definitional firing stands there; CxB and CxU do not, so the
  pair is a dilemma and the firing is void.  Retracting the declaration leaves the
  reading of a KB that never held it at all three."
  [kb pick]
  (doseq [order   (pick (orders [:decl :trigger :rival :rule]))
          retract [nil :decl]]
    (tu/with-terms [CxU CxA CxB trigger_kind rival_kind made_kind species_kind]
      (let [world {:fixed  (concat (scoped-contexts CxU CxA CxB)
                                   [[(list 'disjoint trigger_kind rival_kind) CxU :monotonic]])
                   :writes {:decl    [(list 'forced_monotonic_predicate trigger_kind) CxA]
                            :trigger [(list trigger_kind species_kind) CxU]
                            :rival   [(list rival_kind species_kind) CxU]
                            :rule    [(definitional-rule trigger_kind made_kind) CxU]}
                   :order  order :retract retract
                   :asked  [(list trigger_kind species_kind) (list rival_kind species_kind)
                            (list 'orthogonal species_kind made_kind)]}]
        (is (= (if retract
                 {:a [true true false] :b [true true false] :u [true true false]}
                 {:a [true false true] :b [true true false] :u [true true false]})
               (roster-reading kb {:a CxA :b CxB :u CxU} world))
            (str "order " (vec order) (when retract ", declaration retracted")))))))

(tu/deftest-kb a-declaration-forces-a-verdict-and-a-firing-only-where-it-is-seen
  (declaration-seen-reading kb sampled))

(tu/deftest-kb ^:slow a-declaration-forces-a-verdict-and-a-firing-only-where-it-is-seen-in-every-order
  (declaration-seen-reading kb identity))

(tu/deftest-kb a-declaration-makes-a-denial-inert-only-where-it-is-seen
  ;; [trigger denial] in every arrival order: CxA sees the declaration, so the denial is
  ;; inert and the trigger stands; at CxB and CxU the :monotonic denial defeats the
  ;; :default trigger.  Retracting the declaration leaves that reading at CxA too.
  (doseq [order   (orders [:decl :denial :trigger])
          retract [nil :decl]]
    (tu/with-terms [CxU CxA CxB trigger_kind species_kind]
      (let [t     (list trigger_kind species_kind)
            world {:fixed  (scoped-contexts CxU CxA CxB)
                   :writes {:decl    [(list 'forced_monotonic_predicate trigger_kind) CxA]
                            :denial  [(list 'not t) CxU :monotonic]
                            :trigger [t CxU]}
                   :order  order :retract retract
                   :asked  [t (list 'not t)]}]
        (is (= (if retract
                 {:a [false true] :b [false true] :u [false true]}
                 {:a [true false] :b [false true] :u [false true]})
               (roster-reading kb {:a CxA :b CxB :u CxU} world))
            (str "order " (vec order) (when retract ", declaration retracted")))))))

(tu/deftest-kb a-declared-conclusion-is-void-only-where-the-declaration-is-seen
  ;; [conclusion] in every arrival order: a rule at CxU concludes `(trigger_kind s)` from
  ;; an antecedent off the roster.  CxA sees the declaration, so the firing is void there;
  ;; CxB and CxU do not, so the conclusion is an ordinary belief.  Retracting the
  ;; declaration leaves it believed at all three.
  (doseq [order   (orders [:decl :rule :fact])
          retract [nil :decl]]
    (tu/with-terms [CxU CxA CxB trigger_kind seed_kind species_kind]
      (let [world {:fixed  (scoped-contexts CxU CxA CxB)
                   :writes {:decl [(list 'forced_monotonic_predicate trigger_kind) CxA]
                            :rule [(list 'set/forwardRule (list 'implies (list seed_kind '?s)
                                                                (list trigger_kind '?s)))
                                   CxU]
                            :fact [(list seed_kind species_kind) CxU]}
                   :order  order :retract retract
                   :asked  [(list trigger_kind species_kind)]}]
        (is (= (if retract
                 {:a [true] :b [true] :u [true]}
                 {:a [false] :b [true] :u [true]})
               (roster-reading kb {:a CxA :b CxB :u CxU} world))
            (str "order " (vec order) (when retract ", declaration retracted")))))))

(tu/deftest-kb why-not-names-the-conviction-of-a-declared-conclusion-where-it-is-seen
  (tu/with-terms [CxU CxA CxB trigger_kind seed_kind species_kind]
    (doseq [[s c st] (scoped-contexts CxU CxA CxB)] (v/assert kb s c {:strength st}))
    (v/assert kb (list 'forced_monotonic_predicate trigger_kind) CxU)
    (let [r (v/assert kb (list 'set/forwardRule (list 'implies (list seed_kind '?s)
                                                      (list trigger_kind '?s)))
                      CxU)
          c (list trigger_kind species_kind)]
      (v/assert kb (list seed_kind species_kind) CxU)
      (let [w (v/why-not kb c CxU)]
        (is (= :forced-conclusion (:reason w)))
        (is (= [[r [seed_kind]]] (mapv (juxt :informant :off-roster) (:convicted w)))))
      (is (= 1 (count (forced-entries kb c CxU))) "the firing is void at a reader"))))

(tu/deftest-kb a-late-declaration-defeats-the-rival-of-a-standing-dilemma
  ;; [trigger rival] at one context: the declaration turns the dilemma into a defeat of
  ;; the rival whether it arrives before or after the pair
  (doseq [order (orders [:decl :trigger :rival])]
    (tu/with-terms [CxU trigger_kind rival_kind species_kind]
      (is (= {:u [true false]}
             (roster-reading kb {:u CxU}
                             {:fixed  [[(list 'genlCx CxU 'CxUniverse) 'CxUniverse :monotonic]
                                       [(list 'disjoint trigger_kind rival_kind) CxU :monotonic]]
                              :writes {:decl    [(list 'forced_monotonic_predicate trigger_kind) CxU]
                                       :trigger [(list trigger_kind species_kind) CxU]
                                       :rival   [(list rival_kind species_kind) CxU]}
                              :order  order
                              :asked  [(list trigger_kind species_kind) (list rival_kind species_kind)]}))
          (str "order " (vec order))))))

(tu/deftest-kb a-cxuniverse-declaration-moves-the-verdict-in-every-order
  ;; [declaration trigger rival] at one context, the declaration stated in CxUniverse or at the
  ;; context, the rival at either strength, the declaration retracted last or kept: every
  ;; order gives the answer of the KB that held the same content from the start
  (doseq [[decl-cx rival-strength retract expected]
          [[:at       :default   nil   [true false]]
           [:core     :default   nil   [true false]]
           [:core     :default   :decl [true true]]
           [:at       :monotonic nil   [true true]]
           [:core     :monotonic nil   [true true]]
           [:core     :monotonic :decl [false true]]]
          order (orders [:decl :trigger :rival])]
    (tu/with-terms [CxU trigger_kind rival_kind species_kind]
      (is (= {:u expected}
             (roster-reading kb {:u CxU}
                             {:fixed  [[(list 'genlCx CxU 'CxUniverse) 'CxUniverse :monotonic]
                                       [(list 'disjoint trigger_kind rival_kind) CxU :monotonic]]
                              :writes {:decl    [(list 'forced_monotonic_predicate trigger_kind)
                                                 (if (= :core decl-cx) 'CxUniverse CxU)]
                                       :trigger [(list trigger_kind species_kind) CxU]
                                       :rival   [(list rival_kind species_kind) CxU rival-strength]}
                              :order  order :retract retract
                              :asked  [(list trigger_kind species_kind) (list rival_kind species_kind)]}))
          (str "declared " decl-cx ", rival " rival-strength ", order " (vec order)
               (when retract ", declaration retracted"))))))

(tu/deftest-kb a-cxuniverse-declaration-retracted-beside-another-moves-nothing-it-did-not-force
  ;; CxA states the declaration too: retracting CxUniverse's leaves CxA forcing the trigger
  ;; and CxB reading the dilemma, in every order of the four writes
  (doseq [order (orders [:core :decl-a :trigger :rival])]
    (tu/with-terms [CxU CxA CxB trigger_kind rival_kind species_kind]
      (let [decl (list 'forced_monotonic_predicate trigger_kind)]
        (is (= {:a [true false] :b [true true]}
               (roster-reading kb {:a CxA :b CxB}
                               {:fixed  (concat (scoped-contexts CxU CxA CxB)
                                                [[(list 'disjoint trigger_kind rival_kind) CxU :monotonic]])
                                :writes {:core    [decl 'CxUniverse]
                                         :decl-a  [decl CxA]
                                         :trigger [(list trigger_kind species_kind) CxU]
                                         :rival   [(list rival_kind species_kind) CxU]}
                                :order  order :retract :core
                                :asked  [(list trigger_kind species_kind) (list rival_kind species_kind)]}))
            (str "order " (vec order)))))))

(defn- cxuniverse-declaration-reading
  "CxA, CxB and CxDen under CxU; CxA states the declaration too, in each order `pick`
  keeps.  A :monotonic denial of the CxUniverse declaration at CxDen defeats it there alone,
  so CxDen reads the dilemma and CxA and CxB force the trigger.  The denial at CxUniverse
  defeats the declaration at every context, CxA's copy included, so no reader forces
  anything."
  [kb pick]
  (doseq [[deny-cx expected] [[:den  {:a [true false] :b [true false] :d [true true]}]
                              [:core {:a [true true]  :b [true true]  :d [true true]}]]
          order (pick (orders [:core :deny :decl-a :trigger :rival]))]
    (tu/with-terms [CxU CxA CxB CxDen trigger_kind rival_kind species_kind]
      (let [decl (list 'forced_monotonic_predicate trigger_kind)]
        (is (= expected
               (roster-reading kb {:a CxA :b CxB :d CxDen}
                               {:fixed  (concat (scoped-contexts CxU CxA CxB)
                                                [[(list 'genlCx CxDen CxU) 'CxUniverse :monotonic]
                                                 [(list 'disjoint trigger_kind rival_kind) CxU :monotonic]])
                                :writes {:core    [decl 'CxUniverse]
                                         :deny    [(list 'not decl) (if (= :core deny-cx) 'CxUniverse CxDen)
                                                   :monotonic]
                                         :decl-a  [decl CxA]
                                         :trigger [(list trigger_kind species_kind) CxU]
                                         :rival   [(list rival_kind species_kind) CxU]}
                                :order  order
                                :asked  [(list trigger_kind species_kind) (list rival_kind species_kind)]}))
            (str "denial at " deny-cx ", order " (vec order)))))))

(tu/deftest-kb a-cxuniverse-declaration-forces-only-where-it-is-believed
  (cxuniverse-declaration-reading kb sampled))

(tu/deftest-kb ^:slow a-cxuniverse-declaration-forces-only-where-it-is-believed-in-every-order
  (cxuniverse-declaration-reading kb identity))

(tu/deftest-kb an-except-of-a-defeat-releases-the-loser-beside-a-declaration-elsewhere
  ;; CxU holds a :monotonic (kind_a s) and a :default (kind_b s) under a :monotonic
  ;; `disjoint`; CxR is below CxU and excepts the defeat of (kind_b s).  CxR reads the pair
  ;; as a dilemma, with or without a declaration of kind_b in CxFoo, which CxR does not see.
  (doseq [declared? [false true]]
    (tu/with-terms [CxU CxFoo CxR kind_a kind_b Sp]
      (let [M  {:strength :monotonic}
            ab (fn [c] [(v/ask? kb (list kind_a Sp) c) (v/ask? kb (list kind_b Sp) c)])]
        (v/assert kb (list 'genlCx CxU 'CxUniverse) 'CxUniverse M)
        (doseq [c [CxFoo CxR]] (v/assert kb (list 'genlCx c CxU) 'CxUniverse M))
        (v/assert kb (list 'disjoint kind_a kind_b) CxU M)
        (when declared? (v/assert kb (list 'forced_monotonic_predicate kind_b) CxFoo))
        (v/assert kb (list kind_a Sp) CxU M)
        (let [b (v/assert kb (list kind_b Sp) CxU)
              d (:id (first (filter #(= (list 'defeat (list 'sentexHandle b)) (:sentence %))
                                    (v/sentexes-with-functor kb 'defeat))))]
          (is (= [true false] (ab CxR)) "before the except")
          (v/assert kb (list 'except (list 'sentexHandle d)) CxR M)
          (is (= {:u [true false] :r [true true] :foo [true declared?]}
                 {:u (ab CxU) :r (ab CxR) :foo (ab CxFoo)})
              (str "declared " declared?)))))))

(tu/deftest-kb the-roster-hides-a-handle-whose-valid-firings-are-all-void-at-its-context
  ;; (functional P) is on the baseline roster.  One rule concludes it from an antecedent no
  ;; declaration puts on the roster, which the network holds void, and one from an
  ;; antecedent CxFoo declares, which is valid in the network and void at CxU, which does
  ;; not see CxFoo.  The roster alone hides the conclusion at CxU, where it is stored.
  (tu/with-terms [CxU CxFoo kind_d kind_n parentOf]
    (let [M {:strength :monotonic}]
      (v/assert kb (list 'genlCx CxU 'CxUniverse) 'CxUniverse M)
      (v/assert kb (list 'genlCx CxFoo CxU) 'CxUniverse M)
      (v/assert kb (list 'forced_monotonic_predicate kind_d) CxFoo)
      (doseq [k [kind_n kind_d]]
        (v/assert kb (list 'set/forwardRule (list 'implies (list k '?x) (list 'functional '?x))) CxU)
        (v/assert kb (list k parentOf) CxU))
      (let [h (v/handle-of kb (list 'functional parentOf) CxU)]
        (is (= [false true] [(v/ask? kb (list 'functional parentOf) CxU)
                             (v/ask? kb (list 'functional parentOf) CxFoo)]))
        (is (true? ((exc/roster-hidden-own-fn kb) h)))))))

(defn- declaration-reach-oracle
  "Over a random 40-context DAG per seed, two roots under CxUniverse and each later
  context below one to three earlier ones: the reach of a declaration at each context
  holds the facts stated in the contexts sharing a descendant with it, by the definition
  over the DAG's own edges."
  [kb seeds]
  (doseq [seed seeds]
    (tu/with-terms [kind_r Ind]
      (let [rng     (java.util.Random. (long seed))
            cxs     (vec (repeatedly 40 #(tu/tmp-ctx "Reach")))
            parents (into {} (map-indexed
                              (fn [i c]
                                [c (if (< i 2)
                                     #{}
                                     (into #{} (repeatedly (inc (.nextInt rng 3))
                                                           #(cxs (.nextInt rng i)))))])
                              cxs))
            up      (reduce (fn [m c] (assoc m c (into #{c} (mapcat m) (parents c)))) {} cxs)
            down    (fn [c] (into #{} (filter #(contains? (up %) c)) cxs))
            M       {:strength :monotonic}
            _       (doseq [c cxs, p (or (not-empty (parents c)) ['CxUniverse])]
                      (v/assert kb (list 'genlCx c p) 'CxUniverse M))
            stated  (into {} (for [c cxs :when (.nextBoolean rng)]
                               [c (v/assert kb (list kind_r Ind) c)]))]
        (doseq [c cxs]
          (is (= (into #{} (keep (fn [[x h]] (when (some (down x) (down c)) h))) stated)
                 (set (chain/declaration-reach kb (list 'forced_monotonic_predicate kind_r) c)))
              (str "seed " seed ", declared at context " (.indexOf ^java.util.List cxs c))))))))

(tu/deftest-kb a-declarations-reach-is-the-facts-stated-where-a-context-below-it-sees
  (declaration-reach-oracle kb [0]))

(tu/deftest-kb ^:slow every-declarations-reach-is-the-facts-stated-where-a-context-below-it-sees
  (declaration-reach-oracle kb (range 6)))

;; `violations` reads the `:forced-conclusion` entries off the stored firings
;; (`checks/forced-conclusion-entries`), so these tests count entries against the store.

(defn- foo-under-u
  "CxFoo under CxU under CxUniverse, each edge `:monotonic`."
  [kb cu cfoo]
  (v/assert kb (list 'genlCx cu 'CxUniverse) 'CxUniverse {:strength :monotonic})
  (v/assert kb (list 'genlCx cfoo cu) 'CxUniverse {:strength :monotonic}))

(tu/deftest-kb a-forced-conclusion-entry-names-the-stored-spelling-while-its-firing-stands
  ;; one firing per row: the entry is read once, names the conclusion as stored, leaves
  ;; when the antecedent's retraction removes the firing, and is read once again when the
  ;; firing is derived again.  The symmetric rows conclude a spelling the store reorders.
  (doseq [row [:declared-unary :declared-symmetric :network-orthogonal :network-orthogonal-swapped]]
    (tu/with-terms [CxU CxFoo kind_s kind_t made_kind symRel amy_kind zed_kind]
      (foo-under-u kb CxU CxFoo)
      (let [[conseq c]
            (case row
              :declared-unary     [(list kind_t '?x) (list kind_t zed_kind)]
              :declared-symmetric [(list symRel '?x amy_kind) (list symRel zed_kind amy_kind)]
              :network-orthogonal [(list 'orthogonal '?x made_kind) (list 'orthogonal zed_kind made_kind)]
              :network-orthogonal-swapped [(list 'orthogonal made_kind '?x)
                                           (list 'orthogonal made_kind zed_kind)])]
        (case row
          :declared-unary (v/assert kb (list 'forced_monotonic_predicate kind_t) CxFoo)
          :declared-symmetric (do (v/assert kb (list 'symmetric symRel) 'CxUniverse {:strength :monotonic})
                                  (v/assert kb (list 'forced_monotonic_predicate symRel) CxFoo))
          nil)
        (v/assert kb (list 'set/forwardRule (list 'implies (list kind_s '?x) conseq)) CxU)
        (let [f       (v/assert kb (list kind_s zed_kind) CxU)
              stored  (:sentence (v/sentex kb (v/handle-of kb c CxU)))
              first-n (mapv :sentence (forced-entries kb CxU))
              _       (v/retract! kb f)
              gone    [(some? (v/handle-of kb c CxU)) (count (forced-entries kb CxU))]]
          (v/assert kb (list kind_s zed_kind) CxU)
          (is (= [[stored] [false 0] [stored]]
                 [first-n gone (mapv :sentence (forced-entries kb CxU))])
              (str row)))))))

(defn- entry-shape
  "The `:forced-conclusion` entries `violations` reads in `context`, as `[sentence context
  off-roster]`, with each value of `names` replaced by its key."
  [kb names context]
  (walk/postwalk-replace (zipmap (vals names) (keys names))
                         (mapv (juxt :sentence :context (comp :off-roster :detail))
                               (forced-entries kb context))))

(tu/deftest-kb the-forced-conclusion-entries-are-the-same-in-every-arrival-order
  ;; a network-void firing (orthogonal, on the global roster) and a reader-only void
  ;; firing (kind_t, declared at CxFoo); a second trigger arrives and is retracted last
  (let [shapes (doall
                (for [order (orders [:decl :rule :fact :gone])]
                  (tu/with-terms [CxU CxFoo kind_s kind_t made_kind spa_kind spb_kind]
                    (foo-under-u kb CxU CxFoo)
                    (v/assert kb (definitional-rule kind_s made_kind) CxU)
                    (let [writes {:decl [(list 'forced_monotonic_predicate kind_t) CxFoo]
                                  :rule [(list 'set/forwardRule
                                               (list 'implies (list kind_s '?x) (list kind_t '?x)))
                                         CxU]
                                  :fact [(list kind_s spa_kind) CxU]
                                  :gone [(list kind_s spb_kind) CxU]}]
                      (doseq [k order] (apply v/assert kb (writes k)))
                      (v/retract! kb (apply v/handle-of kb (writes :gone)))
                      (entry-shape kb {'U CxU 'S kind_s 'T kind_t 'M made_kind 'A spa_kind 'B spb_kind} CxU)))))]
    (is (= 1 (count (distinct shapes))) (pr-str (distinct shapes)))
    (is (= #{'[(T A) U [S]] '[(orthogonal M A) U [S]]} (set (first shapes))))))

(tu/deftest-kb the-forced-conclusion-entries-survive-recover-and-clear-violations
  (tu/with-terms [CxU CxFoo kind_s kind_t made_kind spa_kind spb_kind]
    (foo-under-u kb CxU CxFoo)
    (v/assert kb (definitional-rule kind_s made_kind) CxU)
    (v/assert kb (list 'forced_monotonic_predicate kind_t) CxFoo)
    (v/assert kb (list 'set/forwardRule (list 'implies (list kind_s '?x) (list kind_t '?x))) CxU)
    (doseq [sp [spa_kind spb_kind]] (v/assert kb (list kind_s sp) CxU))
    (let [live (forced-entries kb CxU)]
      (v/clear-violations! kb)
      (let [cleared (forced-entries kb CxU)]
        (v/recover kb)
        (is (= 4 (count live)))
        (is (= [live live] [cleared (forced-entries kb CxU)]))))))

(tu/deftest-kb a-firing-void-at-some-reader-reads-one-entry-and-logs-once-while-the-roster-moves
  ;; a roster rule's exceptWhen arriving and leaving, and the declaration leaving and
  ;; arriving again, read the firing again: `violations` reads one entry for it each
  ;; time, and the firing logs once, as its justification is added
  (tu/with-terms [CxU CxFoo kind_t kind_s Sp]
    (let [rule (list 'set/forwardRule (list 'implies (list kind_s '?x) (list kind_t '?x)))
          decl (list 'forced_monotonic_predicate kind_t)
          n    #(count (forced-entries kb (list kind_t Sp) CxU))
          logs (atom 0)]
      (foo-under-u kb CxU CxFoo)
      (v/assert kb decl CxFoo)
      (v/assert kb rule CxU)
      (binding [trove/*log-fn* (fn [_ _ _ id _]
                                 (when (= :vaelii.impl.violations/dropped-conclusion id)
                                   (swap! logs inc)))]
        (v/assert kb (list kind_s Sp) CxU)
        (let [x      (v/assert kb (list 'exceptWhen (list 'orthogonal '?x 'zz_none) rule) CxU)
              during (n)
              _      (v/retract! kb x)
              after  (n)]
          (v/retract! kb (v/handle-of kb decl CxFoo))
          (v/assert kb decl CxFoo)
          (is (= [1 1 1 1] [during after (n) @logs])))))))

(tu/deftest-kb the-entries-of-the-firings-a-declaration-convicts-follow-the-declaration
  ;; three firings stand before the declaration; its arrival reads three entries, its
  ;; leaving none, and its arriving again three
  (tu/with-terms [CxU CxFoo kind_t kind_s SpA SpB SpC]
    (let [decl (list 'forced_monotonic_predicate kind_t)
          n    #(count (forced-entries kb CxU))]
      (foo-under-u kb CxU CxFoo)
      (v/assert kb (list 'set/forwardRule (list 'implies (list kind_s '?x) (list kind_t '?x))) CxU)
      (doseq [sp [SpA SpB SpC]] (v/assert kb (list kind_s sp) CxU))
      (let [d     (v/assert kb decl CxFoo)
            filed (n)
            _     (v/retract! kb d)
            left  (n)]
        (v/assert kb decl CxFoo)
        (is (= [3 0 3] [filed left (n)]))))))

(tu/deftest-kb a-declared-firing-is-listed-only-where-a-context-sees-the-declaration-and-the-conclusion
  ;; the declaration at CxBar, the rule and its firing at CxU, both under CxUniverse.  No
  ;; context sees both until CxJ sits under the two, and CxJ reads the firing void
  (doseq [joined? [false true]]
    (tu/with-terms [CxU CxBar CxJ kind_t kind_s Zed]
      (let [c (list kind_t Zed)]
        (doseq [x [CxU CxBar]]
          (v/assert kb (list 'genlCx x 'CxUniverse) 'CxUniverse {:strength :monotonic})
          (when joined? (v/assert kb (list 'genlCx CxJ x) 'CxUniverse {:strength :monotonic})))
        (v/assert kb (list 'forced_monotonic_predicate kind_t) CxBar)
        (v/assert kb (list 'set/forwardRule (list 'implies (list kind_s '?x) c)) CxU)
        (v/assert kb (list kind_s Zed) CxU)
        (is (= (if joined? [1 true false] [0 true nil])
               [(count (forced-entries kb c CxU)) (v/ask? kb c CxU) (when joined? (v/ask? kb c CxJ))])
            (str "joined? " joined?))))))

(defn- defeated-declaration-reading
  "CxDen and CxB under CxU, the writes in each order `pick` keeps.  A :monotonic denial
  of the declaration at CxDen defeats it there, so CxDen believes the :monotonic denial
  of the trigger fact and the fact loses.  CxB sees the declaration believed: the denial
  is inert and the fact stands."
  [kb pick]
  (doseq [decl-cx [:at :core]
          order   (pick (orders [:decl :deny-decl :deny-fact :fact]))]
    (tu/with-terms [CxU CxDen CxB kind_t Sp]
      (let [decl (list 'forced_monotonic_predicate kind_t)
            t    (list kind_t Sp)]
        (is (= {:den [false false true] :b [true true false]}
               (roster-reading kb {:den CxDen :b CxB}
                               {:fixed  (scoped-contexts CxU CxDen CxB)
                                :writes {:decl      [decl (if (= :core decl-cx) 'CxUniverse CxU)]
                                         :deny-decl [(list 'not decl) CxDen :monotonic]
                                         :deny-fact [(list 'not t) CxU :monotonic]
                                         :fact      [t CxU]}
                                :order  order
                                :asked  [decl t (list 'not t)]}))
            (str "declared " decl-cx ", order " (vec order)))))))

(tu/deftest-kb a-defeated-declaration-makes-no-denial-inert-where-the-defeat-is-seen
  (defeated-declaration-reading kb sampled))

(tu/deftest-kb ^:slow a-defeated-declaration-makes-no-denial-inert-where-the-defeat-is-seen-in-every-order
  (defeated-declaration-reading kb identity))

(tu/deftest-kb an-excepted-defeat-of-a-declaration-leaves-it-forcing-where-the-except-is-seen
  ;; CxR under CxU.  A :monotonic denial of the declaration at CxU places a defeat D on it,
  ;; so CxU reads the dilemma.  CxR excepts D, believes the declaration and forces the
  ;; trigger: the rival loses there, whichever order the four writes arrive in.
  (doseq [order (orders [:decl :deny :trigger :rival])]
    (tu/with-terms [CxU CxR trigger_kind rival_kind species_kind]
      (let [decl   (list 'forced_monotonic_predicate trigger_kind)
            writes {:decl    [decl CxU]
                    :deny    [(list 'not decl) CxU :monotonic]
                    :trigger [(list trigger_kind species_kind) CxU]
                    :rival   [(list rival_kind species_kind) CxU]}
            asked  [decl (list trigger_kind species_kind) (list rival_kind species_kind)]
            read   (fn [c] (mapv #(v/ask? kb % c) asked))]
        (doseq [[s c st] [[(list 'genlCx CxU 'CxUniverse) 'CxUniverse :monotonic]
                          [(list 'genlCx CxR CxU) 'CxUniverse :monotonic]
                          [(list 'disjoint trigger_kind rival_kind) CxU :monotonic]]]
          (v/assert kb s c {:strength (or st :default)}))
        (doseq [[s c st] (map writes order)] (v/assert kb s c {:strength (or st :default)}))
        (let [d (:id (first (filter #(= (list 'defeat (list 'sentexHandle (v/handle-of kb decl CxU)))
                                        (:sentence %))
                                    (v/sentexes-with-functor kb 'defeat))))]
          (is (= {:u [false true true] :r [false true true]} {:u (read CxU) :r (read CxR)})
              (str "before the except, order " (vec order)))
          (v/assert kb (list 'except (list 'sentexHandle d)) CxR {:strength :monotonic})
          (is (= {:u [false true true] :r [true true false]} {:u (read CxU) :r (read CxR)})
              (str "order " (vec order))))))))

(tu/deftest-kb why-not-names-the-conviction-at-a-reader-that-misses-the-declaration
  (tu/with-terms [CxU CxA CxB trigger_kind made_kind species_kind]
    (doseq [[s c st] (scoped-contexts CxU CxA CxB)] (v/assert kb s c {:strength st}))
    (v/assert kb (list 'forced_monotonic_predicate trigger_kind) CxA)
    (let [r (v/assert kb (definitional-rule trigger_kind made_kind) CxU)
          c (list 'orthogonal species_kind made_kind)]
      (v/assert kb (list trigger_kind species_kind) CxU)
      (is (v/ask? kb c CxA))
      (let [w (v/why-not kb c CxB)]
        (is (= :forced-conclusion (:reason w)))
        (is (= [[r [trigger_kind]]] (mapv (juxt :informant :off-roster) (:convicted w))))))))

(tu/deftest-kb an-exception-on-a-roster-rule-makes-its-firings-inert-in-either-order
  ;; a context per order, so the rule and its exception are two sentexes per order
  (doseq [exception-first? [true false]]
    (tu/with-terms [CxHere odd_kind parentOf]
      (let [rule (list 'set/forwardRule
                       (list 'implies (list 'anti_transitive '?p) (list 'irreflexive '?p)))
            exc  #(v/assert kb (list 'exceptWhen (list odd_kind '?p) rule) CxHere)]
        (v/assert kb (list 'genlCx CxHere 'CxUniverse) 'CxUniverse)
        (when exception-first? (exc))
        (v/assert kb rule CxHere)
        (v/assert kb (list 'anti_transitive parentOf) CxHere)
        (when-not exception-first? (exc))
        (is (= [false true] (concluded? kb (list 'irreflexive parentOf) CxHere))
            (str "exception first: " exception-first?))))))

(tu/deftest-kb a-denied-except-still-hides
  ;; `except` is on the forced-monotonic roster: an except keeps the strength it was
  ;; written at and is never a loser, and a denial of one is held OUT, so it keeps hiding
  ;; (docs/nmtms.md, "The forced-monotonic roster").
  (let [ctx (tu/tmp-ctx "Sub") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) ctx {:strength :monotonic})
          x (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :default})]
      (is (= :default (v/defeat-class kb x)))
      (is (not (v/ask? kb (list shiny gold) ctx)) "the except hides it")
      (let [d (v/assert kb (list 'not (list 'except (sx/sentex-handle h))) ctx
                        {:strength :monotonic})]
        (is (not (v/in? kb d)) "the denial is held OUT")
        (is (not (v/ask? kb (list shiny gold) ctx)) "and the target stays hidden")))))

(deftest the-verdict-weighs-only-the-members-off-the-roster
  ;; handles 1 and 2 are roster literals: whatever their class, neither is a loser, and a
  ;; nogood with no defeasible member off the roster is `:hard`
  (let [class-of {1 :default 2 :default 3 :default 4 :default 5 :monotonic}
        roster?  #{1 2}]
    (is (= :hard (decide/verdict class-of roster? #{1 2})))
    (is (= :hard (decide/verdict class-of roster? #{1 5})))
    (is (= {:defeat 3} (decide/verdict class-of roster? #{1 3})))
    (is (= :dilemma (decide/verdict class-of roster? #{1 3 4})))))

(deftest a-roster-member-is-never-a-loser-whatever-its-strength
  ;; decide/verdict weighs only the members off the roster: two arity-class memberships
  ;; separated by a `:default` `disjoint` form a `:hard` clash and both stay believed, in
  ;; either order and at either strength.  A bare KB, so no upper-layer declaration of the
  ;; separation is re-asserted at `:monotonic`.
  (doseq [membership-strength [:monotonic :default] disjoint-first? [true false]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (let [p    (predicate-spelled "RosterRel")
            decl #(v/assert kb '(disjoint unary binary) 'CxUniverse {:strength :default})
            why  (str membership-strength " memberships, disjoint first: " disjoint-first?)]
        (v/assert kb '(genl unary_predicate unary) 'CxUniverse {:strength :monotonic})
        (v/assert kb '(genl binary_predicate binary) 'CxUniverse {:strength :monotonic})
        (when disjoint-first? (decl))
        (let [ms (mapv #(v/assert kb (list % p) 'CxUniverse {:strength membership-strength})
                       '[unary_predicate binary_predicate])]
          (when-not disjoint-first? (decl))
          (is (every? #(v/ask? kb (:sentence (v/sentex kb %)) 'CxUniverse) ms) why)
          (is (some #(= (set ms) (set (:nogood %))) (v/conflicts kb)) why))))))

(defn- own-ground?
  "Is `literal` among `grounds`, a family's `:grounds` map, read as `decide/roster-literal?`
  reads the roster."
  [grounds literal]
  (let [[f & args] literal]
    (boolean (or (contains? (:forced-monotonic grounds) f)
                 (and (contains? (:forced-between-predicates grounds) f)
                      (every? #(re-matches #"[a-z][a-zA-Z0-9]*[A-Z][a-zA-Z0-9]*" (name %)) args))))))

(deftest a-family-names-its-own-ground-as-a-member-only-beside-other-grounds
  ;; A family reads its `:grounds` as stored marks.  The one nogood that names them as
  ;; members is the arity family's `:arity-descension`, two bindings and nothing else,
  ;; which `decide/verdict` reads `:hard`.  Every family with grounds places its nogoods,
  ;; so each is read off the placed `contradicts`; the arity family places only its pairs,
  ;; and the ternary shortRel tuple is inert.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [Ann Bob Cal dog_kind cat_kind Rex]
      (let [[shortRel longRel irrRel antiRel ageRel beatsRel nextRel]
            (mapv predicate-spelled ["Short" "Long" "Irr" "Anti" "Age" "Beats" "Next"])
            U 'CxUniverse]
        (doseq [s [(list 'binary_predicate shortRel) (list shortRel Ann Bob Cal)
                   (list 'ternary_predicate longRel) (list 'genl longRel shortRel)
                   (list 'irreflexive irrRel) (list irrRel Ann Ann)
                   (list 'anti_symmetric antiRel) (list antiRel Ann Bob) (list antiRel Bob Ann)
                   (list 'functional ageRel) (list ageRel Ann 1) (list ageRel Ann 2)
                   (list 'asymmetric beatsRel) (list beatsRel Ann Bob) (list beatsRel Bob Ann)
                   (list 'anti_transitive nextRel) (list nextRel Ann Bob) (list nextRel Bob Cal)
                   (list nextRel Ann Cal)
                   (list 'disjoint dog_kind cat_kind) (list dog_kind Rex) (list cat_kind Rex)]]
          (v/assert kb s U))
        (let [sen     #(:sentence (v/sentex kb %))
              grounds (keep :grounds decide/registry)
              placed  (for [c (v/sentexes-with-functor kb 'contradicts)
                            :let [ms (into #{} (map v/handle-id) (rest (:sentence c)))]]
                        [ms (decide/placed-kind kb ms)])]
          (is (= #{:arity-descension :irreflexive :anti-symmetric :functional :asymmetric
                   :anti-transitive :disjoint}
                 (into #{} (map second) placed))
              "every family with grounds places a nogood here")
          (is (= #{(list cat_kind Rex) (list dog_kind Rex)}
                 (into #{} (comp (filter #(= :disjoint (second %))) (mapcat first) (map sen)) placed))
              "the placed membership nogood names the memberships and not the declaration")
          (doseq [[ms kind] placed
                  :let [own (filterv (fn [h] (some #(own-ground? % (sen h)) grounds)) ms)]
                  :when (seq own)]
            (is (and (= :arity-descension kind) (= (count own) (count ms)))
                (pr-str kind (mapv sen ms)))))))))

(tu/deftest-kb an-except-hides-the-derivation-it-blocks-in-either-order-beside-its-denial
  ;; A denial held OUT moves no belief, so the except and its denial end in one state
  ;; whichever arrives first: the conclusion resting on the hidden fact is swept.
  (let [ctx (tu/tmp-ctx "Sub") qq (tu/tmp-pred) pp (tu/tmp-pred)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies (list qq '?x) (list pp '?x)) ctx {:direction :forward})
    (doseq [denial-first? [false true]]
      (tu/with-terms [Aa]
        (let [h     (v/assert kb (list qq Aa) ctx {:strength :monotonic})
              deny! #(v/assert kb (list 'not (list 'except (sx/sentex-handle h))) ctx
                               {:strength :monotonic})]
          (is (seq (v/sentexes-matching kb (list pp Aa) ctx)) "the rule fired")
          (when denial-first? (deny!))
          (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :default})
          (when-not denial-first? (deny!))
          (is (empty? (v/sentexes-matching kb (list pp Aa) ctx))
              (str "the except sweeps the conclusion, denial first: " denial-first?)))))))

(defn- roster-history
  "Assert into CxUniverse a fact and a denial of `likes`, a non-roster rule concluding
  `likes` from `knows`, and the fact that fires it, with a `(forced_monotonic_predicate
  likes)` declaration arriving before the write at index `at` and retracted after the
  last one (no declaration when `at` is nil).  Answers, for the fact, the denial and the
  rule's conclusion, `[believed? defeat-class justification-count]`."
  [kb likes knows Ann Bob Cal Dan at]
  (let [decl   (list 'forced_monotonic_predicate likes)
        writes [#(v/assert kb (list likes Ann Bob) 'CxUniverse)
                #(v/assert kb (list 'not (list likes Ann Cal)) 'CxUniverse)
                #(v/assert kb (list 'set/forwardRule (list 'implies (list knows '?x '?y)
                                                           (list likes '?x '?y)))
                           'CxUniverse)
                #(v/assert kb (list knows Ann Dan) 'CxUniverse)]]
    (doseq [[i w] (map-indexed vector writes)]
      (when (= i at) (v/assert kb decl 'CxUniverse))
      (w))
    (when at (v/retract! kb (v/handle-of kb decl 'CxUniverse)))
    (mapv (fn [s] (let [h (v/handle-of kb s 'CxUniverse)]
                    [(boolean (and h (v/in? kb h))) (when h (v/defeat-class kb h))
                     (if h (count (v/supporting-justifications kb h)) 0)]))
          [(list likes Ann Bob) (list 'not (list likes Ann Cal)) (list likes Ann Dan)])))

(tu/deftest-kb retracting-a-declaration-leaves-the-belief-a-kb-that-never-had-it-holds
  (let [never (tu/with-terms [likes knows Ann Bob Cal Dan]
                (roster-history kb likes knows Ann Bob Cal Dan nil))]
    (is (= [[true :default 0] [true :default 0] [true :default 1]] never))
    (doseq [at (range 4)]
      (tu/with-terms [likes knows Ann Bob Cal Dan]
        (is (= never (roster-history kb likes knows Ann Bob Cal Dan at))
            (str "declared before write " at))))))

;; ---- the declaration is a switch: an oracle over random histories -------------------

(defn- shuffle-with
  "`xs` in an order drawn from `rng`."
  [^java.util.Random rng xs]
  (let [l (java.util.ArrayList. ^java.util.Collection (vec xs))]
    (java.util.Collections/shuffle l rng)
    (vec l)))

(defn- roster-world
  "A random history over abstract terms, from `seed`: writes of two predicates `:p` and
  `:q` and a non-roster `:k` over four individuals in two contexts, a rule concluding
  `:p` from `:k` and one concluding `:q` from `:p` (a roster rule while both are
  declared), and `forced_monotonic_predicate` declarations of `:p` and `:q` arriving at
  random points, half of them retracted later.  Answers `{:history [[op form ctx
  strength] …] :final [[form ctx strength] …]}`: `:final` is the content the history
  ends with, in an order of its own."
  [seed]
  (let [rng   (java.util.Random. seed)
        pick  #(nth % (.nextInt rng (count %)))
        inds  [:a :b :c :d]
        write (fn []
                (case (.nextInt rng 5)
                  (0 1) [(list (pick [:p :q]) (pick inds) (pick inds)) (pick [:cx-top :cx-low])]
                  2     [(list 'not (list (pick [:p :q]) (pick inds) (pick inds)))
                         (pick [:cx-top :cx-low])]
                  (3 4) [(list :k (pick inds) (pick inds)) (pick [:cx-top :cx-low])]))
        rules [[(list 'set/forwardRule (list 'implies (list :k '?x '?y) (list :p '?x '?y))) :cx-top]
               [(list 'set/forwardRule (list 'implies (list :p '?x '?y) (list :q '?x '?y))) :cx-top]]
        ws    (mapv #(conj % (pick [:default :default :monotonic]))
                    (shuffle-with rng (into rules (distinct) (repeatedly (+ 4 (.nextInt rng 6)) write))))
        decls (for [f [:p :q] :when (pos? (.nextInt rng 3))]
                [(list 'forced_monotonic_predicate f) :cx-top :default])
        hist  (reduce (fn [h d]
                        (let [at (.nextInt rng (inc (count h)))
                              h  (-> (subvec h 0 at) (conj (into [:assert] d)) (into (subvec h at)))]
                          (if (zero? (.nextInt rng 2))
                            (let [later (+ at 1 (.nextInt rng (- (count h) at)))]
                              (-> (subvec h 0 later) (conj (into [:retract] d)) (into (subvec h later))))
                            h)))
                      (mapv #(into [:assert] %) ws)
                      decls)
        gone  (into #{} (comp (filter #(= :retract (first %))) (map #(subvec % 1))) hist)]
    {:history hist
     :final   (shuffle-with rng (into [] (comp (filter #(= :assert (first %))) (map #(subvec % 1))
                                               (remove gone))
                                      hist))}))

(defn- run-world
  "Run `steps` (`[op form ctx strength]`) over fresh temporaries, `:cx-low` below
  `:cx-top`, and answer `[believed? defeat-class]` for every literal of the three
  predicates and its denial at both contexts, keyed by the abstract terms."
  [kb steps]
  (tu/with-terms [likes trusts knows Ann Bob Cal Dan CxTop CxLow]
    (let [terms {:p likes :q trusts :k knows :a Ann :b Bob :c Cal :d Dan
                 :cx-top CxTop :cx-low CxLow}
          inst  #(walk/postwalk (fn [x] (get terms x x)) %)]
      (v/assert kb (list 'genlCx CxLow CxTop) 'CxUniverse)
      (doseq [[op form ctx strength] steps]
        (case op
          :assert  (v/assert kb (inst form) (terms ctx) {:strength strength})
          :retract (v/retract! kb (v/handle-of kb (inst form) (terms ctx)))))
      (into {} (for [f [:p :q :k] a [:a :b :c :d] b [:a :b :c :d] neg? [false true]
                     c [:cx-top :cx-low]
                     :let [s (inst (cond->> (list f a b) neg? (list 'not)))
                           h (v/handle-of kb s (terms c))]]
                 [[f a b neg? c] [(v/ask? kb s (terms c)) (when h (v/defeat-class kb h))]])))))

(defn- declaration-oracle
  "The oracle for the switch over the worlds of `seeds`: declarations arriving and
  leaving at random points give the beliefs and classes the final content gives when
  asserted fresh, in another order (docs/nmtms.md, \"The forced-monotonic roster\")."
  [kb seeds]
  (doseq [seed seeds]
    (let [{:keys [history final]} (roster-world seed)]
      (is (= (run-world kb (mapv #(into [:assert] %) final)) (run-world kb history))
          (str "seed " seed)))))

(tu/deftest-kb a-declaration-history-believes-what-its-final-content-believes
  ;; the sampled twin of the sweep below: seed 1 declares both predicates and retracts one
  (declaration-oracle kb [1]))

(tu/deftest-kb ^:slow every-declaration-history-believes-what-its-final-content-believes
  (declaration-oracle kb (range 60)))

(defn- switches
  "How many times `checks/force-reach!` runs while `f` runs."
  [f]
  (let [n (atom 0) orig checks/force-reach!]
    (with-redefs [checks/force-reach! (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(deftest a-declaration-of-a-baseline-member-runs-no-switch
  ;; a bare KB: the engine's baseline already holds `sameAs`, so its declaration moves no
  ;; membership, while `likes` joins and leaves the roster by its declaration, which a
  ;; stored denial of each reads: held OUT while its literal is on the roster
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [likes Ann Bob Cal Dan]
      (let [same  (v/assert kb (list 'not (list 'sameAs Ann Bob)) 'CxUniverse)
            fact  (v/assert kb (list 'not (list likes Cal Dan)) 'CxUniverse)
            decl  (list 'forced_monotonic_predicate likes)
            in    #(mapv (partial v/in? kb) [same fact])]
        (is (= [false true] (in)))
        (is (= 0 (switches #(v/assert kb '(forced_monotonic_predicate sameAs) 'CxUniverse))))
        (is (= 1 (switches #(v/assert kb decl 'CxUniverse))))
        (is (= [false false] (in)))
        (is (= 1 (switches #(v/retract! kb (v/handle-of kb decl 'CxUniverse)))))
        (is (= [false true] (in)))))))

(tu/deftest-kb an-uncleared-declaration-is-not-retracted
  (testing "genlCx is always forced: its declaration stays"
    (let [h (v/handle-of kb '(forced_monotonic_predicate genlCx) 'CxUniverse)
          e (try (v/retract! kb h) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= [:uncleared-forcing 'genlCx :unforced-context-edge]
             ((juxt :type :predicate :missing) e)))
      (is (v/in? kb h))))
  (testing "a declaration whose predicate has no unforced semantics stays"
    (doseq [[s missing] [['(forced_monotonic_predicate disjoint) :unforced-definitional-declaration]
                         ['(forced_monotonic_predicate sameAs) :unforced-equality]
                         ['(forced_monotonic_predicate except) :unforced-except]
                         ['(forced_monotonic_between_predicates genl) :unforced-predicate-genl]]]
      (let [h (v/handle-of kb s 'CxUniverse)]
        (is (= [:uncleared-forcing missing]
               ((juxt :type :missing)
                (try (v/retract! kb h) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))))
            (pr-str s))
        (is (v/in? kb h) (pr-str s)))))
  (testing "injection, surjection, bijection and an author's own predicate are cleared"
    (tu/with-terms [likes]
      (doseq [p ['injection 'surjection 'bijection likes]]
        (is (not (contains? checks/uncleared-forcing ['forced_monotonic_predicate p]))
            (str p))))))

;; ---- decontextualized_predicate: a fact that belongs to the KB, not to one theory --
;;
;; `(decontextualized_predicate P)` deduces every `(P ...)` into CxUniverse, which
;; every context sees.  CxUniverse and not a named target: the definitional
;; checks are context-scoped and run where the fact is stated, so a target the stating
;; context cannot see is a place those checks never look — two facts, each admissible
;; where it was stated, could meet there as a disjointness violation nothing reports.

(tu/deftest-kb a-decontextualized-fact-reaches-the-universe
  ;; Declaration first, then the fact — the forward path, where the lift runs as the
  ;; fact is stored (the retroactive half is the next test).  The demonstration builds
  ;; its own predicate: the shipped ontology declares the *metadata* marks and
  ;; genlCx and nothing else, every one of them a claim about a predicate rather
  ;; than about a world, so there is no shipped fact to lift.
  (tu/with-terms [rulesOver ridesWith Ann Bob CxAlpha CxBeta]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBeta 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate rulesOver) 'CxUniverse)
    (v/assert kb (list rulesOver Ann Bob) CxAlpha)
    (v/assert kb (list ridesWith Ann Bob) CxAlpha)

    (testing "the fact is copied into CxUniverse"
      (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse))))
    (testing "visible from a sibling context (via CxUniverse), unlike an undeclared one"
      (is (v/ask? kb (list rulesOver Ann Bob) CxBeta))
      (is (not (v/ask? kb (list ridesWith Ann Bob) CxBeta))))
    (testing "the copy is justified by the placement sentex and the declaration"
      (let [u (v/handle-of kb (list rulesOver Ann Bob) 'CxUniverse)
            d (first (v/supporting-justifications kb u))]
        (is (= 'decontextualized_predicate (:informant d)))
        (is (= 2 (count (:antecedents d))))
        (is (some #(= (list 'decontextualized_predicate rulesOver) (:sentence (v/sentex kb %)))
                  (:antecedents d)))))
    (testing "and the declaration reads back as predicate metadata"
      (is (v/has-prop? kb :decontextualized rulesOver))
      (is (not (v/has-prop? kb :decontextualized ridesWith)))
      (is (contains? (v/props kb :decontextualized) rulesOver)))))

(tu/deftest-kb the-shipped-ontology-decontextualizes-predicate-metadata-and-nothing-else
  ;; What carries the mark is a claim about a *predicate* — its algebra — plus
  ;; genlCx by force.  A domain relation carrying it would make one theory's fact
  ;; a claim of the whole KB, and would take a rule's conclusions out with it: a
  ;; decontextualized marriage lifts (knows ?x ?y) through CxSocial's rule into a
  ;; context every data context sees, decontextualizing a predicate nothing declared.
  (testing "the roster is the algebraic marks, the inverse declaration, the length bindings, and genlCx"
    ;; The three commutativity marks are here for `symmetric`'s reason and one of its
    ;; own: they are predicate algebra, and `res/kb-sentex` reads them **globally** —
    ;; a sentex has one key, so whether a predicate sorts its arguments cannot vary by
    ;; reader.  A context-scoped declaration behind a global read would be a mark
    ;; visible from one context and acted on from every one.
    ;; `functionalInArg` is `functional` read at another position, and lifted with it.
    ;; The length bindings are lifted so a relation's length reads the same everywhere.
    (is (= (into '#{functional functionalInArg inverse reflexive symmetric asymmetric transitive
                    irreflexive anti_symmetric anti_transitive equivalence_relation
                    injection surjection bijection
                    commutative commutativeInArgs commutativeInArgAndRest}
                 sx/arity-binding-functors)
           (v/props kb :decontextualized)))
    (is (= '#{genlCx} (v/props kb :forced-decontextualized))))
  (testing "so a social fact stays in the theory that states it"
    (is (not (v/has-prop? kb :decontextualized 'marriedTo)))
    (is (empty? (v/sentexes-matching kb '(marriedTo Bob Nancy) 'CxUniverse)))
    (is (not (v/ask? kb '(marriedTo Bob Nancy) 'CxNaturalWorld)))
    (is (not (v/ask? kb '(owns Tom Car1) 'CxNaturalWorld))))
  (testing "and the knows-fact its rule concludes stays there with it"
    (is (v/ask? kb '(knows Bob Nancy) 'CxSocialWorld))
    (is (not (v/ask? kb '(knows Bob Nancy) 'CxNaturalWorld)))))

(tu/deftest-kb declaring-it-lifts-facts-already-asserted
  ;; The retroactive sweep, the half a declaration-then-facts test never exercises: a
  ;; broken one looks like it works for everything asserted afterwards.
  (tu/with-terms [rulesOver Ann Bob Cid Dee CxAlpha]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list rulesOver Ann Bob) CxAlpha)
    (testing "before the declaration the fact is confined to its own context"
      (is (empty? (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse))))

    (v/assert kb (list 'decontextualized_predicate rulesOver) 'CxUniverse)
    (testing "declaring it lifts the fact that was already there"
      (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse))))
    (testing "and facts asserted afterwards are lifted too"
      (v/assert kb (list rulesOver Cid Dee) CxAlpha)
      (is (seq (v/sentexes-matching kb (list rulesOver Cid Dee) 'CxUniverse))))))

(tu/deftest-kb retracting-the-declaration-withdraws-the-lifted-copies
  (tu/with-terms [rulesOver Ann Bob CxAlpha]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (let [dh (v/assert kb (list 'decontextualized_predicate rulesOver) 'CxUniverse)]
      (v/assert kb (list rulesOver Ann Bob) CxAlpha)
      (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse)))

      (v/retract! kb dh)
      (testing "the copy goes with the declaration that licensed it"
        (is (empty? (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse))))
      (testing "and the metadata follows"
        (is (not (v/has-prop? kb :decontextualized rulesOver))))
      (testing "the fact itself is untouched — only the copy rested on the declaration"
        (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) CxAlpha)))))))

;; ---- the lift reaches derived content, in any order ---------------------
;;
;; A decontextualized predicate is a claim about the *predicate*, so what a rule
;; concludes is lifted exactly as what a caller asserts.  Lifting only asserted content
;; made belief depend on arrival order — declare-then-derive left the conclusion where
;; it was concluded, while derive-then-declare lifted it through the retroactive sweep —
;; and the two are the same knowledge.

(tu/deftest-kb a-derived-conclusion-is-lifted-like-an-asserted-fact
  (tu/with-terms [bornInFrance speaksFrench Ann CxAlpha]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate speaksFrench) 'CxUniverse)
    (v/assert-rule kb [(list bornInFrance '?x)] (list speaksFrench '?x) CxAlpha {:direction :forward})
    (v/assert kb (list bornInFrance Ann) CxAlpha)

    (testing "the rule concludes in its own context"
      (is (seq (v/sentexes-matching kb (list speaksFrench Ann) CxAlpha))))
    (testing "and the conclusion is lifted, exactly as an asserted fact would be"
      (is (seq (v/sentexes-matching kb (list speaksFrench Ann) 'CxUniverse))))
    (testing "the copy names the declaration that licensed it, so `why` points at what to retract"
      (let [u (v/handle-of kb (list speaksFrench Ann) 'CxUniverse)
            d (first (v/supporting-justifications kb u))]
        (is (= 'decontextualized_predicate (:informant d)))
        (is (some #(= (list 'decontextualized_predicate speaksFrench)
                      (:sentence (v/sentex kb %)))
                  (:antecedents d)))))
    (testing "retracting the fact takes the conclusion and its copy with it"
      (v/retract! kb (v/handle-of kb (list bornInFrance Ann) CxAlpha))
      (is (empty? (v/sentexes-matching kb (list speaksFrench Ann) CxAlpha)))
      (is (empty? (v/sentexes-matching kb (list speaksFrench Ann) 'CxUniverse))))))

(tu/deftest-kb the-lift-is-independent-of-the-order-its-parts-arrive
  ;; Declaration, rule and fact in all six orders: same beliefs, or the engine's
  ;; order-independence invariant is broken by the lift.
  (let [outcomes (mapv (fn [order]
                         (tu/with-terms [bornInFrance speaksFrench Ann CxAlpha]
                           (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
                           (doseq [step order]
                             (case step
                               :decl (v/assert kb (list 'decontextualized_predicate speaksFrench)
                                               'CxUniverse)
                               :rule (v/assert-rule kb [(list bornInFrance '?x)] (list speaksFrench '?x) CxAlpha {:direction :forward})
                               :fact (v/assert kb (list bornInFrance Ann) CxAlpha)))
                           [(boolean (seq (v/sentexes-matching kb (list speaksFrench Ann) CxAlpha)))
                            (boolean (seq (v/sentexes-matching kb (list speaksFrench Ann) 'CxUniverse)))]))
                       [[:decl :rule :fact] [:decl :fact :rule]
                        [:rule :decl :fact] [:rule :fact :decl]
                        [:fact :decl :rule] [:fact :rule :decl]])]
    (is (= [[true true]] (distinct outcomes))
        "every order concludes in the rule's context and lifts into CxUniverse")))

(tu/deftest-kb a-rule-over-a-lifted-predicate-reaches-a-fixpoint
  ;; The copy is a new datum in a context the rule can see, so it goes back on the
  ;; agenda and the rule fires on it.  Justification dedup is what stops that being a
  ;; loop: re-deriving a sentence already stored adds no handle, so the agenda drains.
  (tu/with-terms [connects A B C D CxAlpha]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate connects) 'CxUniverse)
    (v/assert-rule kb [(list connects '?x '?y) (list connects '?y '?z)]
                   (list connects '?x '?z) CxAlpha {:direction :forward})
    (v/assert kb (list connects A B) CxAlpha)
    (v/assert kb (list connects B C) CxAlpha)
    (v/assert kb (list connects C D) CxAlpha)
    (testing "the transitive closure of a 3-edge path is 6 edges, derived once"
      (is (= 6 (count (v/sentexes-matching kb (list connects '?x '?y) CxAlpha))))
      (is (= 6 (count (v/sentexes-matching kb (list connects '?x '?y) 'CxUniverse)))))
    (testing "and the run completed rather than hitting the depth guard"
      (is (not (:truncated? (:last (v/chain-stats kb))))))))

(tu/deftest-kb an-exception-in-the-universe-sees-the-lifted-copy
  ;; The copy goes through the derivation-path choke point, so its arrival is a
  ;; re-check trigger like any other fact's.  Without that the exception would never be
  ;; re-evaluated and the conclusion it should block would stand.
  (tu/with-terms [bird flies penguin Opus CxAlpha]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate penguin) 'CxUniverse)
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list 'and (list bird '?x)) (list flies '?x)))))
              'CxUniverse)
    (v/assert kb (list bird Opus) 'CxUniverse)
    (is (v/ask? kb (list flies Opus) 'CxUniverse) "nothing excepts it yet")

    ;; the penguin fact is stated in a context the rule cannot see; only the lift
    ;; brings it into range
    (v/assert kb (list penguin Opus) CxAlpha)
    (is (seq (v/sentexes-matching kb (list penguin Opus) 'CxUniverse)) "lifted into the rule's context")
    (is (not (v/ask? kb (list flies Opus) 'CxUniverse))
        "the arriving copy re-triggered the exception, which now blocks")))

(tu/deftest-kb two-declarations-are-two-witnesses-for-one-copy
  ;; The declaration is not forced-decontextualized, so the same claim stated in two
  ;; contexts is two sentexes.  One copy, justified once per declaration — as a migrated
  ;; twin is justified once per equality — so dropping one leaves the copy standing.
  (tu/with-terms [rulesOver Ann Bob CxAlpha CxBeta]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBeta 'CxUniverse) 'CxUniverse)
    (let [d1 (v/assert kb (list 'decontextualized_predicate rulesOver) CxAlpha)
          d2 (v/assert kb (list 'decontextualized_predicate rulesOver) CxBeta)]
      (is (not= d1 d2) "two contexts, two sentexes")
      (v/assert kb (list rulesOver Ann Bob) CxAlpha)
      (let [u (v/handle-of kb (list rulesOver Ann Bob) 'CxUniverse)]
        (is (= 2 (count (v/supporting-justifications kb u))) "one witness per declaration")
        (v/retract! kb d1)
        (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse))
            "the copy stands on the surviving declaration")
        (v/retract! kb d2)
        (is (empty? (v/sentexes-matching kb (list rulesOver Ann Bob) 'CxUniverse))
            "and goes when the last one does")))))

(tu/deftest-kb a-consequence-of-a-lifted-fact-is-lifted-in-turn
  ;; The copy is a chaining seed, and what that provides is **placement**: forward chaining
  ;; already matches antecedents across contexts, so firing on the copy does not find
  ;; anything new — it places the conclusion in CxUniverse rather than only in the
  ;; context the fact came from.  A consequence of a fact true everywhere is true
  ;; everywhere too.
  (tu/with-terms [edgeTo reachesFrom A B CxAlpha CxSibling]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list edgeTo '?x '?y)] (list reachesFrom '?y '?x) 'CxUniverse {:direction :forward})
    (v/assert kb (list 'decontextualized_predicate edgeTo) 'CxUniverse)
    (v/assert kb (list edgeTo A B) CxAlpha)
    (testing "the conclusion is placed both where the fact was stated and in the universe"
      (is (= #{CxAlpha 'CxUniverse}
             (set (map :context (v/sentexes-matching kb (list reachesFrom B A) '?ctx))))))
    (testing "so a sibling context sees it, which it would not without the lift"
      (is (v/ask? kb (list reachesFrom B A) CxSibling)))))

(tu/deftest-kb a-negative-fact-is-not-lifted
  ;; `(not (P a))` has functor `not`, so a declaration about `P` does not reach it: the
  ;; positive extent becomes universal and the negative one stays in its context.
  ;; Deliberate, and pinned here so changing it has to be a decision.
  (tu/with-terms [flies Tweety Opus CxAlpha]
    (v/assert kb (list 'genlCx CxAlpha 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate flies) 'CxUniverse)
    (v/assert kb (list flies Tweety) CxAlpha)
    (v/assert kb (list 'not (list flies Opus)) CxAlpha)
    (is (seq (v/sentexes-matching kb (list flies Tweety) 'CxUniverse)) "the positive literal lifts")
    (is (empty? (v/sentexes-matching kb (list 'not (list flies Opus)) 'CxUniverse))
        "the negative literal does not")))

(tu/deftest-kb a-lift-out-of-sight-of-the-universe-stores-a-clashing-copy-and-reports-it
  ;; The definitional checks run where a fact is stated, against what is visible from
  ;; there, so they cover the CxUniverse copy whenever the stating context sees
  ;; CxUniverse.  Two contexts no genlCx edge names do not: neither sees the other's
  ;; fact, so each assert passes and the copies meet in CxUniverse.  The copy is admitted
  ;; as a firing's conclusion is: the clash is stored and decided there, in either order.
  (tu/with-terms [dog cat Rex CxOffA CxOffB]
    (is (not (v/sees? kb CxOffA 'CxUniverse)) "no edge names CxOffA")
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'genl cat 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate dog) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate cat) 'CxUniverse)
    (v/clear-violations! kb)

    (v/assert kb (list dog Rex) CxOffA)
    (testing "each fact is admissible where it is stated — neither context sees the other"
      (is (v/assert kb (list cat Rex) CxOffB)))
    (testing "both copies are stored in CxUniverse"
      (is (seq (v/sentexes-matching kb (list dog Rex) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list cat Rex) 'CxUniverse))))
    (testing "and the clash is a reported dilemma, with nothing filed in violations"
      (is (some #(and (= :disjoint (:kind %))
                      (= #{(list dog Rex) (list cat Rex)}
                         (into #{} (map :sentence) (:sides %)))
                      (every? #{'CxUniverse} (map :context (:sides %))))
                (v/contradictions kb)))
      (is (not-any? #(= :disjoint (:violation %)) (v/violations kb))))))

(tu/deftest-kb the-declaration-marks-a-predicate-and-takes-one-argument
  ;; It routes through `prop-problems` like the other unary metadata marks: a second
  ;; argument is not a target to lift into, it is a mistake.
  (tu/with-terms [rulesOver Somewhere]
    (testing "an individual is not a predicate"
      (is (= :not-well-formed
             (:type (try (v/assert kb (list 'decontextualized_predicate Somewhere) 'CxUniverse)
                         (catch clojure.lang.ExceptionInfo e (ex-data e)))))))
    (testing "and it takes exactly one argument"
      ;; :naming, not :not-well-formed — the property is snake_case now, so a second
      ;; argument is refused by the naming check before `wff` counts them
      (is (= :naming
             (:type (try (v/assert kb (list 'decontextualized_predicate rulesOver 'CxUniverse)
                                   'CxUniverse)
                         (catch clojure.lang.ExceptionInfo e (ex-data e)))))))))
