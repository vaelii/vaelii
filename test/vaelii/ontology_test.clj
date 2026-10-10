;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ontology-test
  "The shipped ontology as a *modelling* claim, where `starter-test` reads it as a schema
  that loads and reasons.

  What is pinned here is the structure of the mini-ontology rather than any one inference:
  which names are types and which are properties, that every type is placed under the
  root, that an ability is an event kind related to a kind rather than spelled as a
  predicate of its own, and how a claim about a kind reaches the kinds beneath it and
  stops where a nearer claim contradicts it.  Those are decisions somebody made, and every one of them is
  invisible to a test that only asks whether the KB answers a question.

  The genl-level exception is the centre of it.  A rule states its exception with
  `exceptWhen` (docs/exceptions.md); an *inherited* claim has no rule to except, and is
  stopped instead by a more specific claim — which works only for a default, never for a
  monotonic one, and both halves of that are tested because the asymmetry is the design."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.predicates :as pr]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private B 'CxBiology)
(def ^:private N 'CxNaturalWorld)

;; ---- an ability is an event kind related to a kind, not spelled as a predicate -------

(tu/deftest-kb an-ability-is-an-event-kind-related-to-a-kind
  ;; `flies` as a one-place predicate says the same thing, and says it in a shape that
  ;; cannot be generalized: every further ability needs a further predicate, and nothing
  ;; relates them.  An ability is named by the kind of event its holder can be the doer
  ;; of, so the abilities form a hierarchy inside the event kinds.
  (testing "each ability names a kind of event"
    (is (v/genl? kb 'flying 'event))
    (is (v/genl? kb 'travelling 'event))
    (is (v/genl? kb 'flying 'travelling)))
  (testing "travelling is a causal event, and event and causal both follow from causal_event"
    (is (v/genl? kb 'travelling 'causal_event))
    (is (v/genl? kb 'flying 'causal_event))
    (doseq [k '[travelling flying] super '[event causal]]
      (is (v/genl? kb k super) (str k " genl " super))))
  (testing "and no one-place flight predicate survives beside it"
    (is (empty? (v/sentexes-matching kb '(arity flies ?n) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(arity can_travel ?n) '?ctx))))
  (testing "and the starter KB has no capability type beside the event kinds"
    (is (not (contains? (set (v/terms kb)) 'capability)))
    (is (empty? (v/find-sentexes kb 'capability)))))

(tu/deftest-kb both-ability-predicates-type-their-second-argument-as-an-event-kind
  (testing "the declarations"
    (is (v/ask? kb '(genlArg hasCapability 2 event)))
    (is (v/ask? kb '(genlArg capabilityType 2 event))))
  (testing "an event kind nobody listed as an ability is accepted as one"
    (tu/with-terms [swimming Wanda]
      (v/assert kb (list 'genl swimming 'event) 'CxUniverse)
      (v/assert kb (list 'animal Wanda) N)
      (is (v/assert kb (list 'hasCapability Wanda swimming) N))
      (is (v/assert kb (list 'capabilityType 'fish swimming) N))))
  (testing "a kind that is not an event kind is convicted by genlArg, against event"
    ;; Pinned to the constraint-only reading, where `check` reports the conviction.
    (tu/without-entailing
     (tu/with-terms [Wanda]
       (v/assert kb (list 'animal Wanda) N)
       (doseq [s [(list 'hasCapability Wanda 'metal) (list 'capabilityType 'fish 'metal)]]
         (let [p (first (filter #(= :arg-genl (:type %)) (v/check kb s N)))]
           (is (= :arg-genl (:type p)) (str (pr-str s) " is convicted by genlArg"))
           (is (= 'event (:expected p)) (str (pr-str s) " is convicted against event"))))))))

(tu/deftest-kb a-bird-that-flies-travels
  ;; flying genl travelling, and (transitiveInArg hasCapability 2 genl) carries a
  ;; claim about flying up to travelling at retrieval.
  (tu/with-terms [Robin]
    (v/assert kb (list 'bird Robin) N)
    (v/assert kb (list 'hasCapability Robin 'flying) N)
    (is (v/ask? kb (list 'hasCapability Robin 'flying) N))
    (is (v/ask? kb (list 'hasCapability Robin 'travelling) N))))

(tu/deftest-kb what-a-kind-can-do-reaches-the-kinds-beneath-it
  ;; One sentence is stored.  Everything else here is the taxonomy being read.
  ;; `capabilityType`, not `hasCapability`: this is the kind talking, and the two readings
  ;; are two predicates (`the-two-capability-readings-are-two-predicates-and-say-so`).
  (testing "the stated claim"
    (is (v/ask? kb '(capabilityType bird flying) B)))
  (testing "and the kinds nobody wrote anything about"
    (is (v/ask? kb '(capabilityType eagle flying) B))
    (is (v/ask? kb '(capabilityType sparrow flying) B)))
  (testing "inherited rather than stored — one sentex carries all of it"
    (is (empty? (v/sentexes-matching kb '(capabilityType eagle flying) '?ctx))))
  (testing "and it climbs the genl hierarchy of event kinds: what can fly can travel"
    (is (v/ask? kb '(capabilityType bird travelling) B))
    (is (v/ask? kb '(capabilityType eagle travelling) B)))
  (testing "answered by transitiveInArg, so the kind level stores no rule's output"
    (is (empty? (v/sentexes-matching kb '(capabilityType bird travelling) '?ctx)))))

(tu/deftest-kb a-nearer-claim-stops-an-inherited-default-at-itself
  ;; The genl-level counterpart of `exceptWhen`.  There is no rule to block here — the
  ;; reach is the taxonomy's — so what stops it is a claim about the nearer kind.
  (testing "the excepted kind"
    (is (not (v/ask? kb '(capabilityType penguin flying) B))))
  (testing "its siblings are untouched, which is what makes this an exception"
    (is (v/ask? kb '(capabilityType eagle flying) B))
    (is (v/ask? kb '(capabilityType crow flying) B)))
  (testing "and the general claim survives being excepted"
    (is (v/ask? kb '(capabilityType bird flying) B))))

(tu/deftest-kb the-exception-is-a-claim-and-not-merely-a-silence
  ;; "Penguins do not fly" is something the KB says, not something it fails to say.  An
  ;; application can query it and argue from it; an absence supports no argument.
  (testing "at the kind"
    (is (seq (v/sentexes-matching kb '(not (capabilityType penguin flying)) '?ctx))))
  (testing "and at the member, by its own rule"
    (is (seq (v/sentexes-matching kb '(not (hasCapability Tweety flying)) N)))))

(tu/deftest-kb a-claim-about-a-kind-does-not-reach-its-members-on-its-own
  ;; The bridge is a rule, written once and deliberately, because "every bird flies" and
  ;; "this bird flies" differ by a quantifier the KB will not guess (typeToInstancePred).
  (testing "the member's flight is derived, and it is a record"
    (is (v/ask? kb '(hasCapability Sam flying) N))
    (is (seq (v/sentexes-matching kb '(hasCapability Sam flying) N))))
  (testing "travelling follows from the hierarchy, not a stored forward-rule conclusion"
    (is (v/ask? kb '(hasCapability Sam travelling) N))
    (is (empty? (v/sentexes-matching kb '(hasCapability Sam travelling) N))
        "answered by transitiveInArg, not stored — no redundant rule"))
  (testing "and the flightless member gets neither"
    (is (not (v/ask? kb '(hasCapability Tweety flying) N)))
    (is (empty? (v/sentexes-matching kb '(hasCapability Tweety travelling) N)))))

(tu/deftest-kb the-two-capability-readings-are-two-predicates-and-say-so
  ;; the entailing reading: the derivation is the subject
  (tu/with-entailing
    ;; One symbol read at both levels has to pick one argument check for both, and whichever
    ;; it picks convicts the half it was not written for: `arg … 1 animal` is right for
    ;; `(… Tweety flying)` and wrong for `(… bird flying)`, since a kind is not a member of
    ;; the type it lies under.  So: two predicates, the kind-level one marked, and the pair
    ;; named in prose because the predicate that names pairs cannot take a mixed half.
    (testing "the kind-level half relates kinds, and says so"
      (is (v/ask? kb '(type_relation_predicate capabilityType))))
    (testing "the instance-level half is MIXED — one animal to one event kind — so it
            carries no relation_kind, and its two positions take different checks"
      (is (not (v/ask? kb '(instance_relation_predicate hasCapability))))
      (is (not (v/ask? kb '(type_relation_predicate hasCapability))))
      (is (v/ask? kb '(arg hasCapability 1 animal)))
      (is (v/ask? kb '(genlArg hasCapability 2 event))))
    (testing "so declaring the pairing would mark the mixed half — typeToInstancePred
            types its second argument an instance half, and derives that mark"
      (tu/with-terms [CxPairing]
        (v/assert kb (list 'genlCx CxPairing 'CxLife) 'CxUniverse)
        (v/assert kb '(typeToInstancePred capabilityType hasCapability) CxPairing)
        (is (v/isa? kb 'hasCapability 'instance_relation_predicate CxPairing))))
    (testing "and neither reading answers the other's question"
      (is (not (v/ask? kb '(hasCapability bird flying) B)))
      (is (not (v/ask? kb '(capabilityType Sam flying) N))))))

(tu/deftest-kb every-fact-the-starter-ships-satisfies-the-declarations-it-ships
  ;; The guard the `hasCapability` split existed to install.  A declaration arriving after
  ;; the content it convicts is accepted — that is the open-world reading, and `violations`
  ;; carries no retroactive report for `:arg-type` — so the starter could hold seven facts
  ;; its own checker rejected and nothing said a word.  Loading is not the check; this is.
  ;;
  ;; Facts only.  A rule reaches `check` as its `implies` form and an `exceptWhen` as a
  ;; `sentexHandle` reference, and both are engine-minted encodings rather than anything a
  ;; `.txt` author wrote — `check` reads them out of the rule that gives their variables
  ;; meaning, so convicting them says nothing about the shipped content.
  (let [encoding? (fn [s] (let [s (if (and (seq? s) (= 'not (first s))) (second s) s)]
                            (and (seq? s) (contains? '#{implies exceptWhen} (first s)))))
        facts     (->> (v/terms kb)
                       (mapcat #(v/find-sentexes kb %))
                       (reduce (fn [m sx] (assoc m (:id sx) sx)) {})
                       vals
                       (remove #(some? (:antecedent %)))
                       (remove #(encoding? (:sentence %))))
        guilty  (for [sx    facts
                      :let  [ps (v/check kb (:sentence sx) (:context sx))]
                      :when (seq ps)]
                  [(:sentence sx) (:context sx) (mapv :type ps)])]
    (is (empty? guilty)
        (str "shipped facts their own declarations convict: " (vec guilty)))))

(def ^:private untyped-positions
  "The argument positions of arity **2 and up** that the shipped text contexts leave
  undeclared, each with the reason no `arg` / `genlArg` / `quotedArg` can name it.  A
  position that is not here and not declared fails the test below; a position here that
  gains a declaration fails it too, so the roster stays a list of reasons rather than a
  list of debts.

  A **unary** predicate's one position is exempt as a class and is not rostered — see
  the test."
  (merge
   {'[genl 1]  "predicate specializations: (genlArg genl 1 thing) is false of (genl predicateTypeByArity relationTypeByArity), whose ends are binary predicates"
    '[genl 2]  "the root: (genlArg genl 2 thing) would entail (genl thing thing), refused as irreflexive"
    '[comment 1] "the commented term: a type, a predicate, an individual or a context, so no type below thing covers it"
    '[implementationNote 1] "the noted term: a type, a predicate, an individual or a context, as comment's is"}
   ;; slots that hold a term of any kind, which no type below thing covers
   {'[believes 1]           "a believer, whose types CxCore cannot see"
    '[evaluate 2]           "an evaluate expression: a number or an application"
    '[likes 2]              "what a person likes"
    '[termOfUnit 1]         "the reified constant of a termOfUnit"
    '[rewriteOf 1]          "either side of a rewriteOf"
    '[rewriteOf 2]          "either side of a rewriteOf"
    '[seeAlso 1]            "a cross-referenced term"
    '[seeAlso 2]            "a cross-referenced term"
    '[doneBy 2]             "an event's doer: a person, an animal, a machine or a process"
    '[performedBy 2]        "an event's doer: a person, an animal, a machine or a process"
    '[perceives 1]          "a perceiver, whose types CxCore cannot see"
    '[sees 1]               "a perceiver, whose types CxCore cannot see"
    '[seeImage 1]           "a perceiver, whose types CxCore cannot see"
    '[seeImage 2]           "the image perceived: a thing of any kind"
    '[watchVideo 1]         "a perceiver, whose types CxCore cannot see"
    '[watchVideo 2]         "the video perceived: a thing of any kind"
    '[agentHasTool 1]       "what a tool is available to, whose types the upper ontology does not name"
    '[toolArgType 3]        "the type a tool's argument takes: a type of any kind"
    '[argN 1]               "the term found at a position of a formula"
    '[sameAs 1]             "either side of a sameAs"
    '[sameAs 2]             "either side of a sameAs"
    '[equals 1]             "either side of an equals"
    '[equals 2]             "either side of an equals"
    '[input 2]              "what went into an event: a thing of any kind"
    '[destroyedInput 2]     "what went into an event: a thing of any kind"
    '[preservedInput 2]     "what went into an event: a thing of any kind"
    '[output 2]             "what an event left behind, tangible or intangible"
    '[predAllInstance 3]    "a rule generator's fixed filler"
    '[predExistsInstance 3] "a rule generator's fixed filler"
    '[predInstanceAll 2]    "a rule generator's fixed filler"
    '[predInstanceExists 2] "a rule generator's fixed filler"
    '[means 2]              "the meaning: what a term denotes or the proposition a sentence expresses, a thing of any kind"
    '[denotes 2]            "what a denotational_term names: a thing of any kind"}
   (into {} (for [p '[positiveExample negativeExample borderlineExample]]
              {[p 1] "an exemplified term"
               [p 2] "the example, a sentence written as a term"}))
   ;; the five aggregation operators: a result variable, a census variable, a sentence body
   (into {} (for [op '[agg/count agg/sum agg/avg agg/min agg/max] i [1 2 3]]
              [[op i] "an operator slot — a variable, a variable and a sentence body"]))
   ;; koinii's speech acts name their target as (sentexHandle H) — a mention the engine
   ;; mints with no result type — or carry a proposition; a demand on either would
   ;; convict every meta-sentex the app writes
   (into {} (for [[p i] '[[asserts 2] [queries 2] [answers 2] [answers 3] [justifies 2]
                          [justifies 3] [disputes 2] [endorses 2] [refuse 2] [retracts 2]
                          [votesFor 2] [votesAgainst 2] [notUnderstood 2]]]
              [[p i] "a sentex handle or a proposition, a mention no argument type names"]))))

(deftest every-position-of-a-shipped-arity-above-one-is-typed-or-excused
  ;; Read off the text files rather than a loaded KB, because the claim is about what the
  ;; contexts *write*: an author declaring (arity P n) for n above 1, or a class that
  ;; fixes such an n, owes a type for every one of the n positions — `check` reads only
  ;; what is declared, so an undeclared position admits any term and a bad index or a
  ;; wrong-kinded argument stores clean.  Every kb/*.txt is read, the app's koinii
  ;; contexts included.
  ;;
  ;; **A unary predicate owes nothing here.**  Its one position is its membership, so
  ;; `(arg P 1 T)` says what `(genl P T)` says of the same extent — one per instance
  ;; against one edge — and for the terms the engine interprets the shape in
  ;; `vaelii.impl.predicates` refuses a wrong argument before any declaration is read
  ;; (`(symmetric Fred)` is `:not-well-formed`, not `:arg-type`).  A declaration that
  ;; convicts nothing and mints a record per instance under `*assertive-arg-types?*` is
  ;; not a debt to collect, so the demand stops at arity 2 (docs/argtypes.md).  A unary
  ;; predicate whose position is the only check it has still declares one — the eight
  ;; state predicates in CxLife and CxTime do — and this test does not ask it to.
  (let [files    (->> (file-seq (io/file "resources/kb"))
                      (filter #(.endsWith (.getName ^java.io.File %) ".txt")))
        sents    (mapcat text/read-forms files)
        of       (fn [functors] (filter #(and (seq? %) (contains? functors (first %))) sents))
        arities  (merge (into {} (for [s (of '#{unary_predicate binary_predicate ternary_predicate})]
                                   [(second s) ('{unary_predicate 1 binary_predicate 2 ternary_predicate 3}
                                                (first s))]))
                        (into {} (for [s (of '#{arity})] [(second s) (nth s 2)])))
        declared (set (for [s (of '#{arg genlArg quotedArg}) :when (integer? (nth s 2))]
                        [(second s) (nth s 2)]))
        gaps     (set (for [[p n] arities
                            :when (and (integer? n) (< 1 n))
                            i    (range 1 (inc n))
                            :when (not (declared [p i]))]
                        [p i]))
        excused  (set (keys untyped-positions))]
    (is (seq arities) "the text contexts were found and read")
    (is (empty? (remove excused gaps))
        (str "positions the shipped contexts leave untyped: " (pr-str (sort (remove excused gaps)))))
    (is (empty? (remove gaps excused))
        (str "excused positions that are now declared (drop them from the roster): "
             (pr-str (sort (remove gaps excused)))))))

;; ---- the exception mechanism itself, apart from birds --------------------

(tu/deftest-kb an-inherited-default-is-undercut-and-an-inherited-monotonic-one-is-not
  ;; `transitiveInArgInverse`'s contract in one test, both halves.  A default yields to a nearer
  ;; claim; a monotonic claim does not, because yielding would make a stated certainty
  ;; depend on what else got said, and the strength is exactly the author saying it must
  ;; not.  Two independent hierarchies so neither answer can come from the other.  The
  ;; declaration and the hauler edges are `:monotonic`, since a reading resting on a
  ;; `:default` reason is undercut as a `:default` claim is.
  (tu/with-terms [carriesLoad pack_animal mule_kind hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) 'CxUniverse)
    (v/assert kb (list 'transitiveInArgInverse carriesLoad 1 'genl) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl pack_animal 'animal) 'CxUniverse)
    (v/assert kb (list 'genl mule_kind pack_animal) 'CxUniverse)
    (v/assert kb (list 'genl hauler_kind 'animal) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl cart_kind hauler_kind) 'CxUniverse {:strength :monotonic})
    (testing "a default reaches the subkind"
      (v/assert kb (list carriesLoad pack_animal 'Bone1) 'CxUniverse)
      (is (v/ask? kb (list carriesLoad mule_kind 'Bone1) 'CxUniverse)))
    (testing "and a nearer claim stops it there"
      (v/assert kb (list 'not (list carriesLoad mule_kind 'Bone1)) 'CxUniverse)
      (is (not (v/ask? kb (list carriesLoad mule_kind 'Bone1) 'CxUniverse)))
      (is (v/ask? kb (list carriesLoad pack_animal 'Bone1) 'CxUniverse)))
    (testing "a monotonic claim reaches the subkind the same way"
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) 'CxUniverse {:strength :monotonic})
      (is (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'CxUniverse)))
    (testing "and a nearer default does NOT displace it — the general claim still stands"
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) 'CxUniverse)
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) 'CxUniverse)
          "the monotonic claim is not undercut, which is inherit/undercut?'s contract"))
    (testing "the nearer default loses, and the subkind answers the inherited claim"
      ;; The nogood's members are the stored denial and everything the reading rests on —
      ;; the general claim, the declaration and the `genl` edge — and the `:default`
      ;; denial is its unique weakest member, so it is defeated.
      (is (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'CxUniverse))
      (is (not (v/ask? kb (list 'not (list carriesLoad cart_kind 'Bone1)) 'CxUniverse))))
    (testing "and a decided clash is reported by neither reading"
      ;; The mule/pack_animal half is a `:default` general claim and is undercut, so it
      ;; forms no nogood either.
      (is (empty? (filter #(= :inherited (:kind %))
                          (concat (v/contradictions kb) (v/conflicts kb))))))))

;; ---- what is a type, and what is only a property ------------------------

(def ^:private biology-properties
  "The seven CxLife properties placed under the kind each is said of."
  '{alive biological, dead biological, mortal organism,
    asleep animal, awake animal, breathes_air animal, warm_blooded animal})

(tu/deftest-kb a-type-is-a-noun-and-a-property-is-not-a-type
  ;; The naming rules make `alive` and `mortal` legal unary predicates, and nothing in
  ;; them says whether a name belongs in the genl hierarchy.  That is a modelling
  ;; decision: a type is a kind of thing and wants a noun, while a property is something
  ;; a thing *is*.  A property may sit BELOW the kind it is said of — the alive
  ;; organisms are some of the organisms — but never above a kind: that would make
  ;; "mortal" a kind that organisms are a kind OF.  Were one wanted as a type in that
  ;; sense it would be spelled for it — `mortal_being`, not `mortal`.
  (testing "the properties the biology theory concludes are placed under their kind"
    (doseq [[p kind] biology-properties]
      (is (v/genl? kb p kind) (str p " is placed under " kind))
      (is (v/genl? kb p 'thing) (str p " reaches thing"))
      (is (v/isa? kb p 'unary_predicate)
          (str p " is still a one-place predicate"))))
  (testing "and no type sits below any of them"
    (doseq [p (keys biology-properties)]
      (is (= #{p} (v/specs kb p))
          (str p " is a property, not a kind — nothing may be placed under it"))
      (is (not (v/genl? kb (biology-properties p) p))
          (str (biology-properties p) " is not a kind of " p))))
  (testing "while the kinds they are said of are types, and reach the root"
    (doseq [t '[animal bird penguin dog person tangible event flying]]
      (is (v/genl? kb t 'thing) (str t " must reach thing")))))

(tu/deftest-kb every-shipped-type-is-placed-under-the-root
  ;; An unplaced type is invisible to every closure the engine reads, so it is a type in
  ;; spelling only.  `islands` is the taxonomy's own count of them.
  (let [q (v/kb-quality kb)]
    (is (zero? (:islands (:taxonomy q)))
        "a type with no path to thing answers nothing and is a type in spelling only")
    (is (= (:edged (:taxonomy q)) (:rooted (:taxonomy q)))
        "every name with a genl edge reaches the root")))

(def ^:private placed-unary-predicates
  "Fifteen shipped `unary_predicate` terms each placed under `thing` by a stated `genl`
  edge, so the `:not-under-thing` sweep (docs/integrity.md) reports none of them.  The
  seven biology properties among them are placed under the kind each is said of, and
  `a-type-is-a-noun-and-a-property-is-not-a-type` holds that no kind sits below one."
  '#{initially functional_at_instant
     abducible_predicate closed_extent_predicate decontextualized_predicate
     target_following_predicate forced_decontextualized_predicate
     sibling_disjoint
     alive dead mortal asleep awake breathes_air warm_blooded})

(tu/deftest-kb every-placed-unary-predicate-reaches-thing
  ;; `islands` above counts names WITH a genl edge, so a unary predicate carrying none is
  ;; never an island.  The `:not-under-thing` sweep reads the declaration instead, over a
  ;; caller-owned candidate set, from CxWell, which sees every upper and middle context.
  (let [report (v/kb-integrity kb placed-unary-predicates 'CxWell)]
    (is (= (count placed-unary-predicates) (:candidate-count report)))
    (is (empty? (:not-under-thing report))
        (str "each reaches thing by a genl path visible from CxWell; "
             (count (:not-under-thing report)) " do not: "
             (pr-str (mapv :term (:not-under-thing report)))))))

(tu/deftest-kb sibling-disjoint-is-an-at-least-metatype
  ;; What sibling_disjoint marks is a type (genlArg 1 thing), so sibling_disjoint itself is
  ;; a type of types.  It may mark a first-order type such as animal or a metatype, so it
  ;; is at_least_metatype rather than metatype.
  (is (v/isa? kb 'sibling_disjoint 'at_least_metatype)))

(tu/deftest-kb the-starter-states-its-typeGenl-and-genl-requirements
  ;; CxCore requires every at_least_metatype to name a typeGenl and every unary_predicate
  ;; to name a genl.
  (doseq [[pred indep] '[[typeGenl at_least_metatype] [genl unary_predicate]]]
    (is (v/ask? kb (list 'predAllSpecified pred indep) 'CxUniverse)
        (str "(predAllSpecified " pred " " indep ") is stated")))
  (testing "every unary_predicate the starter and the test world ship names a genl"
    (is (= {:status :audited :violations #{}}
           (v/specified-violations kb 'genl 'unary_predicate 'CxUniverse))))
  (testing "sibling_disjoint names its typeGenl, so the audit does not report it"
    (let [r (v/specified-violations kb 'typeGenl 'at_least_metatype 'CxUniverse)]
      (is (= :audited (:status r)))
      (is (not (contains? (:violations r) 'sibling_disjoint))))))

(tu/deftest-kb empty-and-nonempty-state-typeGenl-so-the-audit-does-not-report-them
  ;; empty and nonempty are at_least_metatype (above) with no stated typeGenl until
  ;; CxCore states (typeGenl empty thing) and (typeGenl nonempty thing) beside their
  ;; declaration — vacuous, since thing is already a genl of every type, and inert,
  ;; since typeGenl has no inference path.
  (testing "the two typeGenl facts are present"
    (is (v/ask? kb '(typeGenl empty thing) 'CxUniverse))
    (is (v/ask? kb '(typeGenl nonempty thing) 'CxUniverse)))
  (testing "the typeGenl audit no longer reports empty or nonempty"
    (let [r (v/specified-violations kb 'typeGenl 'at_least_metatype 'CxUniverse)]
      (is (= :audited (:status r)))
      (is (not (contains? (:violations r) 'empty)))
      (is (not (contains? (:violations r) 'nonempty)))))
  (testing "typeGenl is read by nothing, so the two facts conclude no new genl edge"
    (let [spec (pr/entry 'typeGenl)]
      (is (= [:none] (:storage spec))
          "typeGenl stores a fact for a reader only, never for inference")
      (is (false? (:checked spec))
          "typeGenl has no structural well-formedness arm — no engine reads it"))))

(def ^:private type-relating-predicates
  "The predicates whose every argument is a TYPE (or a predicate) the claim relates, so the
  claim is meaningful only in a context that sees all of them at once.  A `genl`, `disjoint`,
  `orthogonal`, `intersection` or `typeGenl` between two members' terms therefore belongs at
  the context
  that sees both — the collector (CxUniverse for the upper spindle), never the head, which
  sees no member (docs/contexts.md, and the rule `resources/kb/CxUniverse.txt`'s own header
  states).

  `arg` / `genlArg` / `quotedArg` / `result` / `interArg` and the relation-metadata marks are
  deliberately NOT here: they constrain a relation's OWN argument or classify the relation
  itself, and the type they name is checked from the DATA context that asserts a tuple — every
  data context sits below the collector and sees the whole upper spindle — so a member
  declaring `(arg parentOf 1 animal)` over CxOrganism's `animal` is checked where it bites and
  is not misplaced."
  '#{genl disjoint typeGenl genlInverse intersection partitionedByType
     covering separating partition orthogonal})

(tu/deftest-kb no-authored-type-relation-names-a-term-its-own-context-cannot-see
  ;; The scoped complement of `every-shipped-type-is-placed-under-the-root`.  That test asks
  ;; whether a type reaches `thing` from SOME context; this one asks whether a claim RELATING
  ;; types (`type-relating-predicates`) is written where every type it names reaches `thing`
  ;; from that same context.  A relating claim written where one side is invisible does not
  ;; separate or subsume the two types in that context, and names a term that context does
  ;; not root.
  ;;
  ;; The spindle is what makes this possible.  CxCore, the head, sees no member
  ;; (docs/contexts.md), so `(typeGenl stuff_type_by_substance substance)` in CxCore over a
  ;; `substance` defined in CxAbstract stores clean — an undeclared symbol cannot violate an
  ;; assert-time check (open-world, docs/taxonomy.md) — and the claim lands in a context that
  ;; cannot read its own subject.  A relation between two members' terms therefore belongs at
  ;; or above the collector that sees both.
  ;;
  ;; Read off the text files the starter actually loads — `CxCore.txt`, `upper/`, `middle/`
  ;; and the collector `CxUniverse.txt` (`vaelii.host.starter`) — because the claim is about
  ;; what those contexts *write*, not what the engine derives or the starter publishes
  ;; (`(unary_predicate T)` is asserted into CxCore for every subtype of `thing`, and the
  ;; arity rules conclude from those in CxCore too; both are deliberate).  The loaded KB
  ;; still answers rooting, since `v/genl?` scoped to a context is the exact visibility the
  ;; write side checks against.
  (let [anywhere (fn [t]   (v/genl? kb t 'thing))          ; reaches the root from some context
        rooted?  (fn [t c] (v/genl? kb t 'thing c))        ; reaches it from context c
        up       (memoize (fn [c] (set (v/context-up kb c))))
        homes    (fn [ts]                                  ; most-general contexts rooting every t in ts
                   (let [all (filter (fn [c] (every? #(rooted? % c) ts)) (v/contexts kb))]
                     (filterv (fn [c] (not-any? #(and (not= % c) (contains? (up c) %)) all))
                              all)))
        relating? (fn [s] (and (seq? s) (contains? type-relating-predicates (first s))))
        resolve*  (fn [[form fctx]]                         ; (ist Cx S) writes S into Cx
                    (if (and (seq? form) (= 'ist (first form)))
                      [(nth form 2) (nth form 1)]
                      [form fctx]))
        names    (fn [sentence] (distinct (filter symbol? (tree-seq seq? seq sentence))))
        files    (list* (io/file "resources/kb/CxCore.txt") (io/file "resources/kb/CxUniverse.txt")
                        (filter text/kb-file? (mapcat #(file-seq (io/file (str "resources/kb/" %)))
                                                      ["upper" "middle"])))
        forms    (->> files
                      (mapcat (fn [f] (let [c (text/context-of f)]
                                        (map #(vector % c) (text/read-forms f)))))
                      (map resolve*)
                      (filter (fn [[s _]] (relating? s))))
        blind    (for [[s c] forms
                       :let  [miss (filter #(and (anywhere %) (not (rooted? % c))) (names s))]
                       :when (seq miss)]
                   {:context c :sentence s :cannot-see (vec miss) :move-to (homes (distinct miss))})]
    (is (seq forms) "the shipped context files were found and read")
    (is (empty? blind)
        (str "type relations written where a term they name is invisible — move each to a "
             "context that sees the named types (or root the types at/above the head):\n"
             (apply str (interpose "\n"
                                   (for [b blind]
                                     (str "  " (:context b) " asserts " (pr-str (:sentence b))
                                          "\n    cannot see " (pr-str (:cannot-see b))
                                          " — defined in " (pr-str (:move-to b))
                                          ", so move the assertion there"))))))))

(def ^:private head-terms-one-member-may-keep
  "CxCore inert terms only one spindle member references today, kept in the head on
  purpose — each with the reason.  A term absent from this roster that only one member uses
  fails the test below; a term here that gains a second member user fails it too, so the
  roster stays a list of reasons rather than a list of debts."
  '{typeToInstancePred "a relation-linking predicate the head declares as vocabulary; only CxAbstract uses it (partType / partOf) today"})

(tu/deftest-kb head-vocabulary-a-single-member-uses-belongs-in-that-member
  ;; The inverse of `no-authored-type-relation-names-a-term-its-own-context-cannot-see`.
  ;; CxCore, the head, holds a term because more than one spindle member has to SEE it — a
  ;; member sees the head and not its siblings, so a term two members share lives in the head
  ;; (docs/contexts.md).  A CxCore ontology term that only ONE member ever references does not
  ;; earn that placement: it could live in that member, and holding it in the head widens the
  ;; shared vocabulary for no reader that needs it there.  This names each such term and the
  ;; single member to move it to.
  ;;
  ;; Scope: the INERT vocabulary CxCore declares (`v/vocabulary-audit`'s `:inert`) — the
  ;; ontology terms the engine reads by no name.  An `:enforced` term (a code path reads it by
  ;; name) stays in the head whatever its members, so it is out of scope.  A term no member
  ;; references — used only by CxCore's own structure — is head vocabulary, not a member's, so
  ;; it is not flagged; only a count of exactly one member is.
  ;;
  ;; A term CxCore itself references from another term (a subtype, a disjoint partner, an arg
  ;; type, a rule that names it) cannot move down: the head would then reference a term it
  ;; cannot see.  `core-structural-use?` reads that off the head's own sentexes — the term
  ;; appears as a functor or an argument past the subject (the second element), rather than
  ;; only as the subject of its own declaration — and holds such a term in the head.
  (let [members  (set (map text/context-of
                           (mapcat #(filter text/kb-file? (file-seq (io/file (str "resources/kb/" %))))
                                   ["upper" "middle"])))
        ;; authored use only: a rule's conclusion placed in a member names the term there
        ;; without anybody having written it, and moving the term down would not move it
        users    (fn [t] (distinct (filter members (map :context (filter #(v/premise? kb (:id %))
                                                                         (v/find-sentexes kb t))))))
        core-structural-use?
        (fn [t] (some (fn [sx]
                        (let [s (:sentence sx)]
                          (and (seq? s) (not= 'comment (first s))
                               (some #{t} (cons (first s) (drop 2 s))))))
                      (filter #(= 'CxCore (:context %)) (v/find-sentexes kb t))))
        loners   (for [[t _why] (:inert (v/vocabulary-audit kb))
                       :let  [ms (users t)]
                       :when (and (= 1 (count ms))
                                  (not (core-structural-use? t))
                                  (not (contains? head-terms-one-member-may-keep t)))]
                   {:term t :used-only-by (first ms)})]
    (is (empty? loners)
        (str "CxCore ontology terms only one member uses — move each to that member (or add "
             "it to `head-terms-one-member-may-keep` with a reason):\n"
             (apply str (interpose "\n"
                                   (for [c loners]
                                     (str "  " (:term c) " — used only by " (:used-only-by c)
                                          ", so move it there"))))))))

(tu/deftest-kb every-type-a-loaded-membership-names-is-named-by-another-sentence
  ;; A membership in a type no other sentence names reaches no genl edge, argument
  ;; declaration or comment, so a misspelled or retired type name stores clean and nothing
  ;; reads it.  The starter and the test-world state no such membership.
  (let [membership? (fn [t s] (and (seq? s) (= 2 (count s)) (= t (first s))))
        types       (into #{} (comp (filter #(v/premise? kb (:id %)))
                                    (map :sentence)
                                    (keep #(when (and (seq? %) (= 2 (count %))) (first %)))
                                    (filter symbol?))
                          (v/sentexes-matching kb '(?p ?x) '?ctx))]
    (is (< 50 (count types)) "the reading ran over the loaded memberships")
    (is (= [] (filterv (fn [t] (every? #(membership? t (:sentence %)) (v/find-sentexes kb t)))
                       (sort types))))))

;; ---- the shipped rules, read against each other --------------------------

(tu/deftest-kb no-shipped-rule-is-covered-by-another
  ;; `kb-quality`'s subsumption reading over the shipped schema and the test-world's
  ;; fables.  Zero is the claim: nothing here fires wherever another rule fires and
  ;; concludes no more than it does, so no rule in the ontology is carrying its weight
  ;; only because somebody wrote it twice at two levels of the hierarchy.
  ;;
  ;; The arity generator is the case that tests the claim.  It stamps one rule per
  ;; `relationTypeByArity` fact, and CxCore ships three — over `unary`, `binary` and
  ;; `ternary`.  A `(predicateTypeByArity unary_predicate 1)` fact beside them would
  ;; stamp a fourth firing wherever the first already fires, since `unary_predicate`
  ;; is a `unary`; CxCore states that membership with a `genl` edge instead, so the
  ;; reading stays at zero and a mapping table that grew a redundant member would
  ;; show up here.
  (let [q (:subsumption (v/kb-quality kb {:limit 100}))]
    (is (pos? (:total q)) "the reading ran over rules rather than over nothing")
    (is (not (:truncated? q)) "and over all of them")
    (is (zero? (:subsumed-count q))
        (str "covered: " (pr-str (mapv (juxt :by-sentence :sentence) (:subsumed q)))))))

(tu/deftest-kb a-generated-rule-is-not-exempt-from-the-subsumption-reading
  ;; The reading does not spare a rule for having been stamped by a generator: a
  ;; mapping fact over a type and a second over its subtype mint two rules, and the
  ;; narrower one fires nowhere the broader does not.
  (tu/with-terms [broad_type narrow_type outcome_type generatesType]
    (v/assert kb (list 'genl broad_type 'thing) 'CxCore)
    (v/assert kb (list 'genl narrow_type broad_type) 'CxCore)
    (v/assert kb (list 'genl outcome_type 'thing) 'CxCore)
    (v/assert kb (list 'implies (list generatesType '?type)
                       (list 'implies (list '?type '?x) (list outcome_type '?x))) 'CxCore {:direction :forward})
    (doseq [type [broad_type narrow_type]]
      (v/assert kb (list generatesType type) 'CxCore))
    (let [rule (fn [type] (list 'implies (list type '?x) (list outcome_type '?x)))
          pair [(v/handle-of kb (rule broad_type) 'CxCore)
                (v/handle-of kb (rule narrow_type) 'CxCore)]
          q (:subsumption (v/kb-quality kb {:limit 100}))]
      (is (every? some? pair) "both rules are stamped")
      (is (not (:truncated? q)))
      (is (some #(= pair [(:by %) (:subsumed %)]) (:subsumed q))
          "the narrower generated rule is reported as covered"))))

(tu/deftest-kb every-negated-conclusion-the-ontology-can-clash-with-is-stated-as-an-exception
  ;; The other rule-hygiene reading, and the structure of what it finds here is the finding.
  ;; Every pair whose conclusions contradict outright — a bird's flight against a
  ;; penguin's, wakefulness against sleep, life against death, and the shepherd boy's
  ;; credibility against his lying — is one of the two rules **stating** the other as an
  ;; `exceptWhen`, which is what `:excepted` marks.  Nothing else is left: the arity table
  ;; would be three `:functional` pairs, each two of the classification rules concluding a
  ;; different `(arity ?p n)` for one `?p`, and the three classes are declared pairwise
  ;; `disjoint`, so no `?p` satisfies two antecedents and the pairs are unreachable rather
  ;; than unstated (docs/quality.md).
  ;;
  ;; No `:disjoint` pair is left.  CxCriedWolf's `lied_before → liar` concludes a person,
  ;; and two kinds of rule conclude a type disjoint from one: the signed refinements of
  ;; `integer` and the relation classifications (arity, `bijection`, the arity classes).
  ;; No ground term satisfies both antecedents of any such pair — nothing is a person and
  ;; an integer or a relation — and the checker reads that off the
  ;; `arg` declarations: `(arg lied_before 1 person)` types the liar rule's variable a
  ;; `person`, disjoint from what the other rule states or concludes about the same term,
  ;; so `arg-type-conflicted?` drops every such pair as unreachable (vaelii#95).
  (let [pairs (:pairs (:clashes (v/kb-quality kb {:limit 100})))
        kinds (frequencies (map :kind pairs))]
    (is (= {:negation 4} kinds)
        (str "clashes: " (pr-str (mapv (juxt :kind :sentences) pairs))))
    (is (every? :excepted (filter #(= :negation (:kind %)) pairs))
        "negation clashes are excepted")))

(tu/deftest-kb the-arity-rules-clash-with-each-other-in-neither-direction
  ;; The reading's own half of the arity separation.  The generator stamps one rule per
  ;; exact class, and two of them conclude two arities for one relation only where the
  ;; relation holds both classes — which `(disjoint unary binary)` and its two peers
  ;; refuse on the antecedents.  No `?relation` satisfies two of them, so the pair is
  ;; unreachable rather than unstated (docs/quality.md).
  ;;
  ;; `(partition thing tangible intangible)` makes a relation-classification conclusion and a
  ;; story-predicate conclusion disjoint, so the arity rules would pair with CxCriedWolf's
  ;; `lied_before → liar` if the checker read only the conclusions.  It reads the
  ;; antecedents' `arg` declarations too: `(arg arity 1 relation)` types the arity rule's
  ;; variable a `relation`, disjoint from the `person` the paired rule concludes, so
  ;; `arg-type-conflicted?` drops the pair as unreachable (vaelii#95).  The arity table
  ;; therefore pairs with nothing.
  (let [pairs   (:pairs (:clashes (v/kb-quality kb {:limit 100})))
        about   (fn [f] (filter (fn [p] (some #(some #{f} (flatten %)) (:sentences p)))
                                pairs))]
    (is (empty? (about 'arity))
        (str "the arity table pairs with nothing: " (pr-str (mapv :sentences (about 'arity)))))
    (is (empty? (about 'unary_predicate))
        (str "nor do the classes: " (pr-str (mapv :sentences (about 'unary_predicate)))))))

(tu/deftest-kb a-predicate-is-at-most-one-of-the-three-arity-classifications
  ;; The declaration that empties the reading above.  A predicate takes one number of
  ;; arguments, so a second classification is stored as a disjoint clash with the first,
  ;; which the settle weighs.
  (testing "the three pairs are separated, and pairwise — not by a mark on predicate"
    (is (v/disjoint? kb 'unary_predicate 'binary_predicate))
    (is (v/disjoint? kb 'unary_predicate 'ternary_predicate))
    (is (v/disjoint? kb 'binary_predicate 'ternary_predicate))
    (is (not (v/disjoint? kb 'binary_predicate 'instance_relation_predicate))
        "arity is both, so a sibling_disjoint mark on predicate would be too wide"))
  (testing "and the second classification is a clash, in either order"
    (tu/with-terms [zebraOf yakOf]
      (v/assert kb (list 'unary_predicate zebraOf) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'binary_predicate zebraOf) 'CxUniverse))
      (v/assert kb (list 'binary_predicate yakOf) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'unary_predicate yakOf) 'CxUniverse))))
  (testing "a mark below binary_predicate carries the separation with it"
    (tu/with-terms [emuOf]
      (v/assert kb (list 'functional emuOf) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'ternary_predicate emuOf) 'CxUniverse))))
  (testing "belief-filtered: retracting the first frees the second"
    (tu/with-terms [oxOf]
      (let [h (v/assert kb (list 'unary_predicate oxOf) 'CxUniverse)]
        (is (tu/stored-in-clash? kb (list 'ternary_predicate oxOf) 'CxUniverse))
        (v/retract! kb h)
        (is (v/ask? kb (list 'ternary_predicate oxOf) 'CxUniverse))
        (is (not-any? #(some #{(v/handle-of kb (list 'ternary_predicate oxOf) 'CxUniverse)}
                             (:nogood %))
                      (concat (v/contradictions kb) (v/conflicts kb)))))))
  (testing "and scoped: two contexts neither of which sees the other keep both"
    (tu/with-terms [ibisOf CxLeft CxRight CxBelowLeft]
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBelowLeft CxLeft) 'CxUniverse)
      (v/assert kb (list 'unary_predicate ibisOf) CxLeft)
      (is (v/assert kb (list 'binary_predicate ibisOf) CxRight)
          "neither context sees the other, so both classifications stand")
      (is (tu/stored-in-clash? kb (list 'ternary_predicate ibisOf) CxBelowLeft)
          "the descendant sees the first classification, so the third clashes with it"))))

(tu/deftest-kb a-social-agent-is-a-person-but-not-a-mammal
  ;; the entailing reading: the derivation is the subject
  (tu/with-entailing
    ;; The person/human split (#11): `human` is the biological type — a mammal — while
    ;; `person` is the broad class of anything with social agency.  A non-biological agent
    ;; is a person by the genl edge to `person`, and inherits none of the biology, so the
    ;; social predicates constrain their arguments to `person` and still admit it.
    (tu/with-terms [sentientAndroid CmdrData Geordi]
      (v/assert kb (list 'genl sentientAndroid 'person) N)
      (v/assert kb (list sentientAndroid CmdrData) N)
      (v/assert kb (list 'person Geordi) N)
      (testing "the android is a person by the edge to the broad class"
        (is (v/isa? kb CmdrData 'person))
        (is (v/ask? kb (list 'person CmdrData) N)))
      (testing "but not a mammal or an animal — person implies neither any more"
        (is (not (v/isa? kb CmdrData 'mammal)))
        (is (not (v/isa? kb CmdrData 'animal)))
        (is (not (v/ask? kb (list 'mammal CmdrData) N))))
      (testing "so a social relation type-checks between two persons"
        (is (v/assert kb (list 'friendOf CmdrData Geordi) N))
        (is (v/ask? kb (list 'friendOf CmdrData Geordi) N)))
      (testing "while a biological predicate derives organism of the person it is told of"
        (is (v/assert kb (list 'parentOf CmdrData Geordi) N))
        (is (v/isa? kb CmdrData 'organism N)))
      (testing "and human, the biological half, reaches mammal, animal and person alike"
        (is (v/genl? kb 'human 'mammal))
        (is (v/genl? kb 'human 'animal))
        (is (v/genl? kb 'human 'person))
        (is (not (v/genl? kb 'person 'mammal)))))))

(tu/deftest-kb the-types-added-for-argument-constraints-are-placed-where-they-are-used
  (testing "the two calculi types the argument declarations name"
    (is (v/genl? kb 'tangible 'spatial))
    (is (v/genl? kb 'time_point 'temporal)))
  (testing "and an animal reaches spatial, so a spatial relation admits one"
    (is (v/genl? kb 'dog 'spatial))))

(defn- refusal
  "The `:type` of the ex-info `assert` throws for `sentence`, or `:stored` when it takes
  it (and then retracts it again, so the probe leaves nothing behind)."
  [kb sentence context]
  (try (some->> (v/assert kb sentence context) (v/retract! kb)) :stored
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-time-is-in-time-and-in-no-space-and-causes-nothing
  ;; A date cannot be a cause: the year 2000 broke nothing — two-digit years did, at the
  ;; rollover.  `time` is temporal, aspatial and acausal, and time_point and time_interval
  ;; partition it, so a moment and a stretch are all three and never each other.  A
  ;; calendar term is never minted, so its result type is read where it is checked: an
  ;; argument typed with a kind no result type reaches refuses it, one it reaches admits it.
  (testing "both parts reach time, and time_point still reaches temporal through it"
    (is (v/genl? kb 'time_point 'time N))
    (is (v/genl? kb 'time_interval 'time N))
    (is (v/genl? kb 'time_point 'temporal N)))
  (testing "an instant is not a stretch, and neither is something that happens in time"
    (is (v/disjoint? kb 'time_point 'time_interval N))
    (is (v/disjoint? kb 'time_interval 'event N)))
  (testing "and the collector relates a stretch to the dimension it is measured in"
    (is (v/ask? kb '(termsRelated time_interval Duration) 'CxUniverse)))
  (tu/with-terms [acausalProbe aspatialProbe temporalProbe momentProbe]
    (doseq [[p t] [[acausalProbe 'acausal] [aspatialProbe 'aspatial] [temporalProbe 'temporal]
                   [momentProbe 'time_point]]]
      (v/assert kb (list 'unary_predicate p) 'CxUniverse)
      (v/assert kb (list 'arg p 1 t) 'CxUniverse))
    (testing "the year 2000, a month and a day read acausal"
      (is (= :stored (refusal kb (list acausalProbe '(YearFn 2000)) N)))
      (is (= :stored (refusal kb (list acausalProbe '(MonthFn 2000 1)) N)))
      (is (= :stored (refusal kb (list acausalProbe '(DayFn 2000 1 15)) N))))
    (testing "the year 2000 spelled as an ISO string reads acausal, and is no moment"
      (is (= :stored (refusal kb (list acausalProbe '(DatetimeFn "2000")) N)))
      (is (= :stored (refusal kb (list acausalProbe '(DatetimeFn "2000-01-15T13")) N)))
      (is (not= :stored (refusal kb (list momentProbe '(DatetimeFn "2000")) N))))
    (testing "the year 2000 reads aspatial and temporal"
      (is (= :stored (refusal kb (list aspatialProbe '(YearFn 2000)) N)))
      (is (= :stored (refusal kb (list temporalProbe '(YearFn 2000)) N))))
    (testing "the moment the year starts reads acausal and aspatial too"
      (is (= :stored (refusal kb (list acausalProbe '(StartFn (YearFn 2000))) N)))
      (is (= :stored (refusal kb (list aspatialProbe '(StartFn (YearFn 2000))) N))))))

(def ^:private cxtime-calendar-facts
  "Facts CxTime states over calendar terms and moments: a stretch contains a stretch, a
  stretch contains a moment, and a calendar moment equals a moment spelled with
  InstantFn."
  '[(contains (YearFn 2000) (MonthFn 2000 1))
    (contains (DatetimeFn "2000") (DatetimeFn "2000-01"))
    (contains (YearFn 2000) (InstantFn 2000 3 1 0 0 0))
    (instantEqual (StartFn (YearFn 2000)) (InstantFn 2000 1 1 0 0 0))])

(tu/deftest-kb a-band-context-reads-the-time-partition-without-cxabstract
  ;; CxTime types its calendar results time_interval and its moments time_point, and does
  ;; not see CxAbstract, so CxCore holds time's edges to temporal and aspatial and the
  ;; partition.  The partition derives each part's edge to time, so CxCore states none.
  (testing "in CxTime a moment and a stretch are temporal, aspatial and never each other"
    (doseq [t '[time_point time_interval]
            up '[time temporal aspatial]]
      (is (true? (v/genl? kb t up 'CxTime)) (str t " must reach " up " in CxTime")))
    (is (true? (v/disjoint? kb 'time_point 'time_interval 'CxTime))))
  (testing "CxCore states no edge the partition derives"
    (let [stated (set (map (comp first text/peel-strength)
                           (text/read-forms (io/file "resources/kb/CxCore.txt"))))]
      (doseq [s '[(genl time_point temporal) (genl time_point time) (genl time_interval time)]]
        (is (not (contains? stated s)) (str (pr-str s) " is derived from the partition")))))
  (testing "CxTime stores its calendar facts under both argument-type readings"
    (doseq [s cxtime-calendar-facts]
      (is (= :stored (tu/with-entailing (refusal kb s 'CxTime))) (pr-str s))
      (is (= :stored (tu/without-entailing (refusal kb s 'CxTime))) (pr-str s)))))

;; ---- the upper divisions by location and by mass --------------------------
;; Two partitions of `thing`.  `spatial` / `aspatial` divides by a location in SOME space —
;; physical space, or a mathematical one, where a line or a square of an abstract board
;; has a location and none in the world.  `tangible` / `intangible` divides by mass.
;; `spatiotemporal` is below `spatial` and `temporal`: what has a location in space and
;; time.  CxCore states the two edges as `genl` edges and not as an intersection, so a
;; thing stated spatial and temporal is not concluded spatiotemporal; `nowhere_never` is
;; placed below `aspatial` and `atemporal` the same way.  The spatial calculi relate
;; anything spatial.  A region is the case the two partitions cross on: spatiotemporal,
;; and massless.

(tu/deftest-kb spatiotemporal-is-below-spatial-and-temporal
  (testing "the kind is below each of the two types"
    (is (true? (v/genl? kb 'spatiotemporal 'spatial)))
    (is (true? (v/genl? kb 'spatiotemporal 'temporal))))
  (testing "something spatial and temporal is not concluded spatiotemporal"
    (tu/with-terms [Puddle]
      (v/assert kb (list 'spatial Puddle) 'CxUniverse)
      (v/assert kb (list 'temporal Puddle) 'CxUniverse)
      (is (empty? (v/sentexes-matching kb (list 'spatiotemporal Puddle) 'CxUniverse))))))

(tu/deftest-kb a-tangible-thing-is-spatiotemporal-and-so-spatial-and-temporal
  (testing "the type reaches all three"
    (is (true? (v/genl? kb 'tangible 'spatiotemporal)))
    (is (true? (v/genl? kb 'tangible 'spatial)))
    (is (true? (v/genl? kb 'tangible 'temporal))))
  (testing "and an instance carries the memberships"
    (tu/with-terms [Pebble]
      (v/assert kb (list 'tangible Pebble) 'CxUniverse)
      (is (true? (v/ask? kb (list 'spatiotemporal Pebble) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'spatial Pebble) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'temporal Pebble) 'CxUniverse))))))

(tu/deftest-kb an-abstract-figure-is-spatial-without-being-spatiotemporal
  ;; A line in a plane has a location in that plane and none in the world, no mass,
  ;; and no place in time.
  (tu/with-terms [Diagonal]
    (v/assert kb (list 'spatial Diagonal) 'CxUniverse)
    (v/assert kb (list 'atemporal Diagonal) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'intangible Diagonal) 'CxUniverse))
        "spatial and intangible together are consistent")
    (is (true? (v/ask? kb (list 'spatial Diagonal) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'intangible Diagonal) 'CxUniverse)))
    (is (not (v/ask? kb (list 'spatiotemporal Diagonal) 'CxUniverse))
        "it is not located in space and time")))

(tu/deftest-kb nowhere-never-is-below-aspatial-and-atemporal
  (testing "the kind is below each of the two types, and massless"
    (is (true? (v/genl? kb 'nowhere_never 'aspatial)))
    (is (true? (v/genl? kb 'nowhere_never 'atemporal)))
    (is (true? (v/genl? kb 'nowhere_never 'intangible))))
  (testing "an expression and a language are nowhere and never"
    (is (true? (v/genl? kb 'expression 'nowhere_never)))
    (is (true? (v/genl? kb 'language 'nowhere_never)))
    (tu/with-terms [Formula]
      (v/assert kb (list 'expression Formula) 'CxUniverse)
      (is (true? (v/ask? kb (list 'nowhere_never Formula) 'CxUniverse)))))
  (testing "something aspatial and atemporal is not concluded nowhere_never"
    (tu/with-terms [Platitude]
      (v/assert kb (list 'aspatial Platitude) 'CxUniverse)
      (v/assert kb (list 'atemporal Platitude) 'CxUniverse)
      (is (empty? (v/sentexes-matching kb (list 'nowhere_never Platitude) 'CxUniverse)))))
  (testing "a line in the plane is atemporal and spatial, so it is not"
    (tu/with-terms [Bisector]
      (v/assert kb (list 'spatial Bisector) 'CxUniverse)
      (v/assert kb (list 'atemporal Bisector) 'CxUniverse)
      (is (not (v/ask? kb (list 'nowhere_never Bisector) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'nowhere_never Bisector) 'CxUniverse))))))

(tu/deftest-kb spatial-and-aspatial-partition-thing
  (is (true? (v/disjoint? kb 'spatial 'aspatial)))
  (is (true? (v/disjoint? kb 'spatiotemporal 'aspatial))
      "the partition separates spatiotemporal from aspatial through the genl to spatial")
  (is (true? (v/genl? kb 'spatial 'thing)))
  (is (true? (v/genl? kb 'aspatial 'thing)))
  (testing "a thing cannot be both"
    (tu/with-terms [Figment]
      (v/assert kb (list 'spatial Figment) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'aspatial Figment) 'CxUniverse)))))
  (testing "and a thing denied a location in any space is aspatial — the coverage half"
    (tu/with-terms [Rumour]
      (v/assert kb (list 'thing Rumour) 'CxUniverse)
      (v/assert kb (list 'not (list 'spatial Rumour)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'aspatial Rumour) 'CxUniverse))))))

(tu/deftest-kb temporal-and-atemporal-partition-thing
  (is (true? (v/disjoint? kb 'temporal 'atemporal)))
  (testing "a thing cannot be both"
    (tu/with-terms [Moment]
      (v/assert kb (list 'temporal Moment) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'atemporal Moment) 'CxUniverse)))))
  (testing "and a thing denied a place in time is atemporal — the coverage half"
    (tu/with-terms [Theorem]
      (v/assert kb (list 'thing Theorem) 'CxUniverse)
      (v/assert kb (list 'not (list 'temporal Theorem)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'atemporal Theorem) 'CxUniverse))))))

(tu/deftest-kb tangible-and-intangible-partition-thing
  (is (true? (v/disjoint? kb 'tangible 'intangible)))
  (is (true? (v/genl? kb 'tangible 'thing)))
  (is (true? (v/genl? kb 'intangible 'thing)))
  (testing "a thing cannot be both"
    (tu/with-terms [Boulder]
      (v/assert kb (list 'tangible Boulder) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'intangible Boulder) 'CxUniverse)))))
  (testing "and a thing denied mass is intangible — the coverage half"
    (tu/with-terms [Echo]
      (v/assert kb (list 'thing Echo) 'CxUniverse)
      (v/assert kb (list 'not (list 'tangible Echo)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'intangible Echo) 'CxUniverse))))))

;; ---- the kinds of relation ----------------------------------------------
;; (partition relation function truth_valued_relation), (partition truth_valued_relation
;; logical_constant predicate) and (partition logical_constant quantifier
;; logical_connective), after Cyc's TruthFunction: an application of a relation denotes a
;; value or is true or false, and what is true or false is a predicate's application or a
;; logical constant's.

(tu/deftest-kb three-partitions-divide-relation
  (testing "each part reaches relation and the root"
    (doseq [t '[function truth_valued_relation predicate logical_constant quantifier
                logical_connective]]
      (is (true? (v/genl? kb t 'relation)) (str t " must reach relation"))
      (is (true? (v/genl? kb t 'thing)) (str t " must reach thing"))))
  (testing "predicate and the logical constants are truth-valued relations"
    (doseq [t '[predicate logical_constant quantifier logical_connective]]
      (is (true? (v/genl? kb t 'truth_valued_relation))
          (str t " must be under truth_valued_relation"))))
  (testing "quantifier and logical_connective are logical constants"
    (doseq [t '[quantifier logical_connective]]
      (is (true? (v/genl? kb t 'logical_constant)) (str t " must be under logical_constant"))))
  (testing "the parts of each partition are disjoint, and the separation descends"
    (doseq [[a b] '[[function truth_valued_relation] [logical_constant predicate]
                    [quantifier logical_connective]
                    [predicate function] [logical_connective function] [quantifier function]
                    [logical_connective predicate] [quantifier predicate]]]
      (is (true? (v/disjoint? kb a b)) (str a " and " b " must be disjoint")))))

(tu/deftest-kb what-the-partitions-entail-is-derived-and-not-stated
  ;; Each of these was stated in CxCore before the partitions, and each is entailed by
  ;; them: a part of a partition is under its whole, and the parts are disjoint, which
  ;; descends to predicate through truth_valued_relation.  A fact entailed by a stated
  ;; fact is not stated as well, so CxCore carries none of the three.
  (let [stated (set (map (comp first text/peel-strength)
                         (text/read-forms (io/file "resources/kb/CxCore.txt"))))]
    (doseq [s '[(genl function relation) (genl predicate relation)
                (disjoint function predicate) (disjoint predicate function)]]
      (is (not (contains? stated s)) (str (pr-str s) " is entailed by the partitions"))))
  (is (true? (v/genl? kb 'function 'relation)))
  (is (true? (v/genl? kb 'predicate 'relation)))
  (is (true? (v/disjoint? kb 'function 'predicate)))
  (is (true? (v/disjoint? kb 'predicate 'function))))

(tu/deftest-kb the-connectives-are-logical-connectives-and-not-predicates
  (doseq [c '[and or not implies]]
    (is (true? (v/isa? kb c 'logical_connective)) (str c " must be a logical_connective"))
    (is (true? (v/isa? kb c 'truth_valued_relation)) (str c " must be a truth_valued_relation"))
    (is (not (v/isa? kb c 'predicate)) (str c " must not be a predicate")))
  (testing "neither connective keeps its old predicate arity class"
    (is (not (v/isa? kb 'not 'unary_predicate)))
    (is (not (v/isa? kb 'implies 'binary_predicate))))
  (testing "and each states its arity with the relation-wide vocabulary"
    (is (true? (v/isa? kb 'not 'unary)))
    (is (true? (v/isa? kb 'implies 'binary)))
    (is (true? (v/isa? kb 'and 'variable_arity)))
    (is (true? (v/isa? kb 'or 'variable_arity))))
  (testing "and so neither is a type the not-under-thing sweep asks to place"
    (is (nil? (:not-under-thing (v/kb-integrity kb #{'not 'implies} 'CxWell))))))

(tu/deftest-kb the-quantifiers-are-quantifiers-and-not-connectives
  ;; OE 6: forall, thereExists and exists are declared quantifier instances in CxCore —
  ;; where the engine reads each as a query operator or rule-firing sugar rather than as
  ;; a predicate with its own facts (forall desugars to a nested unknown, docs/naf.md;
  ;; thereExists is the query existential, docs/naf.md; exists is a head existential
  ;; forward firing skolemizes, docs/skolem.md).
  (doseq [q '[forall thereExists exists]]
    (is (true? (v/isa? kb q 'quantifier)) (str q " must be a quantifier"))
    (is (true? (v/isa? kb q 'logical_constant)) (str q " must be a logical_constant"))
    (is (not (v/isa? kb q 'logical_connective)) (str q " must not be a logical_connective")))
  (testing "and is a logical_connective, not a quantifier"
    (is (v/ask? kb (list 'not (list 'quantifier 'and)) 'CxUniverse)))
  (testing "an ordinary term is neither"
    (is (v/ask? kb (list 'not (list 'quantifier 'Muffet)) 'CxUniverse)))
  (testing "forall is not a logical_connective"
    (is (v/ask? kb (list 'not (list 'logical_connective 'forall)) 'CxUniverse)))
  (testing "sign_value is closed-extent too (CxMeasure, beside its three instances)"
    (is (v/ask? kb (list 'not (list 'sign_value 'Muffet)) 'CxUniverse))))

(tu/deftest-kb what-has-no-place-in-space-or-time-has-no-mass
  ;; Mass entails a location in space and time, so what lacks either lacks mass.
  (is (true? (v/genl? kb 'aspatial 'intangible)))
  (is (true? (v/genl? kb 'atemporal 'intangible)))
  (tu/with-terms [Prime]
    (v/assert kb (list 'atemporal Prime) 'CxUniverse)
    (is (true? (v/ask? kb (list 'intangible Prime) 'CxUniverse)))
    (is (true? (tu/stored-in-clash? kb (list 'tangible Prime) 'CxUniverse)))))

(def ^:private aspatial-kinds
  "The kinds with no location in any space, each with the contexts that read it as
  aspatial.  `context` and `language` are read from two band contexts besides CxCore,
  which see CxCore's `expression` lattice and `language` edge."
  '{quantity      [CxMeasure]
    fluent        [CxTime]
    organization  [CxCore CxSociety]
    context       [CxCore CxSpace CxSociety]
    language      [CxCore CxSpace CxSociety]})

(tu/deftest-kb a-kind-with-no-location-in-any-space-is-disjoint-from-spatial
  (doseq [[kind ctxs] aspatial-kinds
          ctx         (conj ctxs 'CxUniverse)
          located     '[spatial spatiotemporal]]
    (is (true? (v/disjoint? kb kind located ctx)) (str kind " and " located " in " ctx)))
  (testing "a spatial relation between a fluent and an organization derives two clashes"
    ;; Pinned to the entailing reading: the clash sides are the minted (spatial X), and
    ;; the constraint-only reading refuses the northOf instead.
    (tu/with-entailing
      (tu/with-terms [LampLit AcmeCo]
        (v/assert kb (list 'fluent LampLit) 'CxUniverse)
        (v/assert kb (list 'organization AcmeCo) 'CxUniverse)
        (v/assert kb (list 'northOf LampLit AcmeCo) 'CxUniverse)
        (let [clashes (into #{} (comp (filter #(= :disjoint (:kind %)))
                                      (map #(into #{} (map :sentence) (:sides %))))
                            (v/contradictions kb))]
          (is (contains? clashes #{(list 'fluent LampLit) (list 'spatial LampLit)}))
          (is (contains? clashes #{(list 'organization AcmeCo) (list 'spatial AcmeCo)}))))))
  (testing "and a dog stays disjoint from a number and a relation"
    (is (true? (v/disjoint? kb 'dog 'number)))
    (is (true? (v/disjoint? kb 'dog 'relation)))))

(tu/deftest-kb a-region-is-spatiotemporal-and-intangible-at-once
  ;; A region of space has a location and no mass.  Nothing separates intangible from
  ;; spatial or from spatiotemporal, so the pair is consistent.
  (is (not (v/disjoint? kb 'intangible 'spatiotemporal)))
  (is (not (v/disjoint? kb 'intangible 'spatial)))
  (tu/with-terms [Meadow]
    (v/assert kb (list 'spatiotemporal Meadow) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'intangible Meadow) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'intangible Meadow) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'spatial Meadow) 'CxUniverse)))
    (is (not (v/ask? kb (list 'tangible Meadow) 'CxUniverse)))))

(tu/deftest-kb a-partition-is-stated-a-cover-and-a-separation
  ;; Every partition is a cover and a separation, so CxCore says so with two sub-relation
  ;; edges.  What they add is a query for the weaker spelling answering the stronger one,
  ;; and nothing the other way.
  (doseq [super '[covering separating]]
    (is (true? (v/ask? kb (list 'genl 'partition super) 'CxUniverse))
        (str "(genl partition " super ") is believed"))
    (is (true? (v/genl? kb 'partition super))))
  (tu/with-terms [whole_kind part_a part_b part_c Item]
    (v/assert kb (list 'partition whole_kind part_a part_b) 'CxUniverse)
    (testing "a partition answers a covering query and a separating query"
      (is (true? (v/ask? kb (list 'covering whole_kind part_a part_b) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'separating whole_kind part_a part_b) 'CxUniverse))))
    (testing "and a cover is not read as a partition"
      (v/assert kb (list 'covering whole_kind part_a part_c) 'CxUniverse)
      (is (not (v/ask? kb (list 'partition whole_kind part_a part_c) 'CxUniverse))))
    (testing "the coverage inference reads the partition as it did before"
      (v/assert kb (list whole_kind Item) 'CxUniverse)
      (v/assert kb (list 'not (list part_a Item)) 'CxUniverse)
      (is (true? (v/ask? kb (list part_b Item) 'CxUniverse))))))

(def ^:private derivable-and-unstated
  "Relations the shipped KB holds without stating them, each with the context that held
  the sentence before it was removed and the route it is derived by instead.  A
  partition installs a genl edge from each part to the whole and separates the parts,
  an intersection installs an edge to each of its types, genl is transitive, and a
  disjointness descends a genl edge — so a stated sentence repeating one of those is not
  written."
  '[[genl aspatial thing CxCore "partition thing spatial aspatial"]
    [disjoint spatiotemporal aspatial CxCore "spatiotemporal genl spatial; partition thing spatial aspatial"]
    [genl intangible thing CxCore "partition thing tangible intangible"]
    [genl nowhere_never intangible CxCore "nowhere_never genl aspatial genl intangible"]
    [genl organization intangible CxCore "organization genl aspatial genl intangible"]
    [genl context intangible CxCore "context genl nowhere_never genl aspatial genl intangible"]
    [genl language intangible CxCore "language genl nowhere_never genl aspatial genl intangible"]
    [genl number thing CxCore "number genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl keyword thing CxCore "keyword genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl boolean thing CxCore "boolean genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl character thing CxCore "character genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl denotational_term thing CxReflection "denotational_term genl closed_expression genl expression genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl formula thing CxCore "formula genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl quantity intangible CxMeasure "quantity genl aspatial genl intangible"]
    [genl fluent intangible CxTime "fluent genl aspatial genl intangible"]
    [genl temporal thing CxCore "partition thing temporal atemporal"]
    [genl atemporal thing CxCore "partition thing temporal atemporal"]
    [disjoint temporal atemporal CxCore "partition thing temporal atemporal"]
    [genl spatiotemporal thing CxCore "spatiotemporal genl spatial, spatial genl thing (partition)"]
    [genl organism tangible CxCore "organism genl biological genl tangible"]
    [genl body_part tangible CxAbstract "body_part genl biological genl tangible"]
    [genl body_part biological CxAbstract "separating biological organism body_part"]
    [disjoint organism substance CxAbstract "organism genl biological; disjoint biological substance"]
    [disjoint substance body_part CxAbstract "body_part genl biological; disjoint biological substance"]
    [genl tangible temporal CxAbstract "tangible genl spatiotemporal genl temporal"]
    [disjoint tangible intangible CxAbstract "partition thing tangible intangible"]
    [disjoint organization substance CxAbstract "organization genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint language substance CxAbstract "language genl nowhere_never genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint organization animal CxUniverse "organization genl aspatial genl intangible, animal genl organism genl biological genl tangible; partition thing tangible intangible"]
    [genl string intangible CxAbstract "string genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl number intangible CxAbstract "number genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl keyword intangible CxAbstract "keyword genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl boolean intangible CxAbstract "boolean genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl character intangible CxAbstract "character genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl building made CxAbstract "building genl container genl made"]
    [genl made tangible CxAbstract "partition tangible made natural"]
    [genl natural tangible CxAbstract "partition tangible made natural"]
    [genl formation tangible CxAbstract "formation genl natural genl tangible"]
    [disjoint formation made CxAbstract "formation genl natural; partition tangible made natural"]
    [disjoint formation organism CxAbstract "organism genl biological; separating tangible formation biological"]
    [disjoint formation body_part CxAbstract "body_part genl biological; separating tangible formation biological"]
    [genl asymmetric binary_predicate CxCore "asymmetric genl anti_symmetric genl binary_predicate"]
    [disjoint string predicate CxAbstract "string genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint number predicate CxAbstract "number genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint keyword predicate CxAbstract "keyword genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint boolean predicate CxAbstract "boolean genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint character predicate CxAbstract "character genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint glass_stuff stone CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal glass_stuff CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal stone CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal wood CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint wood glass_stuff CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint wood stone CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [genl reifiable_function function CxCore "partition function reifiable_function unreifiable_function"]
    [genl unreifiable_function function CxCore "partition function reifiable_function unreifiable_function"]
    [genl fixed_order_type unary_predicate CxCore "partition unary_predicate fixed_order_type variable_order_type"]
    [genl variable_order_type unary_predicate CxCore "partition unary_predicate fixed_order_type variable_order_type"]
    [genl equivalence_relation binary_predicate CxCore "intersection equivalence_relation reflexive symmetric transitive; reflexive genl binary_predicate"]
    [genl linguistic nowhere_never CxCore "separating nowhere_never logical linguistic quantitative"]
    [genl relation nowhere_never CxCore "separating logical relation context; separating nowhere_never logical linguistic quantitative"]
    [genl context nowhere_never CxCore "separating logical relation context; separating nowhere_never logical linguistic quantitative"]
    [genl measure nowhere_never CxCore "measure genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [disjoint linguistic relation CxCore "relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint linguistic measure CxCore "measure genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [disjoint measure relation CxCore "measure genl quantitative, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint relation context CxAbstract "separating logical relation context"]
    [genl unit_of_measure nowhere_never CxMeasure "unit_of_measure genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [genl physical_dimension nowhere_never CxMeasure "physical_dimension genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [genl sign_value nowhere_never CxMeasure "sign_value genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [disjoint unit_of_measure relation CxMeasure "unit_of_measure genl quantitative, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint physical_dimension relation CxMeasure "physical_dimension genl quantitative, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [genl proposition nowhere_never CxReflection "separating logical relation proposition context; separating nowhere_never logical linguistic quantitative"]
    [disjoint proposition linguistic CxReflection "proposition genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint proposition relation CxReflection "separating logical relation proposition context"]
    [disjoint expression relation CxReflection "expression genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint expression context CxReflection "expression genl linguistic, context genl logical; separating nowhere_never logical linguistic quantitative"]])

(tu/deftest-kb the-kb-states-no-relation-it-already-derives
  ;; Each relation is read from the context that held the removed sentence, so a removal
  ;; that left a context unable to see the route would fail here.
  (doseq [[pred a b ctx route] derivable-and-unstated]
    (is (true? (if (= 'genl pred) (v/genl? kb a b ctx) (v/disjoint? kb a b ctx)))
        (str "(" pred " " a " " b ") holds in " ctx " by " route))
    ;; stated means a premise: a derived copy is the KB deriving it, which is the point
    (is (not-any? #(v/premise? kb (:id %)) (v/sentexes-matching kb (list pred a b) '?ctx))
        (str "and (" pred " " a " " b ") is not stated"))))

;; ---- the literal types: one vocabulary, and one exception ----------------
;; `string` / `number` / `integer` / `symbol` are the KB's only names for text, numbers
;; and names, and both argument declarations read the same four (docs/argtypes.md).  The
;; distinction between them is carried by *which predicate you write* — `arg` types what
;; an argument denotes, `quotedArg` the term written there — so a second set of type
;; names would be redundancy plus a trap, a `quotedArg` outside the syntactic lattice
;; convicting nothing for the life of the KB.  These pin the modelling half of that: the
;; placement, the two disjointness claims, and the one type the pattern does not reach.

(tu/deftest-kb the-value-kinds-are-placed-in-the-domain-lattice
  (testing "text and a number have no mass and no location"
    (is (v/genl? kb 'string 'intangible))
    (is (v/genl? kb 'number 'intangible)))
  (testing "integer reaches intangible through number, carrying no edge of its own"
    (is (v/genl? kb 'integer 'number))
    (is (v/genl? kb 'integer 'intangible))
    (is (empty? (v/sentexes-matching kb '(genl integer intangible) 'CxUniverse))
        "the reach is transitive: no second parent is asserted for it"))
  (testing "and neither of them is a relation"
    (is (v/disjoint? kb 'string 'predicate))
    (is (v/disjoint? kb 'number 'predicate))
    (is (v/disjoint? kb 'integer 'predicate)
        "the declaration on number carries integer with it")))

(tu/deftest-kb symbol-is-mention-only-and-is-disjoint-from-predicate
  ;; a symbol does not denote itself, so the set of names and the set of things named are
  ;; two sets — parentOf is written as a symbol and denotes a predicate.  symbol reaches
  ;; expression through atomic_term and atomic_expression, and expression is disjoint
  ;; from relation, so from predicate: a symbol is what (Quote parentOf) denotes, not
  ;; what parentOf denotes.
  (is (true? (v/disjoint? kb 'symbol 'predicate))
      "a symbol is what (Quote dog) denotes, not what dog denotes")
  (is (true? (v/genl? kb 'symbol 'linguistic))
      "and a symbol is a written form: linguistic, so nowhere_never"))

(tu/deftest-kb the-comment-text-position-derives-a-string-and-a-relation-clashes
  ;; the entailing reading: the derivation is the subject
  (tu/with-entailing
    ;; `(arg comment 2 string)` at the ground level derives `string` of a symbol in the text
    ;; position, as every argument constraint derives under the entailing reading.  A term
    ;; the KB holds as a relation then stands in the clash `(disjoint string relation)`
    ;; makes, and a string value is what the position is for.
    (tu/with-terms [SomeDoc]
      (testing "a predicate in the text position derives a string membership, in a clash"
        (is (= [] (v/check kb (list 'comment 'thing 'genl) 'CxUniverse)))
        (v/assert kb (list 'comment 'thing 'genl) 'CxUniverse)
        (is (tu/stored-in-clash? kb (list 'string 'genl) 'CxUniverse)))
      (testing "an unclassified name is admitted"
        (is (= [] (v/check kb (list 'comment 'thing SomeDoc) 'CxUniverse))))
      (testing "and a string value is what the position is for"
        (is (= [] (v/check kb (list 'comment 'thing "some text") 'CxUniverse)))))))

(tu/deftest-kb a-term-cannot-be-both-a-string-and-a-relation
  (tu/with-terms [Thing1]
    (v/assert kb (list 'string Thing1) 'CxUniverse)
    (is (tu/stored-in-clash? kb (list 'predicate Thing1) 'CxUniverse))))

;; ---- what is biological ---------------------------------------------------
;; An organism and a part it grew are both biological, and tangible through it.  The two
;; are separated without being said to exhaust biological.

(tu/deftest-kb an-organism-and-a-body-part-are-biological-and-tangible
  (doseq [t '[organism body_part]]
    (is (true? (v/genl? kb t 'biological)) (str t " is biological"))
    (is (true? (v/genl? kb t 'tangible)) (str t " is tangible through biological")))
  (is (true? (v/genl? kb 'biological 'tangible)))
  (testing "a kind CxOrganism places reaches tangible from CxOrganism itself"
    (is (true? (v/genl? kb 'animal 'tangible 'CxOrganism))))
  (tu/with-terms [Gizzard]
    (v/assert kb (list 'body_part Gizzard) 'CxUniverse)
    (is (true? (v/ask? kb (list 'biological Gizzard) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'tangible Gizzard) 'CxUniverse)))))

(tu/deftest-kb a-biological-thing-is-not-a-substance
  ;; Stated once, of biological and substance, and read down to both of biological's
  ;; parts: neither an organism nor a part it grew is stuff.
  (is (true? (v/disjoint? kb 'biological 'substance)))
  (testing "the separation reaches organism and body_part, which state none of their own"
    (is (true? (v/disjoint? kb 'organism 'substance)))
    (is (true? (v/disjoint? kb 'body_part 'substance)))
    (is (true? (v/disjoint? kb 'leaf 'wood)) "and the kinds below each"))
  (tu/with-terms [Gristle]
    (v/assert kb (list 'biological Gristle) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'substance Gristle) 'CxUniverse))
        "a biological thing that is also a substance is a clash")))

(tu/deftest-kb an-organism-is-not-a-body-part
  (is (true? (v/disjoint? kb 'organism 'body_part)))
  (is (true? (v/disjoint? kb 'animal 'feather))
      "the separation reaches the kinds below each part")
  (tu/with-terms [Polyp]
    (v/assert kb (list 'organism Polyp) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'body_part Polyp) 'CxUniverse))))
  (testing "and nothing says a biological thing is one or the other"
    (tu/with-terms [Spore]
      (v/assert kb (list 'biological Spore) 'CxUniverse)
      (v/assert kb (list 'not (list 'organism Spore)) 'CxUniverse)
      (is (not (v/ask? kb (list 'body_part Spore) 'CxUniverse))))))

(tu/deftest-kb a-body-part-can-be-food
  ;; A leg of lamb or a chicken wing is both, so the pair is declared orthogonal rather
  ;; than disjoint.
  (is (not (v/disjoint? kb 'food 'body_part)))
  (tu/with-terms [Drumstick]
    (v/assert kb (list 'body_part Drumstick) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'food Drumstick) 'CxUniverse))
        "a body part that is also food is no clash")
    (is (true? (v/ask? kb (list 'food Drumstick) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'body_part Drumstick) 'CxUniverse)))))

(tu/deftest-kb an-organism-or-a-body-part-can-be-made
  ;; Something made can be biological too: an engineered bacterium, an organ grown in a
  ;; lab, a cloned sheep.  The pair is declared orthogonal rather than disjoint.
  (is (not (v/disjoint? kb 'biological 'made)))
  (is (not (v/disjoint? kb 'organism 'made)))
  (is (not (v/disjoint? kb 'body_part 'made)))
  (tu/with-terms [Engineered LabKidney]
    (v/assert kb (list 'organism Engineered) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'made Engineered) 'CxUniverse))
        "an organism that is also made is no clash")
    (is (true? (v/ask? kb (list 'made Engineered) 'CxUniverse)))
    (v/assert kb (list 'body_part LabKidney) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'made LabKidney) 'CxUniverse))
        "a body part that is also made is no clash"))
  (testing "while a biological thing stays apart from a substance"
    (is (true? (v/disjoint? kb 'organism 'substance)))
    (is (true? (v/disjoint? kb 'body_part 'substance)))))

;; ---- the relation vocabulary: what divides a relation ---------------------
;; A relation is a function or a truth_valued_relation, a function is reifiable or not,
;; and a unary_predicate is of one fixed order or of variable order.  Each is a partition, so
;; the parts are separated and cover their whole: a member denied every part but one is
;; concluded the last.

(tu/deftest-kb a-relation-that-is-not-truth-valued-is-a-function
  ;; The coverage half of (partition relation function truth_valued_relation);
  ;; three-partitions-divide-relation pins the separation half.
  (tu/with-terms [relatesTo]
    (v/assert kb (list 'relation relatesTo) 'CxUniverse)
    (v/assert kb (list 'not (list 'truth_valued_relation relatesTo)) 'CxUniverse)
    (is (true? (v/ask? kb (list 'function relatesTo) 'CxUniverse)))))

(tu/deftest-kb reifiable-and-unreifiable-partition-function
  (is (true? (v/disjoint? kb 'reifiable_function 'unreifiable_function 'CxCore)))
  (is (true? (v/genl? kb 'reifiable_function 'function 'CxCore)))
  (is (true? (v/genl? kb 'unreifiable_function 'function 'CxCore)))
  (testing "the separation is not quoting_function's: that mark crosses both parts"
    (is (not (v/disjoint? kb 'quoting_function 'reifiable_function)))
    (is (not (v/disjoint? kb 'quoting_function 'unreifiable_function)))))

(tu/deftest-kb fixed-and-variable-order-partition-unary-predicate
  (is (true? (v/disjoint? kb 'fixed_order_type 'variable_order_type 'CxCore)))
  (is (true? (v/genl? kb 'fixed_order_type 'unary_predicate 'CxCore)))
  (is (true? (v/genl? kb 'variable_order_type 'unary_predicate 'CxCore)))
  (testing "so a type of one order is never of variable order"
    (is (true? (v/disjoint? kb 'metatype 'variable_order_type 'CxCore)))))

(tu/deftest-kb an-equivalence-relation-is-the-intersection-of-its-three-marks
  (is (true? (v/genl? kb 'equivalence_relation 'reflexive 'CxCore)))
  (is (true? (v/genl? kb 'equivalence_relation 'symmetric 'CxCore)))
  (is (true? (v/genl? kb 'equivalence_relation 'transitive 'CxCore)))
  (testing "a predicate carrying all three marks is concluded an equivalence_relation"
    (tu/with-terms [sameShadeAs]
      (doseq [m '[reflexive symmetric transitive]]
        (v/assert kb (list m sameShadeAs) 'CxUniverse))
      (is (true? (v/ask? kb (list 'equivalence_relation sameShadeAs) 'CxUniverse)))))
  (testing "and one carrying two of them is not"
    (tu/with-terms [nearTo]
      (v/assert kb (list 'reflexive nearTo) 'CxUniverse)
      (v/assert kb (list 'symmetric nearTo) 'CxUniverse)
      (is (not (v/ask? kb (list 'equivalence_relation nearTo) 'CxUniverse))))))

;; ---- situations: change divides them ---------------------------------------

(tu/deftest-kb static-situations-and-events-partition-situation
  (is (true? (v/disjoint? kb 'static_situation 'event)))
  (testing "a situation that is not an event is a static_situation — the coverage half"
    (tu/with-terms [Drought]
      (v/assert kb (list 'situation Drought) 'CxUniverse)
      (v/assert kb (list 'not (list 'event Drought)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'static_situation Drought) 'CxUniverse))))))

;; ---- the folk taxonomy of organisms ----------------------------------------
;; Species under classes, classes under vertebrate, invertebrate and plant, and a
;; disjoint_metatype at each level: the separations are consulted, not stated per pair.

(def ^:private folk-species
  '[ant bee cat cow crow dog duck eagle fox frog grasshopper hare horse human lion mouse
    oak owl penguin rabbit rose sheep snake sparrow spider tortoise wolf])

(tu/deftest-kb vertebrates-and-invertebrates-partition-animal
  (is (true? (v/disjoint? kb 'vertebrate 'invertebrate)))
  (doseq [c '[amphibian bird fish mammal reptile]]
    (is (true? (v/genl? kb c 'vertebrate)) (str c " has a backbone")))
  (doseq [c '[arachnid insect]]
    (is (true? (v/genl? kb c 'invertebrate)) (str c " has none")))
  (is (true? (v/disjoint? kb 'insect 'mammal)) "so an insect is never a mammal")
  (is (true? (v/disjoint? kb 'spider 'owl)) "and the separation reaches the species")
  (testing "an animal denied a backbone is an invertebrate — the coverage half"
    (tu/with-terms [Limpet]
      (v/assert kb (list 'animal Limpet) 'CxUniverse)
      (v/assert kb (list 'not (list 'vertebrate Limpet)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'invertebrate Limpet) 'CxUniverse))))))

(tu/deftest-kb the-folk-classes-separate-their-kinds
  (is (true? (v/disjoint? kb 'tree 'flower)) "plant_class separates the plant classes")
  (is (true? (v/disjoint? kb 'oak 'rose)) "and the kinds below them")
  (is (true? (v/disjoint? kb 'insect 'arachnid)) "invertebrate_class separates its classes")
  (doseq [m '[vertebrate_class invertebrate_class plant_class]]
    (is (true? (v/genl? kb m 'folk_biological_class)) (str m " is a folk_biological_class")))
  (is (true? (v/disjoint? kb 'vertebrate_class 'plant_class))
      "and no class is of two of them"))

(tu/deftest-kb no-organism-is-of-two-folk-species
  (is (true? (v/disjoint? kb 'cat 'cow)))
  (is (true? (v/disjoint? kb 'crow 'owl)))
  (is (true? (v/disjoint? kb 'human 'horse)))
  (is (true? (v/disjoint? kb 'folk_biological_class 'folk_species))
      "and a species is never a class")
  (tu/with-terms [Bessie]
    (v/assert kb (list 'cow Bessie) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'horse Bessie) 'CxUniverse)))))

(tu/deftest-kb the-folk-taxonomy-settles-every-pair-of-organism-kinds
  ;; Every pair of the kinds below organism is subsumption-related or separated.  grass is
  ;; a plant_class beside tree and flower, so it is apart from each and from oak and rose.
  ;; The seven biology properties CxLife places under biological, organism and animal are states
  ;; and capacities of an organism rather than kinds of one, so they are left out: each
  ;; crosses the folk taxonomy, and its pairs with it stay unknown.
  (let [props   '#{alive dead mortal asleep awake breathes_air warm_blooded}
        org     (set (remove props (filter #(v/genl? kb % 'organism) (v/types kb))))
        unknown (for [{:keys [a b status]} (:pairs-data (v/disjointness-audit kb))
                      :when (and (org a) (org b) (= :unknown status))]
                  (set [a b]))]
    (is (every? org folk-species) "every species is an organism")
    (is (true? (v/disjoint? kb 'grass 'oak)) "grass is not a tree, so not an oak")
    (is (= [] (vec unknown)))))

;; ---- folk_species is on the forced-monotonic roster ------------------------
;; A species membership is definitional, so CxUniverse writes each :monotonic and a rule
;; concluding a roster literal from one alone fires as a roster rule.

(tu/deftest-kb a-folk-species-membership-is-held-monotonic
  (is (= :monotonic (v/defeat-class kb (v/handle-of kb '(folk_species dog) 'CxOrganism))))
  (testing "a denial of one is held OUT"
    (let [d (v/assert kb '(not (folk_species dog)) 'CxUniverse)]
      (is (not (v/in? kb d)))
      (is (true? (v/ask? kb '(folk_species dog) 'CxUniverse))))))

(tu/deftest-kb a-rule-from-folk-species-to-orthogonal-is-a-roster-rule
  ;; A rule that declares every species orthogonal to a kind of tangible thing:
  ;; its one antecedent is a roster literal, so its firings are believed rather than held
  ;; void and reported as a :forced-conclusion.
  (tu/with-terms [tended]
    (v/assert kb (list 'genl tended 'tangible) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies '(folk_species ?s) (list 'orthogonal '?s tended)))
              'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal 'dog tended) 'CxUniverse)))
    (is (= :orthogonal (v/subsumption-status kb 'dog tended)))
    (is (not-any? #(= :forced-conclusion (:violation %)) (v/violations kb)))))

(tu/deftest-kb a-warm-blooded-animal-is-a-vertebrate-by-default
  (let [edges (filter #(v/premise? kb (:id %)) (v/sentexes-matching kb '(genl warm_blooded vertebrate) 'CxUniverse))]
    (is (= 1 (count edges)) "(genl warm_blooded vertebrate) is stated in CxUniverse")
    (is (= :default (:strength (first edges))) "at default strength"))
  (tu/with-terms [Warm1 Cat1 Trout1]
    (v/assert kb (list 'warm_blooded Warm1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'vertebrate Warm1) 'CxUniverse)))
    (testing "and the class rules that derive and deny warm_blooded raise no clash"
      (v/assert kb (list 'mammal Cat1) 'CxBiology)
      (v/assert kb (list 'fish Trout1) 'CxBiology)
      (is (true? (v/ask? kb (list 'warm_blooded Cat1) 'CxBiology)))
      (is (true? (v/ask? kb (list 'not (list 'warm_blooded Trout1)) 'CxBiology)))
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb artifact-is-declared-nowhere-and-the-seven-kinds-are-made
  ;; The KB declares no artifact term and no alias for one.  building, clothing,
  ;; container, furniture, machine, tool and vehicle are kinds of made.
  (is (empty? (v/sentexes-matching kb '(comment artifact ?text) '?ctx)))
  (is (empty? (v/sentexes-matching kb '(genl artifact ?type) '?ctx)))
  (is (empty? (v/sentexes-matching kb '(genl ?type artifact) '?ctx)))
  (is (= 1 (count (v/sentexes-matching kb '(comment made ?text) 'CxAbstract))))
  (doseq [t '[building clothing container furniture machine tool vehicle]]
    (is (true? (v/genl? kb t 'made 'CxAbstract)) (str t " is made")))
  (doseq [t '[clothing container furniture machine tool vehicle]]
    (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'genl t 'made) 'CxAbstract))
        (str "(genl " t " made) is stated"))))

;; ---- made and natural ------------------------------------------------------
;; made and natural partition tangible.  A formation is a natural tangible that nothing
;; grew and nobody made.  biological is orthogonal to made and to natural.

(tu/deftest-kb made-and-natural-partition-tangible
  (is (true? (v/disjoint? kb 'made 'natural)))
  (is (true? (v/genl? kb 'made 'tangible 'CxAbstract)))
  (is (true? (v/genl? kb 'natural 'tangible 'CxAbstract)))
  (is (= 1 (count (v/sentexes-matching kb '(comment natural ?text) 'CxAbstract))))
  (testing "a tangible cannot be both"
    (tu/with-terms [Hybrid1]
      (v/assert kb (list 'made Hybrid1) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'natural Hybrid1) 'CxUniverse)))))
  (testing "and a tangible denied being made is natural — the coverage half"
    (tu/with-terms [Pebble1]
      (v/assert kb (list 'tangible Pebble1) 'CxUniverse)
      (v/assert kb (list 'not (list 'made Pebble1)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'natural Pebble1) 'CxUniverse))))))

(tu/deftest-kb a-formation-is-natural-and-never-made
  (is (true? (v/genl? kb 'formation 'natural 'CxAbstract)))
  (is (= 1 (count (v/sentexes-matching kb '(comment formation ?text) 'CxAbstract))))
  (tu/with-terms [Rock1]
    (v/assert kb (list 'formation Rock1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'natural Rock1) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'tangible Rock1) 'CxUniverse)))
    (is (true? (tu/stored-in-clash? kb (list 'made Rock1) 'CxUniverse))
        "a formation that is also made is a clash, by the partition")))

(tu/deftest-kb a-formation-is-not-biological
  (is (true? (v/disjoint? kb 'formation 'biological)))
  (is (true? (v/disjoint? kb 'formation 'organism)) "the separation reaches below biological")
  (tu/with-terms [Crystal1]
    (v/assert kb (list 'formation Crystal1) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'biological Crystal1) 'CxUniverse)))))

(tu/deftest-kb a-wild-sheep-is-natural-and-biological
  ;; biological is orthogonal to made and to natural.  A wild sheep is natural and
  ;; biological, and a cloned sheep is made and biological.
  (is (not (v/disjoint? kb 'biological 'natural)))
  (is (not (v/disjoint? kb 'sheep 'natural)))
  (tu/with-terms [WildSheep1]
    (v/assert kb (list 'sheep WildSheep1) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'natural WildSheep1) 'CxUniverse))
        "a sheep that is natural is no clash")
    (is (true? (v/ask? kb (list 'natural WildSheep1) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'biological WildSheep1) 'CxUniverse)))
    (is (not (v/ask? kb (list 'made WildSheep1) 'CxUniverse)))))

(tu/deftest-kb a-substance-can-be-made
  ;; Steel is a made substance, so nothing separates substance from made.
  (is (not (v/disjoint? kb 'substance 'made)))
  (is (not-any? #(v/premise? kb (:id %)) (v/sentexes-matching kb '(disjoint substance made) '?ctx)))
  (tu/with-terms [Steel1]
    (v/assert kb (list 'substance Steel1) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'made Steel1) 'CxUniverse))
        "a substance that is also made is no clash")
    (is (true? (v/ask? kb (list 'made Steel1) 'CxUniverse)))))

;; ---- orthogonal pairs across made and natural -------------------------------
;; In each pair the two types overlap and neither subsumes the other.  An orthogonal is
;; not inherited along genl, so the KB states each pair, or states a typeOrthogonal fact
;; over origin_type that derives the pair with made and the pair with natural.  Each
;; witness is an individual in both types.

(def ^:private cross-cutting
  '[[organism made Dolly1] [organism natural WildSheep1]
    [body_part made LabBladder1] [body_part natural Heart1]
    [substance made Steel1] [substance natural Water1] [substance formation Sand1]
    [food made Bread1] [food natural Apple1] [food biological Apple2]
    [food formation SeaSalt1]])

(tu/deftest-kb what-cuts-across-made-and-natural-is-stated-orthogonal
  (doseq [[a b witness] cross-cutting]
    (testing (str a " and " b)
      (if (contains? '#{made natural} b)
        (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'typeOrthogonal 'origin_type a) 'CxAbstract))
            (str "(typeOrthogonal origin_type " a ") is stated"))
        (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'orthogonal a b) 'CxAbstract))
            (str "(orthogonal " a " " b ") is stated")))
      (is (= :orthogonal (v/subsumption-status kb a b)) "the pair reads orthogonal")
      (is (not (v/disjoint? kb a b)))
      (let [w (tu/fresh-term :individual witness)]
        (v/assert kb (list a w) 'CxUniverse)
        (is (not (tu/stored-in-clash? kb (list b w) 'CxUniverse))
            (str "a " a " that is " b " is no clash"))
        (is (true? (v/ask? kb (list b w) 'CxUniverse)))))))

(tu/deftest-kb a-body-part-is-made-of-a-substance
  ;; Nothing is both biological and a substance.  madeOf relates a biological thing to the
  ;; substance it is made of, so a trunk made of wood is no clash.
  (tu/with-terms [Trunk1 WoodPortion1]
    (v/assert kb (list 'body_part Trunk1) 'CxUniverse)
    (v/assert kb (list 'substance WoodPortion1) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'madeOf Trunk1 WoodPortion1) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'madeOf Trunk1 WoodPortion1) 'CxUniverse)))))

;; ---- the use/mention vocabulary: proposition, means, denotes, expresses -----

(tu/deftest-kb a-sentence-denoting-symbol-is-well-formed-in-expresses
  ;; MuffetsFavoriteSentence stands for a wff_sentence without spelling one out.  Arg 2 of
  ;; expresses asks for a proposition — what a sentence EXPRESSES, not a sentence itself —
  ;; and (number 212) is itself a wff_sentence (number is a unary_predicate, and (number
  ;; 212) holds because 212 is one): a formula written where the vocabulary asks for its
  ;; semantic content, not its shape.
  (v/assert kb (list 'wff_sentence 'MuffetsFavoriteSentence) 'CxUniverse)
  (let [sentence (list 'expresses 'MuffetsFavoriteSentence (list 'number 212))
        h        (v/assert kb sentence 'CxUniverse)]
    (is (some? h) "the write is accepted, not refused for a formula in a term position")
    (is (true? (v/ask? kb sentence 'CxUniverse)) "and believed, not merely stored and convicted")))

(tu/deftest-kb two-sentences-express-one-proposition
  ;; MuffetEstUnChien stands for the French sentence "Muffet est un chien" without
  ;; spelling it out.  It and (Quote (dog Muffet)) are two different wff sentences, and
  ;; both express the one proposition that Muffet is a dog.
  (v/assert kb (list 'wff_sentence 'MuffetEstUnChien) 'CxUniverse)
  (v/assert kb (list 'proposition 'MuffetIsADog) 'CxUniverse)
  (let [english (list 'expresses (list 'Quote (list 'dog 'Muffet)) 'MuffetIsADog)
        french  (list 'expresses 'MuffetEstUnChien 'MuffetIsADog)]
    (v/assert kb english 'CxUniverse)
    (v/assert kb french 'CxUniverse)
    (is (true? (v/ask? kb english 'CxUniverse)))
    (is (true? (v/ask? kb french 'CxUniverse)))
    (is (= 2 (count (v/sentexes-matching kb (list 'expresses '?s 'MuffetIsADog) 'CxUniverse)))
        "(expresses ?s MuffetIsADog) finds both sentences")))

(tu/deftest-kb means-is-functional-and-its-specs-inherit-it
  ;; (functional means) constrains argument 2 of means — and, through props-over's walk
  ;; up genl (taxonomy.clj: "a genl edge between predicates says the sub's tuples ARE the
  ;; super's"), of every sub-predicate too.  denotes genl's to means, so two monotonic,
  ;; distinct-symbol fillers of one denotes should derive (equals ...) the way two
  ;; fillers of means itself would.
  (tu/with-terms [X Y]
    (v/assert kb (list 'denotes (list 'Quote 'Muffet) X) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'denotes (list 'Quote 'Muffet) Y) 'CxUniverse {:strength :monotonic})
    (is (true? (v/ask? kb (list 'equals X Y) 'CxUniverse))
        "functional on means reaches denotes through its genl edge")))
