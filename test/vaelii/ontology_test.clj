;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ontology-test
  "The shipped ontology as a *modelling* claim, where `starter-test` reads it as a schema
  that loads and reasons.

  This namespace asserts the structure of the mini-ontology rather than any one inference:
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
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.predicates :as pr]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private B 'CxBiology)

(defn- upper-forms
  "Every form the upper files state, in loader order."
  []
  (mapcat #(text/read-forms (io/file "resources/kb/upper" %)) (core-context/upper-files)))
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

(tu/deftest-kb all-dogs-have-shell-access
  ;; Asserts that argument 2 of capabilityType and of hasCapability is a happening kind, not
  ;; only an event kind.  Shell access comes and goes: a dog logs in, wanders off, and logs
  ;; in again, so shell_access lies under happening and intermittent, never under event.
  ;; Both predicates take it with no clash, and neither places it under event.
  (tu/with-terms [shell_access Rex]
    (v/assert kb (list 'genl shell_access 'happening) 'CxUniverse)
    (v/assert kb (list 'genl shell_access 'intermittent) 'CxUniverse)
    (v/assert kb (list 'capabilityType 'dog shell_access) 'CxUniverse)
    (is (true? (v/ask? kb (list 'capabilityType 'dog shell_access) 'CxUniverse))
        "every dog may have shell access")
    (v/assert kb (list 'dog Rex) 'CxUniverse)
    (v/assert kb (list 'hasCapability Rex shell_access) 'CxUniverse)
    (is (true? (v/ask? kb (list 'hasCapability Rex shell_access) 'CxUniverse))
        "and this one does")
    (is (not (v/genl? kb shell_access 'event)) "a happening with a gap is no event")
    (is (empty? (v/conflicts kb)) "and nothing clashes")))

(tu/deftest-kb both-ability-predicates-type-their-second-argument-as-a-happening-kind
  (testing "the declarations"
    (is (v/ask? kb '(genlArg hasCapability 2 happening)))
    (is (v/ask? kb '(genlArg capabilityType 2 happening))))
  (testing "an event kind nobody listed as an ability is accepted as one"
    (tu/with-terms [swimming Wanda]
      (v/assert kb (list 'genl swimming 'event) 'CxUniverse)
      (v/assert kb (list 'animal Wanda) N)
      (is (v/assert kb (list 'hasCapability Wanda swimming) N))
      (is (v/assert kb (list 'capabilityType 'fish swimming) N))))
  (testing "a kind that is not a happening kind is convicted by genlArg, against happening"
    ;; Forced to the constraint-only reading, where `assert` holds the fact inert.
    (tu/without-entailing
     (tu/with-terms [Wanda]
       (v/assert kb (list 'animal Wanda) N)
       (doseq [s [(list 'hasCapability Wanda 'metal_stuff) (list 'capabilityType 'fish 'metal_stuff)]]
         (let [p (first (filter #(= :arg-genl (:type %)) (tu/check-or-conviction kb s N)))]
           (is (= :arg-genl (:type p)) (str (pr-str s) " is convicted by genlArg"))
           (is (= 'happening (:expected p)) (str (pr-str s) " is convicted against happening"))))))))

(tu/deftest-kb the-first-position-of-hasCapability-takes-any-causal-doer
  ;; A doer is whatever doneBy can name, and that is wider than animal: a machine or an
  ;; organization can be the doer of an event.  What cannot is an acausal thing, which
  ;; can occupy no cause slot.  Forced to the constraint-only reading, where `assert`
  ;; holds the fact under the conviction.
  (tu/without-entailing
   (tu/with-terms [Pump Acme Noon]
     (v/assert kb (list 'machine Pump) N)
     (v/assert kb (list 'organization Acme) N)
     (v/assert kb (list 'time Noon) N)
     (testing "the declaration, which names causal and not animal"
       (is (v/ask? kb '(arg hasCapability 1 causal)))
       (is (not (v/ask? kb '(arg hasCapability 1 animal)))))
     (testing "the doers that are not animals"
       (is (v/genl? kb 'machine 'causal))
       (is (v/genl? kb 'organization 'causal))
       (is (= [] (v/check kb (list 'hasCapability Pump 'travelling) N)) "a machine")
       (is (= [] (v/check kb (list 'hasCapability Acme 'event) N)) "an organization"))
     (testing "an acausal thing is still convicted, against causal"
       (is (v/genl? kb 'time 'acausal))
       (let [p (first (filter #(= :arg-type (:type %))
                              (tu/check-or-conviction kb (list 'hasCapability Noon 'travelling) N)))]
         (is (some? p) "a time can be the doer of nothing")
         (is (= 1 (:position p)))
         (is (= 'causal (:expected p))))))))

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

(tu/deftest-kb a-life-stage-takes-a-kind-claim-of-its-own
  ;; One lineage, two stages: the adult flies and the larva does not.  Both stages are
  ;; kinds of the lineage, and each stage carries its own capability claim.
  (testing "the stages are kinds of the lineage, named by their stage relation"
    (is (v/ask? kb '(genl caterpillar lepidopteran) B))
    (is (v/ask? kb '(genl butterfly lepidopteran) B))
    (is (v/ask? kb '(larvalFormOf caterpillar lepidopteran) B))
    (is (v/ask? kb '(adultFormOf butterfly lepidopteran) B)))
  (testing "never both at once, though one organism is each in turn"
    (is (v/ask? kb '(diachronicallyDisjoint caterpillar butterfly) B))
    (is (v/ask? kb '(diachronicallyDisjoint butterfly caterpillar) B) "symmetric")
    (is (not (true? (v/disjoint? kb 'caterpillar 'butterfly))) "and not timelessly disjoint"))
  (testing "a timeless disjoint is also a diachronic one"
    (is (v/ask? kb '(diachronicallyDisjoint quantity situation) B)))
  (testing "the adult flies"
    (is (v/ask? kb '(capabilityType butterfly flying) B)))
  (testing "the larva does not, and the KB says so rather than staying silent"
    (is (not (v/ask? kb '(capabilityType caterpillar flying) B)))
    (is (seq (v/sentexes-matching kb '(not (capabilityType caterpillar flying)) '?ctx)))))

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
    ;; it picks convicts the half it was not written for: `arg … 1 causal` is right for
    ;; `(… Tweety flying)` and wrong for `(… bird flying)`, since a kind is not a member of
    ;; the type it lies under.  So: two predicates, the kind-level one marked, and the pair
    ;; named in prose because the predicate that names pairs cannot take a mixed half.
    (testing "the kind-level half relates kinds, and says so"
      (is (v/ask? kb '(type_relation_predicate capabilityType))))
    (testing "the instance-level half is MIXED — one causal thing to one event kind — so it
            carries no relation_kind, and its two positions take different checks"
      (is (not (v/ask? kb '(instance_relation_predicate hasCapability))))
      (is (not (v/ask? kb '(type_relation_predicate hasCapability))))
      (is (v/ask? kb '(arg hasCapability 1 causal)))
      (is (v/ask? kb '(genlArg hasCapability 2 happening))))
    (testing "so declaring the pairing would mark the mixed half — typeToInstancePred
            types its second argument an instance half, and derives that mark"
      (tu/with-terms [CxPairing]
        (v/assert kb (list 'genlCx CxPairing 'CxUniverse) 'CxUniverse)
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
  ;; meaning, so convicting them says nothing about the shipped content.  A `defeat` is
  ;; one only the engine places, so `check` refuses it as `:derived-only`.
  (let [encoding? (fn [s] (let [s (if (and (seq? s) (= 'not (first s))) (second s) s)]
                            (and (seq? s) (contains? '#{implies exceptWhen defeat} (first s)))))
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
        (str "shipped facts their own declarations convict: " (vec guilty)))
    (is (empty? (filter #(= :inert-argument (:violation %)) (v/violations kb)))
        "and none is held inert")))

(def ^:private undeclared-positions
  "The argument positions of arity **2 and up** that the shipped text contexts declare with
  no `arg`-family form, each with the reason.  A position that holds a term of any kind
  declares `thing` (`(arg P n thing)`), and a position that holds a term taken as written
  declares the expression type with `quotedArg`, so neither belongs here.  What remains is
  a position no declaration fits.

  A position that is not here and not declared fails the test below; a position here that
  gains a declaration fails it too.

  A **unary** predicate's one position is exempt as a class and is not listed — see the
  test."
  (merge
   {'[genl 1] "predicate specializations: (genlArg genl 1 thing) is false of (genl performedBy doneBy), whose ends are binary predicates (core.txt, beside genl)"
    '[genl 2] "the root: (genlArg genl 2 thing) would entail (genl thing thing), refused as irreflexive (core.txt, beside genl)"}
   ;; the example: (Quote S), whose arg reading derives a membership of a reified
   ;; constant or of a bare symbol written in its place, and whose quotedArg reading
   ;; names no syntactic type of the form
   (into {} (for [p '[positiveExample negativeExample borderlineExample]]
              [[p 2] "the example, a quoted sentence (Quote …)"]))
   ;; the five aggregation operators: a result, a value variable, a sentence body.  Each
   ;; is a query operator that is never stored, and a type on a slot reaches the rule
   ;; variables bound there.
   (into {} (for [op '[agg/count agg/sum agg/avg agg/min agg/max] i [1 2 3]]
              [[op i] "an operator slot — a result, a value variable and a sentence body"]))
   ;; the stored exception (exceptWhen Q (sentexHandle H)): assert-entry/assert-exceptWhen-meta!
   ;; runs no argument check on it, and it is excluded from fact matching
   {'[exceptWhen 1] "the exception query, whose variables are the rule's, so a type on the slot would reach the rule variables bound there"
    '[exceptWhen 2] "the sentexHandle of the rule the exception qualifies, a mention of a stored sentex"}))

(deftest every-shipped-function-declares-its-corresponding-predicate
  ;; A function comes with the predicate relating its arguments to its value
  ;; (`functionCorrespondingPredicate`, docs/nat.md), so a rule can be written over the
  ;; predicate without building the function's term.  Read off the engine's text
  ;; contexts, as the test below reads them; koinii's contexts are the app's vocabulary
  ;; and are not read.
  (let [files (->> (file-seq (io/file "resources/kb"))
                   (filter #(.endsWith (.getName ^java.io.File %) ".txt"))
                   (remove #(.contains (.getPath ^java.io.File %) "/koinii/")))
        sents (filter seq? (mapcat text/read-forms files))
        fns   (set (for [s sents :when (#{'reifiable_function 'unreifiable_function} (first s))]
                     (second s)))
        corr  (set (for [s sents :when (= 'functionCorrespondingPredicate (first s))]
                     (second s)))]
    (is (seq fns) "the text contexts were found and read")
    (is (empty? (remove corr fns))
        (str "functions declaring no corresponding predicate: " (pr-str (sort (remove corr fns)))))))

(deftest every-position-of-a-shipped-arity-above-one-is-declared
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
  ;; state predicates in the upper layer do — and this test does not ask it to.
  (let [files    (->> (file-seq (io/file "resources/kb"))
                      (filter #(.endsWith (.getName ^java.io.File %) ".txt")))
        sents    (mapcat text/read-forms files)
        of       (fn [functors] (filter #(and (seq? %) (contains? functors (first %))) sents))
        classes  '{unary_predicate 1 binary_predicate 2 ternary_predicate 3}
        ;; a `:monotonic` membership of a type a `:monotonic` edge chain carries to an
        ;; exact class binds the length too (docs/taxonomy.md, "Arity")
        mono     (keep #(when (and (seq? %) (= 'set/monotonic (first %)) (seq? (second %)))
                          (second %))
                       sents)
        edges    (filter #(and (= 'genl (first %)) (= 3 (count %))) mono)
        metas    (loop [m classes]
                   (let [m' (into m (keep (fn [[_ a b]] (when-let [n (get m b)]
                                                          (when-not (contains? m a) [a n]))))
                                  edges)]
                     (if (= m m') m (recur m'))))
        arities  (merge (into {} (for [s (filter #(= 2 (count %)) mono)
                                       :let [n (get metas (first s))]
                                       :when n]
                                   [(second s) n]))
                        (into {} (for [s (of '#{unary_predicate binary_predicate ternary_predicate})]
                                   [(second s) (classes (first s))]))
                        (into {} (for [s (of '#{arity})] [(second s) (nth s 2)])))
        declared (set (for [s (of '#{arg argArg genlArg quotedArg}) :when (integer? (nth s 2))]
                        [(second s) (nth s 2)]))
        gaps     (set (for [[p n] arities
                            :when (and (integer? n) (< 1 n))
                            i    (range 1 (inc n))
                            :when (not (declared [p i]))]
                        [p i]))
        excused  (set (keys undeclared-positions))]
    (is (seq arities) "the text contexts were found and read")
    (is (empty? (remove excused gaps))
        (str "positions the shipped contexts leave undeclared: " (pr-str (sort (remove excused gaps)))))
    (is (empty? (remove gaps excused))
        (str "listed positions that are now declared (drop them from undeclared-positions): "
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

;; ---- the biology properties and the kinds they are said of ---------------

(def ^:private biology-properties
  "The seven life.txt properties placed under the kind each is said of."
  '{alive biological, dead biological, mortal organism,
    asleep animal, awake animal, breathes_air animal, warm_blooded animal})

(tu/deftest-kb the-biology-properties-are-placed-under-their-kind
  ;; The naming rules make `alive` and `mortal` legal unary predicates, and nothing in
  ;; them says where a name sits in the genl hierarchy.  Each of these properties is
  ;; said of one kind, so it is placed under that kind: only an animal is warm-blooded,
  ;; and `(warm_blooded Rock1)` is a type clash.  A kind may sit below one of them, as
  ;; `bird` and `mammal` sit below `warm_blooded`, and the kind a property is said of
  ;; never does.  Spelling a type as a noun and a
  ;; property as an adjective is a style hint, not a rule of the hierarchy.
  (testing "the properties the biology theory concludes are placed under their kind"
    (doseq [[p kind] biology-properties]
      (is (v/genl? kb p kind) (str p " is placed under " kind))
      (is (v/genl? kb p 'thing) (str p " reaches thing"))
      (is (v/isa? kb p 'unary_predicate)
          (str p " is still a one-place predicate"))
      (is (not (v/genl? kb kind p)) (str kind " is not placed under " p))))
  (testing "a kind may sit below one: every bird and every mammal is warm-blooded"
    (doseq [t '[bird mammal penguin dog]]
      (is (v/genl? kb t 'warm_blooded) (str t " is placed under warm_blooded")))
    (tu/with-terms [Pingu Rex Nemo]
      (v/assert kb (list 'penguin Pingu) 'CxWell)
      (v/assert kb (list 'dog Rex) 'CxWell)
      (v/assert kb (list 'fish Nemo) 'CxWell)
      (is (v/ask? kb (list 'warm_blooded Pingu) 'CxWell) "a penguin is warm-blooded")
      (is (v/ask? kb (list 'warm_blooded Rex) 'CxWell) "a dog is warm-blooded")
      (is (v/ask? kb (list 'not (list 'warm_blooded Nemo)) 'CxWell)
          "a fish is not, by the rule that denies it")))
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
  seven biology properties among them are placed under the kind each is said of, as
  `the-biology-properties-are-placed-under-their-kind` holds."
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
  ;; CxUniverse requires every at_least_metatype to name a typeGenl and every unary_predicate
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
  ;; CxUniverse states (typeGenl empty thing) and (typeGenl nonempty thing) beside their
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
  `orthogonal`, `intersection` or `typeGenl` between two contexts' terms therefore belongs at
  a context that sees both.

  `arg` / `genlArg` / `quotedArg` / `result` / `interArg` and the relation-metadata marks are
  deliberately NOT here: they constrain a relation's OWN argument or classify the relation
  itself, and the type they name is checked from the DATA context that asserts a tuple —
  every data context sits below CxUniverse and sees the whole upper layer."
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
  ;; A middle context sees CxUniverse and not, in general, another middle context, so a claim
  ;; in one middle context over a type another defines stores clean (an undeclared symbol
  ;; cannot violate an assert-time check: open-world, docs/taxonomy.md) and lands in a context
  ;; that cannot read its own subject.
  ;;
  ;; Read off the text files the starter actually loads (`upper/` into CxUniverse, `middle/`
  ;; into each file's context, `vaelii.host.starter`) because the claim is about what those
  ;; contexts *write*, not what the engine derives or the starter publishes
  ;; (`(unary_predicate T)` is asserted into CxUniverse for every subtype of `thing`, and the
  ;; arity rules conclude from those in CxUniverse too; both are deliberate).  The loaded KB
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
        files    (concat (for [f (core-context/upper-files)] [(io/file "resources/kb/upper" f) 'CxUniverse])
                         (for [f (text/kb-files (io/file "resources/kb/middle"))] [f (text/context-of f)]))
        forms    (->> files
                      (mapcat (fn [[f c]] (map #(vector % c) (text/read-forms f))))
                      (map resolve*)
                      (filter (fn [[s _]] (relating? s))))
        blind    (for [[s c] forms
                       :let  [miss (filter #(and (anywhere %) (not (rooted? % c))) (names s))]
                       :when (seq miss)]
                   {:context c :sentence s :cannot-see (vec miss) :move-to (homes (distinct miss))})]
    (is (seq forms) "the shipped context files were found and read")
    (is (empty? blind)
        (str "type relations written where a term they name is invisible — move each to a "
             "context that sees the named types (or define the types in an upper file):\n"
             (apply str (interpose "\n"
                                   (for [b blind]
                                     (str "  " (:context b) " asserts " (pr-str (:sentence b))
                                          "\n    cannot see " (pr-str (:cannot-see b))
                                          " — defined in " (pr-str (:move-to b))
                                          ", so move the assertion there"))))))))

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
  ;; The arity generators are the case that tests the claim.  The relation-wide one
  ;; generates one rule per `relationTypeByArity` fact, over `unary` through `quinary`,
  ;; and the predicate and function ones generate a rule per mapping fact over the ten
  ;; kind classes, each guarded by its kind.  A guarded rule concludes a kind
  ;; class the relation-wide rule does not, so neither covers the other, and a mapping
  ;; table that grew a redundant member would show up here.
  (let [q (:subsumption (v/kb-quality kb {:limit 100}))]
    (is (pos? (:total q)) "the reading ran over rules rather than over nothing")
    (is (not (:truncated? q)) "and over all of them")
    (is (zero? (:subsumed-count q))
        (str "covered: " (pr-str (mapv (juxt :by-sentence :sentence) (:subsumed q)))))))

(tu/deftest-kb a-generated-rule-is-not-exempt-from-the-subsumption-reading
  ;; The reading does not spare a rule for having been generated by a generator: a
  ;; mapping fact over a type and a second over its subtype mint two rules, and the
  ;; narrower one fires nowhere the broader does not.
  (tu/with-terms [broad_type narrow_type outcome_type generatesType]
    (v/assert kb (list 'genl broad_type 'thing) 'CxUniverse)
    (v/assert kb (list 'genl narrow_type broad_type) 'CxUniverse)
    (v/assert kb (list 'genl outcome_type 'thing) 'CxUniverse)
    (v/assert kb (list 'implies (list generatesType '?type)
                       (list 'implies (list '?type '?x) (list outcome_type '?x))) 'CxUniverse {:direction :forward})
    (doseq [type [broad_type narrow_type]]
      (v/assert kb (list generatesType type) 'CxUniverse))
    (let [rule (fn [type] (list 'implies (list type '?x) (list outcome_type '?x)))
          pair [(v/handle-of kb (rule broad_type) 'CxUniverse)
                (v/handle-of kb (rule narrow_type) 'CxUniverse)]
          q (:subsumption (v/kb-quality kb {:limit 100}))]
      (is (every? some? pair) "both rules are generated")
      (is (not (:truncated? q)))
      (is (some #(= pair [(:by %) (:subsumed %)]) (:subsumed q))
          "the narrower generated rule is reported as covered"))))

(defn- rule-clashes-everywhere
  "Every finding of the kb-integrity rule-clash `categories` over the whole KB: the union
  of the sweeps from each leaf context, since a pair a context sees is seen by every
  context below it."
  [kb categories]
  (into #{}
        (comp (filter #(= #{%} (set (v/context-down kb %))))
              (mapcat #(mapcat (v/kb-integrity kb #{} % {:categories categories})
                               [:rule-clash :rule-clash-review])))
        (v/contexts kb)))

(tu/deftest-kb every-negated-conclusion-the-ontology-can-clash-with-is-stated-as-an-exception
  ;; kb-integrity's rule-clash pairing, and the structure of what it finds here is the
  ;; finding.
  ;; Every pair whose conclusions contradict outright — a bird's flight against a
  ;; penguin's, wakefulness against sleep, life against death, and the shepherd boy's
  ;; credibility against his lying — is one of the two rules **stating** the other as an
  ;; `exceptWhen`, which is what `:excepted` marks.  Nothing else is left: the arity table
  ;; would be `:functional` pairs, each two of the classification rules concluding a
  ;; different `(arity ?p n)` for one `?p`, and the five exact classes are separated, so no
  ;; `?p` satisfies two antecedents and the pairs are unreachable rather than unstated
  ;; (docs/integrity.md).
  ;;
  ;; The arity floors would be 82 `:disjoint` pairs.  A floor rule reads `(arity ?r ?n)`
  ;; with `(lessThan k ?n)` and concludes `(at_least_… ?r)`, which is disjoint from every
  ;; exact class of k places or fewer, and a rule concluding that class or claiming that
  ;; arity binds the same `?r` to exactly k places or fewer.  The arity table is
  ;; functional, so no `?r` satisfies both antecedents, and `arity-floor-conflicted?` drops
  ;; every such pair as unreachable.
  ;;
  ;; No `:disjoint` pair is left.  CxCriedWolf's `lied_before → liar` concludes a person,
  ;; and two kinds of rule conclude a type disjoint from one: the signed refinements of
  ;; `integer` and the relation classifications (arity, `bijection`, the arity classes).
  ;; No ground term satisfies both antecedents of any such pair — nothing is a person and
  ;; an integer or a relation — and the checker reads that off the
  ;; `arg` declarations: `(arg lied_before 1 person)` types the liar rule's variable a
  ;; `person`, disjoint from what the other rule states or concludes about the same term,
  ;; so `arg-type-conflicted?` drops every such pair as unreachable (vaelii#95).
  ;;
  ;; Two pairs are left unexcepted on purpose.  A proper reading's definition concludes a
  ;; proper tangible part or a proper sub-situation, so a part, and the root rule
  ;; `(properPartOf x y) → (not (partOf y x))` denies one.  Both fire for one tuple only
  ;; where the facts already contradict the root rule: a part whose whole is stated a proper
  ;; part of it.  Both rules are strict definitions, so that clash is the one the facts owe,
  ;; and an exception would hide it.  Those two are the live `:rule-clash` findings.
  (let [live        (rule-clashes-everywhere kb #{:rule-clash})
        pairs       (rule-clashes-everywhere kb #{:rule-clash-review})
        kinds       (frequencies (map :kind (concat live pairs)))
        root-denial '(implies (properPartOf ?part ?whole) (not (partOf ?whole ?part)))
        definition? #(some #{root-denial} (:sentences %))]
    (is (every? definition? live)
        (str "live clashes: " (pr-str (mapv (juxt :kind :sentences) live))))
    (is (= {:negation 6} kinds)
        (str "clashes: " (pr-str (mapv (juxt :kind :sentences) (concat live pairs)))))
    (is (every? :excepted (filter #(= :negation (:kind %)) pairs))
        "negation clashes are excepted")
    (is (= 2 (count live))
        "and the root denial meets the two proper readings' definitions, unexcepted")))

(tu/deftest-kb a-type-relation-predicate-relates-predicates
  ;; Every argument of a type_relation_predicate is a predicate: the kinds it relates are
  ;; unary predicates, and genl relates predicate specializations of any arity as well.
  ;; core.txt concludes that forward from the relation kind, as (args ?relation predicate).
  (testing "disjoint's arguments derive as predicates"
    (is (= [{'?t 'predicate}] (v/query kb '(args disjoint ?t) 'CxUniverse))))
  (testing "and genl's, whose binary-predicate edges are predicates and not unary ones"
    (is (= [{'?t 'predicate}] (v/query kb '(args genl ?t) 'CxUniverse)))
    (is (v/ask? kb '(genl performedBy doneBy) 'CxUniverse)))
  (testing "the declaration reaches the rule-clash reading"
    ;; `(unary ?type) (disjoint ?type ?type) → (empty ?type)` demands ?type be a predicate
    ;; through disjoint's args, and `(function ?r) (arity ?r 1) → (unary_function ?r)` places
    ;; the same term under function.  predicate and function are disjoint, so the pair is
    ;; unreachable and arg-type-conflicted? drops it.
    (let [pairs (:pairs (:clashes (v/kb-quality kb {:limit 100})))]
      (is (not-any? (fn [p] (some #(some #{'empty} (flatten %)) (:sentences p))) pairs)
          (str "the emptiness rule pairs with nothing: " (pr-str (mapv :sentences pairs)))))))

(tu/deftest-kb the-arity-rules-clash-with-each-other-in-neither-direction
  ;; The rule-clash pairing's own half of the arity separation.  The generator generates one rule per
  ;; exact class, and two of them conclude two arities for one relation only where the
  ;; relation holds both classes — which `(disjoint unary binary)` and its two peers
  ;; refuse on the antecedents.  No `?relation` satisfies two of them, so the pair is
  ;; unreachable rather than unstated (docs/integrity.md).
  ;;
  ;; `(partition thing tangible intangible)` makes a relation-classification conclusion and a
  ;; story-predicate conclusion disjoint, so the arity rules would pair with CxCriedWolf's
  ;; `lied_before → liar` if the checker read only the conclusions.  It reads the
  ;; antecedents' `arg` declarations too: `(arg arity 1 relation)` types the arity rule's
  ;; variable a `relation`, disjoint from the `person` the paired rule concludes, so
  ;; `arg-type-conflicted?` drops the pair as unreachable (vaelii#95).  The arity table
  ;; therefore pairs with nothing.  An arity floor beside an exact class binds one relation
  ;; above and at or below one length, and `arity-floor-conflicted?` drops that pair, so
  ;; the floors pair with nothing either.
  (let [pairs   (rule-clashes-everywhere kb #{:rule-clash :rule-clash-review})
        about   (fn [f] (filter (fn [p] (some #(some #{f} (flatten %)) (:sentences p)))
                                pairs))]
    (is (empty? (about 'arity))
        (str "the arity table pairs with nothing: " (pr-str (mapv :sentences (about 'arity)))))
    (is (empty? (about 'unary_predicate))
        (str "nor do the classes: " (pr-str (mapv :sentences (about 'unary_predicate)))))
    (doseq [floor '[at_least_binary at_least_ternary at_least_quaternary at_least_quinary]]
      (is (empty? (about floor))
          (str "nor does " floor ": " (pr-str (mapv :sentences (about floor))))))))

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
  "The `:type` of the ex-info `assert` throws for `sentence`, or of the argument conviction
  it holds the fact inert under, or `:stored` when it takes it and holds nothing.  A fact
  the probe stored is retracted again (`tu/write-conviction`)."
  [kb sentence context]
  (or (:type (tu/write-conviction kb sentence context)) :stored))

(tu/deftest-kb a-time-is-in-time-and-in-no-space-and-causes-nothing
  ;; A date cannot be a cause: the year 2000 broke nothing — two-digit years did, at the
  ;; rollover.  `time` is temporal, aspatial and acausal, uninterrupted_time and
  ;; intermittent_time partition it, and time_point and time_interval partition
  ;; uninterrupted_time, so a moment and a stretch are all three and never each other.  A
  ;; calendar term is never minted, so its result type is read where it is checked: an
  ;; argument typed with a kind no result type reaches refuses it, one it reaches admits it.
  (testing "both parts reach time, and time_point still reaches temporal through it"
    (is (v/genl? kb 'time_point 'uninterrupted_time N))
    (is (v/genl? kb 'time_interval 'uninterrupted_time N))
    (is (v/genl? kb 'time_point 'time N))
    (is (v/genl? kb 'time_interval 'time N))
    (is (v/genl? kb 'time_point 'temporal N)))
  (testing "an instant is not a stretch, and neither is something that happens in time"
    (is (v/disjoint? kb 'time_point 'time_interval N))
    (is (v/disjoint? kb 'time_interval 'event N)))
  (testing "and CxUniverse relates a stretch to the dimension it is measured in"
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

(def ^:private time-calendar-facts
  "Facts time.txt states over calendar terms and moments: a stretch contains a stretch, a
  stretch contains a moment, and a calendar moment equals a moment spelled with
  InstantFn."
  '[(contains (YearFn 2000) (MonthFn 2000 1))
    (contains (DatetimeFn "2000") (DatetimeFn "2000-01"))
    (contains (YearFn 2000) (InstantFn 2000 3 1 0 0 0))
    (instantEqual (StartFn (YearFn 2000)) (InstantFn 2000 1 1 0 0 0))])

(tu/deftest-kb cxuniverse-reads-the-time-partition
  ;; time.txt types its calendar results time_interval and its moments time_point.  Each
  ;; partition derives its parts' edges to the whole, so no upper file states them.
  (testing "in CxUniverse a moment and a stretch are temporal, aspatial and never each other"
    (doseq [t '[time_point time_interval]
            up '[uninterrupted_time uninterrupted time temporal aspatial]]
      (is (true? (v/genl? kb t up 'CxUniverse)) (str t " must reach " up " in CxUniverse")))
    (is (true? (v/disjoint? kb 'time_point 'time_interval 'CxUniverse))))
  (testing "no upper file states an edge the partition derives"
    (let [stated (set (map (comp first text/peel-form)
                           (upper-forms)))]
      (doseq [s '[(genl time_point temporal) (genl time_point uninterrupted_time)
                  (genl time_interval uninterrupted_time) (genl uninterrupted_time time)
                  (genl intermittent_time time)]]
        (is (not (contains? stated s)) (str (pr-str s) " is derived from the partition")))))
  (testing "CxUniverse stores its calendar facts under both argument-type readings"
    (doseq [s time-calendar-facts]
      (is (= :stored (tu/with-entailing (refusal kb s 'CxUniverse))) (pr-str s))
      (is (= :stored (tu/without-entailing (refusal kb s 'CxUniverse))) (pr-str s)))))

;; ---- whether a temporal thing has a gap ------------------------------------
;; uninterrupted and intermittent partition temporal: a thing is present at every moment
;; between its start and its end, or there is a moment between them at which it is not.

(tu/deftest-kb uninterrupted-and-intermittent-partition-temporal
  (doseq [ctx '[CxUniverse]]
    (testing (str ctx)
      (is (true? (v/genl? kb 'uninterrupted 'temporal ctx)))
      (is (true? (v/genl? kb 'intermittent 'temporal ctx)))
      (is (true? (v/disjoint? kb 'uninterrupted 'intermittent ctx)))))
  (testing "a temporal thing denied being uninterrupted is intermittent — the coverage half"
    (tu/with-terms [Trial]
      (v/assert kb (list 'temporal Trial) 'CxUniverse)
      (v/assert kb (list 'not (list 'uninterrupted Trial)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'intermittent Trial) 'CxUniverse))))))

(tu/deftest-kb a-tangible-is-uninterrupted-by-default
  ;; A rock is present at every moment between its start and its end.  A watch taken
  ;; apart and rebuilt is not, and stating so is allowed.
  (is (true? (v/genl? kb 'tangible 'uninterrupted 'CxUniverse)))
  (is (empty? (filter #(= :monotonic (:strength %))
                      (v/sentexes-matching kb '(genl tangible uninterrupted) 'CxUniverse)))
      "the edge is a default")
  (tu/with-terms [Rock Watch]
    (v/assert kb (list 'stone Rock) 'CxUniverse)
    (is (true? (v/ask? kb (list 'uninterrupted Rock) 'CxUniverse)))
    (v/assert kb (list 'tangible Watch) 'CxUniverse)
    (is (some? (v/assert kb (list 'intermittent Watch) 'CxUniverse)) "the write is stored")
    (is (true? (v/ask? kb (list 'intermittent Watch) 'CxUniverse)))))

(tu/deftest-kb the-watch-of-theseus-is-intermittent
  ;; A watch taken apart and rebuilt exists intermittently, so its exception is stated
  ;; monotonically and defeats the default edge from tangible to uninterrupted.
  (let [clashes (fn [w] (count (filter #(some #{w} (flatten (map :sentence (:sides %))))
                                       (v/contradictions kb))))]
    (testing "a tangible with no stated exception is uninterrupted by default"
      (tu/with-terms [Rock]
        (v/assert kb (list 'tangible Rock) 'CxUniverse)
        (is (true? (v/ask? kb (list 'uninterrupted Rock) 'CxUniverse)))))
    (testing "the tangible membership first, then the monotonic exception"
      (tu/with-terms [WatchOfTheseus]
        (v/assert kb (list 'tangible WatchOfTheseus) 'CxUniverse)
        (v/assert kb (list 'intermittent WatchOfTheseus) 'CxUniverse {:strength :monotonic})
        (is (true? (v/ask? kb (list 'intermittent WatchOfTheseus) 'CxUniverse)))
        (is (false? (v/ask? kb (list 'uninterrupted WatchOfTheseus) 'CxUniverse)))
        (is (zero? (clashes WatchOfTheseus)))))
    (testing "the monotonic exception first, then the tangible membership"
      (tu/with-terms [WatchOfTheseus]
        (v/assert kb (list 'intermittent WatchOfTheseus) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list 'tangible WatchOfTheseus) 'CxUniverse)
        (is (true? (v/ask? kb (list 'intermittent WatchOfTheseus) 'CxUniverse)))
        (is (false? (v/ask? kb (list 'uninterrupted WatchOfTheseus) 'CxUniverse)))
        (is (zero? (clashes WatchOfTheseus)))))))

(tu/deftest-kb a-time-is-uninterrupted-or-intermittent
  ;; A week's evenings are a time with gaps; a moment and a stretch are times with none.
  (doseq [ctx '[CxUniverse]]
    (testing (str ctx)
      (is (true? (v/genl? kb 'uninterrupted_time 'uninterrupted ctx)))
      (is (true? (v/genl? kb 'intermittent_time 'intermittent ctx)))
      (is (true? (v/genl? kb 'intermittent_time 'time ctx)))
      (is (true? (v/disjoint? kb 'uninterrupted_time 'intermittent_time ctx)))
      (is (true? (v/disjoint? kb 'intermittent_time 'time_interval ctx)))))
  (testing "a time denied being uninterrupted is an intermittent_time"
    (tu/with-terms [Evenings]
      (v/assert kb (list 'time Evenings) 'CxUniverse)
      (v/assert kb (list 'not (list 'uninterrupted Evenings)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'intermittent_time Evenings) 'CxUniverse)))))
  (testing "and an uninterrupted time is an uninterrupted_time"
    (tu/with-terms [Afternoon]
      (v/assert kb (list 'time Afternoon) 'CxUniverse)
      (v/assert kb (list 'uninterrupted Afternoon) 'CxUniverse)
      (is (true? (v/ask? kb (list 'uninterrupted_time Afternoon) 'CxUniverse))))))

(tu/deftest-kb a-temporal-thing-has-a-time-and-a-time-is-its-own
  (testing "TimeOfFn ships with its corresponding predicate"
    (is (true? (v/ask? kb '(functionCorrespondingPredicate TimeOfFn timeOf) 'CxUniverse)))
    (is (true? (v/ask? kb '(reifiable_function TimeOfFn) 'CxUniverse)))
    (is (true? (v/ask? kb '(arg TimeOfFn 1 temporal) 'CxUniverse)))
    (is (true? (v/ask? kb '(result TimeOfFn time) 'CxUniverse)))
    (is (true? (v/ask? kb '(arg timeOf 1 temporal) 'CxUniverse)))
    (is (true? (v/ask? kb '(arg timeOf 2 time) 'CxUniverse))))
  (testing "a time is its own time, so the function names it"
    (tu/with-terms [Afternoon]
      (v/assert kb (list 'time_interval Afternoon) 'CxUniverse)
      (is (true? (v/ask? kb (list 'timeOf Afternoon Afternoon) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'time_interval (list 'TimeOfFn Afternoon)) 'CxUniverse))))))

;; ---- the upper divisions by location and by mass --------------------------
;; Two partitions of `thing`.  `spatial` / `aspatial` divides by a location in SOME space —
;; physical space, or a mathematical one, where a line or a square of an abstract board
;; has a location and none in the world.  `tangible` / `intangible` divides by mass.
;; `spatiotemporal` is below `physical` and `temporal`, and so below `spatial`: what has a
;; location in physical space and time.  CxUniverse states the edges as `genl` edges and not
;; as an intersection, so a thing stated spatial and temporal is not concluded
;; spatiotemporal; `nowhere_never` is
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

;; `physical` is `spatial` narrowed to the physical space of our universe.  spatiotemporal
;; is by definition what is physical and temporal, and CxUniverse places it below both by
;; genl edges and not by an intersection, so neither the membership nor its negation is
;; concluded from the two types.

(tu/deftest-kb spatiotemporal-is-below-physical-and-physical-below-spatial
  (is (true? (v/genl? kb 'physical 'spatial)))
  (is (true? (v/genl? kb 'spatiotemporal 'physical)))
  (is (true? (v/genl? kb 'spatiotemporal 'temporal)))
  (is (true? (v/genl? kb 'tangible 'physical))))

(tu/deftest-kb a-tangible-individual-is-physical-and-spatial
  (tu/with-terms [Pebble]
    (v/assert kb (list 'tangible Pebble) 'CxUniverse)
    (is (true? (v/ask? kb (list 'physical Pebble) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'spatial Pebble) 'CxUniverse)))))

(tu/deftest-kb something-physical-and-temporal-is-not-concluded-spatiotemporal
  (is (true? (v/genl? kb 'spatiotemporal 'physical)))
  (tu/with-terms [CxPond Puddle]
    (v/assert kb (list 'genlCx CxPond 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'physical Puddle) CxPond)
    (v/assert kb (list 'temporal Puddle) CxPond)
    (is (not (v/ask? kb (list 'spatiotemporal Puddle) CxPond)))
    (is (not (v/ask? kb (list 'not (list 'spatiotemporal Puddle)) CxPond)))))

(tu/deftest-kb a-line-in-the-plane-is-not-concluded-physical
  ;; Located in the Cartesian plane and in no time, the line y=x is spatial and atemporal.
  (is (true? (v/genl? kb 'physical 'spatial)))
  (tu/with-terms [Diagonal]
    (v/assert kb (list 'spatial Diagonal) 'CxUniverse)
    (v/assert kb (list 'atemporal Diagonal) 'CxUniverse)
    (is (not (v/ask? kb (list 'physical Diagonal) 'CxUniverse)))
    (is (not (v/ask? kb (list 'not (list 'physical Diagonal)) 'CxUniverse)))))

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
      "the partition separates spatiotemporal from aspatial through physical's genl to spatial")
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
  ;; Each of these is entailed by the partitions: a part of a partition is under its whole,
  ;; and the parts are disjoint, which descends to predicate through truth_valued_relation.  A fact entailed by a stated
  ;; fact is not stated as well, so CxUniverse carries none of the three.
  (let [stated (set (map (comp first text/peel-form)
                         (upper-forms)))]
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
  ;; OE 6: forall, thereExists and exists are declared quantifier instances in CxUniverse —
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
  (testing "sign_value is closed-extent too (measure.txt, beside its three instances)"
    (is (v/ask? kb (list 'not (list 'sign_value 'Muffet)) 'CxUniverse))))

(tu/deftest-kb the-closed-extent-grants-pass-the-integrity-sweep
  ;; New vocabulary is swept with kb-integrity over its own terms, in the context that
  ;; declares it.  The review-only :missing-arg pass reports every undeclared position,
  ;; and each position of the six grants is declared.
  (let [terms '#{closedExtentForArg closedExtentForArg1 closedExtentForArg2 closedExtentForArg3
                 closedExtentForArg4 closedExtentForArg5}]
    (is (= :audited (:status (v/kb-integrity kb terms 'CxUniverse)))
        "the default passes find nothing")
    (let [missing (:missing-arg (v/kb-integrity kb terms 'CxUniverse {:categories #{:missing-arg}}))]
      (is (empty? (for [{:keys [predicate missing]} missing
                        :when (contains? terms predicate)
                        i     missing]
                    [predicate i]))
          "every position of the six grants is declared"))))

(tu/deftest-kb what-has-no-place-in-space-or-time-has-no-mass
  ;; Mass entails a location in space and time, so what lacks either lacks mass.
  (is (true? (v/genl? kb 'aspatial 'intangible)))
  (is (true? (v/genl? kb 'atemporal 'intangible)))
  (tu/with-terms [Prime]
    (v/assert kb (list 'atemporal Prime) 'CxUniverse)
    (is (true? (v/ask? kb (list 'intangible Prime) 'CxUniverse)))
    (is (true? (tu/stored-in-clash? kb (list 'tangible Prime) 'CxUniverse)))))

(tu/deftest-kb a-fluent-may-be-located
  ;; A boulder rolling and thin ice are held states with a place, so nothing separates
  ;; fluent from spatial.
  (is (not (v/disjoint? kb 'fluent 'spatial 'CxUniverse)))
  (is (not (v/genl? kb 'fluent 'aspatial 'CxUniverse)))
  (tu/with-terms [ThinIce]
    (v/assert kb (list 'fluent ThinIce) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'spatial ThinIce) 'CxUniverse)))))

(tu/deftest-kb a-quantity-is-in-time-causes-nothing-and-is-no-situation
  ;; A water level is a magnitude that changes over time.  It causes nothing itself, and
  ;; the level being 3 m is a fluent about it rather than the quantity.
  (doseq [ctx '[CxUniverse]]
    (testing (str ctx)
      (is (true? (v/genl? kb 'quantity 'temporal ctx)))
      (is (true? (v/genl? kb 'quantity 'acausal ctx)))
      (is (true? (v/disjoint? kb 'quantity 'situation ctx)))
      (is (true? (v/disjoint? kb 'quantity 'fluent ctx)))))
  (tu/with-terms [WaterLevel]
    (v/assert kb (list 'quantity WaterLevel) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'fluent WaterLevel) 'CxUniverse)))))

(tu/deftest-kb a-sign-value-is-in-no-space-and-at-no-time
  (is (true? (v/genl? kb 'sign_value 'nowhere_never 'CxUniverse)))
  (doseq [t '[aspatial atemporal intangible]]
    (is (true? (v/ask? kb (list t 'SignPositive) 'CxUniverse)) (str "SignPositive is " t))))

(defn- located-or-not
  "Each [kind side witness] row: the pair is stated orthogonal in CxUniverse, reads
  :orthogonal, and an individual of the kind that is also of the side is no clash."
  [kb rows]
  (doseq [[a b witness] rows]
    (testing (str a " and " b)
      (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'orthogonal a b) 'CxUniverse))
          (str "(orthogonal " a " " b ") is stated"))
      (is (= :orthogonal (v/subsumption-status kb a b)))
      (let [w (tu/fresh-term :individual witness)]
        (v/assert kb (list a w) 'CxUniverse)
        (is (not (tu/stored-in-clash? kb (list b w) 'CxUniverse)) (str "a " a " that is " b))))))

(tu/deftest-kb a-situation-or-a-held-state-may-be-located-nowhere
  ;; A debt owed or a treaty in force is located nowhere; a cat on a mat is located.
  (located-or-not kb '[[situation aspatial Debt1]
                       [static_situation spatial CatOnMat1]
                       [static_situation aspatial TreatyInForce1]]))

(tu/deftest-kb an-event-is-temporal-and-may-or-may-not-be-located
  ;; The battle of Waterloo is located; a contract expiring at midnight is not.
  (is (true? (v/genl? kb 'event 'temporal 'CxUniverse)) "an event is temporal through situation")
  (is (not-any? #(v/premise? kb (:id %)) (v/sentexes-matching kb '(genl event temporal) '?ctx))
      "and the edge is not stated")
  (located-or-not kb '[[event spatial Waterloo1] [event aspatial ContractExpiry1]]))

(tu/deftest-kb an-event-and-a-held-state-may-or-may-not-be-spatiotemporal
  ;; A battle is an event and spatiotemporal, and a contract expiring is an event and not.
  ;; A cat on a mat is a held state and spatiotemporal, and a treaty in force is one and not.
  (located-or-not kb '[[event spatiotemporal Battle2]
                       [static_situation spatiotemporal CatOnMat2]]))

;; ---- hollow: what a thing is shaped like, not what it is for ---------------
;; `hollow` holds of a thing while it has an interior space that other things can occupy.
;; It says nothing about what the thing is used for.  A container is made and hollow.

(tu/deftest-kb hollow-is-a-shape-located-in-space-and-time
  (is (true? (v/genl? kb 'hollow 'spatiotemporal 'CxUniverse)))
  (is (seq (v/sentexes-matching kb '(comment hollow ?text) 'CxUniverse)))
  (testing "a cup, a pitcher plant and a cupped hand are hollow; stuff is not"
    (is (= :orthogonal (v/subsumption-status kb 'hollow 'made)))
    (is (= :orthogonal (v/subsumption-status kb 'hollow 'organism)))
    (is (= :orthogonal (v/subsumption-status kb 'hollow 'body_part)))
    (is (true? (v/disjoint? kb 'hollow 'substance)))
    (is (true? (v/disjoint? kb 'hollow 'nowhere_never))))
  (testing "a hollow organism is no clash"
    (tu/with-terms [PitcherPlant]
      (v/assert kb (list 'organism PitcherPlant) 'CxUniverse)
      (is (not (tu/stored-in-clash? kb (list 'hollow PitcherPlant) 'CxUniverse))))))

(tu/deftest-kb a-wing-is-never-fur
  ;; A bat's wing has fur on it, and the fur is part of the wing.  That is parthood, not
  ;; one thing in both types, so wing and fur are stated disjoint.
  (is (true? (v/disjoint? kb 'wing 'fur)))
  (is (= :disjoint (v/subsumption-status kb 'wing 'fur)))
  (testing "a fur-covered wing is no clash"
    (tu/with-terms [BatWing BatFur]
      (v/assert kb (list 'wing BatWing) 'CxUniverse)
      (v/assert kb (list 'fur BatFur) 'CxUniverse)
      (is (not (tu/stored-in-clash? kb (list 'tangiblePartOf BatFur BatWing) 'CxUniverse)))))
  (testing "one thing in both types clashes"
    (tu/with-terms [Furwing]
      (v/assert kb (list 'wing Furwing) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'fur Furwing) 'CxUniverse)))))

(tu/deftest-kb a-biological-thing-can-be-hollow
  ;; A pitcher plant and a lab-grown bladder are biological and hollow.  A cup and a cave
  ;; are hollow and not biological, and a leaf is biological and not hollow.
  (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb '(orthogonal biological hollow) 'CxUniverse)))
  (is (= :orthogonal (v/subsumption-status kb 'biological 'hollow)))
  (tu/with-terms [LabBladder1]
    (v/assert kb (list 'body_part LabBladder1) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'hollow LabBladder1) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'hollow LabBladder1) 'CxUniverse)))))

(tu/deftest-kb a-container-is-made-and-hollow
  (doseq [t '[made hollow]]
    (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'genl 'container t) 'CxUniverse))
        (str "(genl container " t ") is stated"))
    (is (true? (v/genl? kb 'building t 'CxUniverse)) (str "building genl " t " through container")))
  (testing "a container stays clear of organism, person and substance"
    (doseq [t '[organism person substance]]
      (is (true? (v/disjoint? kb 'container t)) (str "container and " t))))
  (testing "a made hollow organism is no clash, and is not concluded a container"
    ;; A potted pitcher plant is made, hollow and an organism.
    (tu/with-terms [PottedPitcherPlant]
      (v/assert kb (list 'organism PottedPitcherPlant) 'CxUniverse)
      (v/assert kb (list 'made PottedPitcherPlant) 'CxUniverse)
      (is (not (tu/stored-in-clash? kb (list 'hollow PottedPitcherPlant) 'CxUniverse)))
      (is (not (true? (v/ask? kb (list 'container PottedPitcherPlant) 'CxUniverse)))))))

(tu/deftest-kb a-spatial-event-is-an-event-located-in-some-space
  (is (seq (v/sentexes-matching kb '(comment spatial_event ?text) 'CxUniverse)))
  (doseq [t '[event spatial spatiotemporal temporal situation]]
    (is (true? (v/genl? kb 'spatial_event t 'CxUniverse)) (str "spatial_event genl " t)))
  (tu/with-terms [Smelting1 Waterloo1]
    (v/assert kb (list 'spatial_event Smelting1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'spatiotemporal Smelting1) 'CxUniverse)))
    (v/assert kb (list 'event Waterloo1) 'CxUniverse)
    (v/assert kb (list 'spatial Waterloo1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'spatial_event Waterloo1) 'CxUniverse))
        "an event located in some space is a spatial event")))

(def ^:private aspatial-kinds
  "The kinds with no location in any space."
  '#{quantity organization context language})

(tu/deftest-kb a-kind-with-no-location-in-any-space-is-disjoint-from-spatial
  (doseq [kind    (sort aspatial-kinds)
          ctx     '[CxUniverse CxWell]
          located '[spatial spatiotemporal]]
    (is (true? (v/disjoint? kb kind located ctx)) (str kind " and " located " in " ctx)))
  (testing "a spatial relation between a quantity and an organization derives two clashes"
    ;; Forced to the entailing reading: the clash sides are the minted (spatial X), and
    ;; the constraint-only reading refuses the northOf instead.
    (tu/with-entailing
      (tu/with-terms [WaterLevel AcmeCo]
        (v/assert kb (list 'quantity WaterLevel) 'CxUniverse)
        (v/assert kb (list 'organization AcmeCo) 'CxUniverse)
        (v/assert kb (list 'northOf WaterLevel AcmeCo) 'CxUniverse)
        (let [clashes (into #{} (comp (filter #(= :disjoint (:kind %)))
                                      (map #(into #{} (map :sentence) (:sides %))))
                            (v/contradictions kb))]
          (is (contains? clashes #{(list 'quantity WaterLevel) (list 'spatial WaterLevel)}))
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
  ;; Every partition is a cover and a separation, so CxUniverse says so with two sub-relation
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
  '[[genl aspatial thing CxUniverse "partition thing spatial aspatial"]
    [genl spatiotemporal spatial CxUniverse "spatiotemporal genl physical genl spatial"]
    [disjoint spatiotemporal aspatial CxUniverse "spatiotemporal genl physical genl spatial; partition thing spatial aspatial"]
    [genl intangible thing CxUniverse "partition thing tangible intangible"]
    [genl nowhere_never intangible CxUniverse "nowhere_never genl aspatial genl intangible"]
    [genl organization intangible CxUniverse "organization genl aspatial genl intangible"]
    [genl context intangible CxUniverse "context genl nowhere_never genl aspatial genl intangible"]
    [genl language intangible CxUniverse "language genl nowhere_never genl aspatial genl intangible"]
    [genl number thing CxUniverse "number genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl keyword thing CxUniverse "keyword genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl boolean thing CxUniverse "boolean genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl character thing CxUniverse "character genl unrepresented_term genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl denotational_term thing CxUniverse "denotational_term genl closed_expression genl expression genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl formula thing CxUniverse "formula genl linguistic genl nowhere_never genl aspatial; partition thing spatial aspatial"]
    [genl quantity intangible CxUniverse "quantity genl aspatial genl intangible"]
    [genl temporal thing CxUniverse "partition thing temporal atemporal"]
    [genl atemporal thing CxUniverse "partition thing temporal atemporal"]
    [disjoint temporal atemporal CxUniverse "partition thing temporal atemporal"]
    [genl causal thing CxUniverse "partition thing causal acausal"]
    [genl acausal thing CxUniverse "partition thing causal acausal"]
    [disjoint causal acausal CxUniverse "partition thing causal acausal"]
    [genl sign_value thing CxUniverse "sign_value genl nowhere_never genl intangible genl thing"]
    [genl spatiotemporal thing CxUniverse "spatiotemporal genl physical genl spatial, spatial genl thing (partition)"]
    [genl organism tangible CxUniverse "organism genl biological genl tangible"]
    [genl body_part tangible CxUniverse "body_part genl biological genl tangible"]
    [genl body_part biological CxUniverse "separating biological organism body_part"]
    [disjoint organism substance CxUniverse "organism genl biological; disjoint biological substance"]
    [disjoint substance body_part CxUniverse "body_part genl biological; disjoint biological substance"]
    [genl tangible temporal CxUniverse "tangible genl spatiotemporal genl temporal"]
    [disjoint tangible intangible CxUniverse "partition thing tangible intangible"]
    [disjoint organization substance CxUniverse "organization genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint language substance CxUniverse "language genl nowhere_never genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint organization animal CxUniverse "organization genl aspatial genl intangible, animal genl organism genl biological genl tangible; partition thing tangible intangible"]
    [genl string intangible CxUniverse "string genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl number intangible CxUniverse "number genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl keyword intangible CxUniverse "keyword genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl boolean intangible CxUniverse "boolean genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl character intangible CxUniverse "character genl unrepresented_term genl linguistic genl nowhere_never genl intangible"]
    [genl building made CxUniverse "building genl container genl made"]
    [genl building hollow CxUniverse "building genl container genl hollow"]
    [genl made tangible CxUniverse "partition tangible made natural"]
    [genl natural tangible CxUniverse "partition tangible made natural"]
    [genl formation tangible CxUniverse "formation genl natural genl tangible"]
    [disjoint formation made CxUniverse "formation genl natural; partition tangible made natural"]
    [disjoint formation organism CxUniverse "organism genl biological; separating tangible formation biological"]
    [disjoint formation body_part CxUniverse "body_part genl biological; separating tangible formation biological"]
    [genl asymmetric binary_predicate CxUniverse "asymmetric genl anti_symmetric genl binary_predicate"]
    [disjoint string predicate CxUniverse "string genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint number predicate CxUniverse "number genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint keyword predicate CxUniverse "keyword genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint boolean predicate CxUniverse "boolean genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint character predicate CxUniverse "character genl unrepresented_term, predicate genl relation; unrepresented_term genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint glass_stuff stone CxUniverse "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal_stuff glass_stuff CxUniverse "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal_stuff stone CxUniverse "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal_stuff wood CxUniverse "disjoint_metatype stuff_type_by_substance"]
    [disjoint wood glass_stuff CxUniverse "disjoint_metatype stuff_type_by_substance"]
    [disjoint wood stone CxUniverse "disjoint_metatype stuff_type_by_substance"]
    [genl reifiable_function function CxUniverse "partition function reifiable_function unreifiable_function"]
    [genl unreifiable_function function CxUniverse "partition function reifiable_function unreifiable_function"]
    [genl fixed_order_type unary_predicate CxUniverse "partition unary_predicate fixed_order_type variable_order_type"]
    [genl variable_order_type unary_predicate CxUniverse "partition unary_predicate fixed_order_type variable_order_type"]
    [genl equivalence_relation binary_predicate CxUniverse "intersection equivalence_relation reflexive symmetric transitive; reflexive genl binary_predicate"]
    [genl linguistic nowhere_never CxUniverse "separating nowhere_never logical linguistic quantitative"]
    [genl relation nowhere_never CxUniverse "separating logical relation context; separating nowhere_never logical linguistic quantitative"]
    [genl context nowhere_never CxUniverse "separating logical relation context; separating nowhere_never logical linguistic quantitative"]
    [genl measure nowhere_never CxUniverse "measure genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [disjoint linguistic relation CxUniverse "relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint linguistic measure CxUniverse "measure genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [disjoint measure relation CxUniverse "measure genl quantitative, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint relation context CxUniverse "separating logical relation context"]
    [genl unit_of_measure nowhere_never CxUniverse "unit_of_measure genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [genl physical_dimension nowhere_never CxUniverse "physical_dimension genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [genl sign_value nowhere_never CxUniverse "sign_value genl quantitative; separating nowhere_never logical linguistic quantitative"]
    [disjoint unit_of_measure relation CxUniverse "unit_of_measure genl quantitative, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint physical_dimension relation CxUniverse "physical_dimension genl quantitative, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [genl proposition nowhere_never CxUniverse "separating logical relation proposition context; separating nowhere_never logical linguistic quantitative"]
    [disjoint proposition linguistic CxUniverse "proposition genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint proposition relation CxUniverse "separating logical relation proposition context"]
    [disjoint expression relation CxUniverse "expression genl linguistic, relation genl logical; separating nowhere_never logical linguistic quantitative"]
    [disjoint expression context CxUniverse "expression genl linguistic, context genl logical; separating nowhere_never logical linguistic quantitative"]])

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
;; convicting nothing for the life of the KB.  These assert the modelling half of that: the
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

(tu/deftest-kb a-string-and-a-predicate-of-one-term-are-an-irreducible-conflict
  ;; `string` and `predicate` are both forced-monotonic term kinds, so the
  ;; clash `(disjoint linguistic relation)` makes of them through their genl edges has no
  ;; member to defeat: both stay believed and `conflicts` names the pair, the same in
  ;; either order
  (doseq [[first-kind second-kind] '[[string predicate] [predicate string]]]
    (tu/with-terms [Thing1]
      (v/assert kb (list first-kind Thing1) 'CxUniverse)
      (v/assert kb (list second-kind Thing1) 'CxUniverse)
      (is (v/ask? kb (list 'string Thing1) 'CxUniverse)
          (str second-kind " after " first-kind ": string stays believed"))
      (is (v/ask? kb (list 'predicate Thing1) 'CxUniverse))
      (let [hs (v/handle-of kb (list 'string Thing1) 'CxUniverse)
            hp (v/handle-of kb (list 'predicate Thing1) 'CxUniverse)]
        (is (some #(= #{hs hp} (set (:nogood %))) (v/conflicts kb))
            "and the pair is reported as a conflict")))))

;; ---- what is biological ---------------------------------------------------
;; An organism and a part it grew are both biological, and tangible through it.  The two
;; are separated without being said to exhaust biological.

(tu/deftest-kb an-organism-and-a-body-part-are-biological-and-tangible
  (doseq [t '[organism body_part]]
    (is (true? (v/genl? kb t 'biological)) (str t " is biological"))
    (is (true? (v/genl? kb t 'tangible)) (str t " is tangible through biological")))
  (is (true? (v/genl? kb 'biological 'tangible)))
  (testing "a kind organism.txt places reaches tangible in CxUniverse"
    (is (true? (v/genl? kb 'animal 'tangible 'CxUniverse))))
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

(tu/deftest-kb a-function-is-not-a-truth-valued-relation
  ;; (partition relation function truth_valued_relation), read off a function stated as
  ;; one and off a relation denied the other part; three-partitions-divide-relation
  ;; asserts the separation half.  A denial of the forced-monotonic truth_valued_relation
  ;; is believed while no (truth_valued_relation X) is stored.
  (tu/with-terms [relatesTo deniedRelation]
    (v/assert kb (list 'relation relatesTo) 'CxUniverse)
    (v/assert kb (list 'function relatesTo) 'CxUniverse)
    (is (false? (v/ask? kb (list 'truth_valued_relation relatesTo) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'not (list 'truth_valued_relation relatesTo)) 'CxUniverse))
        "a function is refuted as a truth_valued_relation")
    (is (= :false (:verdict (v/argue kb (list 'truth_valued_relation relatesTo) 'CxUniverse))))
    (testing "a relation denied truth_valued_relation is concluded a function by the cover"
      (v/assert kb (list 'relation deniedRelation) 'CxUniverse)
      (v/assert kb (list 'not (list 'truth_valued_relation deniedRelation)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'function deniedRelation) 'CxUniverse))))))

(tu/deftest-kb reifiable-and-unreifiable-partition-function
  (is (true? (v/disjoint? kb 'reifiable_function 'unreifiable_function 'CxUniverse)))
  (is (true? (v/genl? kb 'reifiable_function 'function 'CxUniverse)))
  (is (true? (v/genl? kb 'unreifiable_function 'function 'CxUniverse))))

(tu/deftest-kb fixed-and-variable-order-partition-unary-predicate
  (is (true? (v/disjoint? kb 'fixed_order_type 'variable_order_type 'CxUniverse)))
  (is (true? (v/genl? kb 'fixed_order_type 'unary_predicate 'CxUniverse)))
  (is (true? (v/genl? kb 'variable_order_type 'unary_predicate 'CxUniverse)))
  (testing "so a type of one order is never of variable order"
    (is (true? (v/disjoint? kb 'metatype 'variable_order_type 'CxUniverse)))))

(tu/deftest-kb an-equivalence-relation-is-the-intersection-of-its-three-marks
  (is (true? (v/genl? kb 'equivalence_relation 'reflexive 'CxUniverse)))
  (is (true? (v/genl? kb 'equivalence_relation 'symmetric 'CxUniverse)))
  (is (true? (v/genl? kb 'equivalence_relation 'transitive 'CxUniverse)))
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

(tu/deftest-kb static-situations-and-events-partition-uninterrupted-situation
  ;; The intersections defining static_situation and event separate them; the stated
  ;; partition of uninterrupted_situation adds the coverage.
  (is (true? (v/disjoint? kb 'static_situation 'event)))
  (testing "an uninterrupted situation that is not an event is a static_situation — the coverage half"
    (tu/with-terms [Drought]
      (v/assert kb (list 'uninterrupted_situation Drought) 'CxUniverse)
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
  ;; The seven biology properties life.txt places under biological, organism and animal are
  ;; states and capacities of an organism rather than kinds of one, so they are left out: each
  ;; crosses the folk taxonomy, and its pairs with it stay unknown.  Two life stages of one
  ;; kind (caterpillar and butterfly) are neither: one organism is both, one after the other,
  ;; so their pair is left unknown on purpose and only pairs of stages of a kind are skipped.
  (let [props   '#{alive dead mortal asleep awake breathes_air warm_blooded}
        org     (set (remove props (filter #(v/genl? kb % 'organism) (v/types kb))))
        stage-of (fn [s] (set (for [r '[larvalFormOf adultFormOf]
                                    k org
                                    :when (v/ask? kb (list r s k) B)]
                                k)))
        same-kind-stages? (fn [a b] (boolean (some (stage-of a) (stage-of b))))
        unknown (for [{:keys [a b status]} (:pairs-data (v/disjointness-audit kb))
                      :when (and (org a) (org b) (= :unknown status)
                                 (not (same-kind-stages? a b)))]
                  (set [a b]))]
    (is (every? org folk-species) "every species is an organism")
    (is (true? (v/disjoint? kb 'grass 'oak)) "grass is not a tree, so not an oak")
    (is (= [] (vec unknown)))))

;; ---- folk_species is forced-monotonic ------------------------
;; A species membership is definitional, so CxUniverse writes each :monotonic and a rule
;; concluding a forced-monotonic literal from one alone fires as a forced-monotonic rule.

(tu/deftest-kb a-folk-species-membership-is-held-monotonic
  (is (= :monotonic (v/defeat-class kb (v/handle-of kb '(folk_species dog) 'CxUniverse))))
  (testing "a denial of one loses to it"
    (let [d (v/assert kb '(not (folk_species dog)) 'CxUniverse)]
      (is (not (v/in? kb d)))
      (is (true? (v/ask? kb '(folk_species dog) 'CxUniverse))))))

(tu/deftest-kb a-rule-from-folk-species-to-orthogonal-is-a-forced-monotonic-rule
  ;; A rule that declares every species orthogonal to a kind of tangible thing:
  ;; its one antecedent is a forced-monotonic literal, so its firings are believed rather than held
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

(tu/deftest-kb artifact-is-declared-nowhere-and-the-made-kinds-are-made
  ;; The KB declares no artifact term and no alias for one.  building, clothing,
  ;; container, electronic_device, furniture, machine and vehicle are kinds of made.
  (is (empty? (v/sentexes-matching kb '(comment artifact ?text) '?ctx)))
  (is (empty? (v/sentexes-matching kb '(genl artifact ?type) '?ctx)))
  (is (empty? (v/sentexes-matching kb '(genl ?type artifact) '?ctx)))
  (is (= 1 (count (v/sentexes-matching kb '(comment made ?text) 'CxUniverse))))
  (doseq [t '[building clothing container electronic_device furniture machine vehicle]]
    (is (true? (v/genl? kb t 'made 'CxUniverse)) (str t " is made")))
  (doseq [t '[clothing container electronic_device furniture machine vehicle]]
    (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'genl t 'made) 'CxUniverse))
        (str "(genl " t " made) is stated"))))

(tu/deftest-kb an-electronic-device-is-made-and-overlaps-machine
  ;; electronic_device is defined by the circuit it contains.  A fan-cooled desktop is a
  ;; machine and an electronic device, a wind-up clock a machine with no circuit, and a
  ;; single-board computer an electronic device with no moving part that does work.
  (is (= 1 (count (v/sentexes-matching kb '(comment electronic_device ?text) 'CxUniverse))))
  (is (true? (v/genl? kb 'electronic_device 'made 'CxUniverse)))
  (is (some #(v/premise? kb (:id %))
            (v/sentexes-matching kb '(orthogonal electronic_device machine) 'CxUniverse))
      "(orthogonal electronic_device machine) is stated")
  (is (= 1 (count (v/sentexes-matching
                   kb '(comment (orthogonal electronic_device machine) ?text) 'CxUniverse)))
      "the orthogonal sentence carries its witnesses as a comment")
  (is (= :orthogonal (v/subsumption-status kb 'machine 'electronic_device)))
  (is (not (v/disjoint? kb 'machine 'electronic_device)))
  (testing "a term in both types is no clash"
    (tu/with-terms [Desktop1]
      (v/assert kb (list 'machine Desktop1) 'CxUniverse)
      (is (not (tu/stored-in-clash? kb (list 'electronic_device Desktop1) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'electronic_device Desktop1) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'machine Desktop1) 'CxUniverse)))))
  (testing "a machine is not concluded an electronic device, nor the converse"
    (tu/with-terms [WindUpClock1 BoardComputer1]
      (v/assert kb (list 'machine WindUpClock1) 'CxUniverse)
      (v/assert kb (list 'electronic_device BoardComputer1) 'CxUniverse)
      (is (not (v/ask? kb (list 'electronic_device WindUpClock1) 'CxUniverse)))
      (is (not (v/ask? kb (list 'machine BoardComputer1) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'made BoardComputer1) 'CxUniverse)))
      (is (not (v/ask? kb (list 'person BoardComputer1) 'CxUniverse))
          "an electronic device is not concluded a person"))))

;; ---- mechanism ----------------------------------------------------------------
;; mechanism is the common genl of machine and electronic_device, and their shared
;; separations are stated once on it: a mechanism is never an organism and never stuff.

(tu/deftest-kb mechanism-parents-machine-and-electronic-device
  (is (= 1 (count (v/sentexes-matching kb '(comment mechanism ?text) 'CxUniverse))))
  (doseq [t '[machine electronic_device]]
    (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'genl t 'mechanism) 'CxUniverse))
        (str "(genl " t " mechanism) is stated")))
  (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb '(genl mechanism tangible) 'CxUniverse))
      "(genl mechanism tangible) is stated")
  (is (not (v/genl? kb 'mechanism 'made 'CxUniverse))
      "most mechanisms are made, not all: a mechanism is not concluded made")
  (doseq [t '[organism substance]]
    (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'disjoint 'mechanism t) 'CxUniverse))
        (str "(disjoint mechanism " t ") is stated"))
    (doseq [k '[mechanism machine electronic_device]]
      (is (true? (v/disjoint? kb k t)) (str k " is disjoint with " t))))
  (is (empty? (v/sentexes-matching kb '(disjoint animal machine) 'CxUniverse))
      "the animal/machine separation is reached through mechanism, not restated")
  (is (true? (v/disjoint? kb 'animal 'machine)))
  (testing "an organism stated a mechanism is a clash"
    (tu/with-terms [Sheep1]
      (v/assert kb (list 'organism Sheep1) 'CxUniverse)
      (v/assert kb (list 'electronic_device Sheep1) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'electronic_device Sheep1) 'CxUniverse)))))

;; ---- made and natural ------------------------------------------------------
;; made and natural partition tangible.  A formation is a natural tangible that nothing
;; grew and nobody made.  biological is orthogonal to made and to natural.

(tu/deftest-kb made-and-natural-partition-tangible
  (is (true? (v/disjoint? kb 'made 'natural)))
  (is (true? (v/genl? kb 'made 'tangible 'CxUniverse)))
  (is (true? (v/genl? kb 'natural 'tangible 'CxUniverse)))
  (is (= 1 (count (v/sentexes-matching kb '(comment natural ?text) 'CxUniverse))))
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
  (is (true? (v/genl? kb 'formation 'natural 'CxUniverse)))
  (is (= 1 (count (v/sentexes-matching kb '(comment formation ?text) 'CxUniverse))))
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
        (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'typeOrthogonal 'origin_type a) 'CxUniverse))
            (str "(typeOrthogonal origin_type " a ") is stated"))
        (is (some #(v/premise? kb (:id %)) (v/sentexes-matching kb (list 'orthogonal a b) 'CxUniverse))
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

(tu/deftest-kb a-tangible-part-is-a-part-and-parthood-chains-across-kinds
  ;; (genl tangiblePartOf partOf) makes every tangiblePartOf tuple a partOf tuple, and
  ;; (transitive partOf) chains a tangible part with a stated broad one.
  (tu/with-terms [Piston Engine Car Fleet]
    (v/assert kb (list 'tangiblePartOf Piston Engine) 'CxUniverse)
    (v/assert kb (list 'tangiblePartOf Engine Car) 'CxUniverse)
    (v/assert kb (list 'partOf Car Fleet) 'CxUniverse)
    (is (true? (v/ask? kb (list 'partOf Piston Engine) 'CxUniverse))
        "a tangiblePartOf fact answers partOf")
    (is (true? (v/ask? kb (list 'partOf Piston Fleet) 'CxUniverse))
        "partOf's transitivity chains through its tangiblePartOf tuples")
    (is (not (v/ask? kb (list 'tangiblePartOf Piston Fleet) 'CxUniverse))
        "a broad partOf fact is not a tangiblePartOf one")))

(tu/deftest-kb a-sub-situation-is-a-part-and-a-shared-time-makes-none
  ;; subSituationOf is transitive and below partOf.  Parthood is not read off time: two
  ;; situations occupying one time are not thereby parts of one another.
  (tu/with-terms [Inning Game Series Rally Afternoon]
    (doseq [s [Inning Game Series Rally]]
      (v/assert kb (list 'situation s) 'CxUniverse))
    (v/assert kb (list 'subSituationOf Inning Game) 'CxUniverse)
    (v/assert kb (list 'subSituationOf Game Series) 'CxUniverse)
    (v/assert kb (list 'timeOf Game Afternoon) 'CxUniverse)
    (v/assert kb (list 'timeOf Rally Afternoon) 'CxUniverse)
    (is (true? (v/ask? kb (list 'subSituationOf Inning Series) 'CxUniverse))
        "subSituationOf chains")
    (is (true? (v/ask? kb (list 'partOf Inning Series) 'CxUniverse))
        "a sub-situation is a part")
    (is (not (v/ask? kb (list 'subSituationOf Rally Game) 'CxUniverse))
        "a shared time derives no subSituationOf")
    (is (not (v/ask? kb (list 'subSituationOf Game Rally) 'CxUniverse))
        "nor in the other direction")))

(tu/deftest-kb each-non-proper-parthood-relation-holds-of-a-thing-and-itself
  ;; partOf, tangiblePartOf, partOfRegion and subSituationOf each carry their own
  ;; (reflexive P) mark, since the reflexive prover reads the mark and not a genl edge.
  (tu/with-terms [Wheel]
    (doseq [p '[partOf tangiblePartOf partOfRegion subSituationOf]]
      (is (true? (v/has-prop? kb :reflexive p)) (str p " carries its own mark"))
      (is (true? (v/ask? kb (list p Wheel Wheel) 'CxUniverse)) (str p " holds of a thing and itself")))))

(tu/deftest-kb a-proper-counterpart-needs-the-reverse-tuple-denied
  ;; properCounterpart's generator: the proper tuple follows from a tuple and a believed
  ;; denial of its reverse, never from the reverse tuple being absent.
  (tu/with-terms [coversOf properCoversOf A B]
    (v/assert kb (list 'properCounterpart coversOf properCoversOf) 'CxUniverse)
    (v/assert kb (list coversOf A B) 'CxUniverse)
    (is (not (v/ask? kb (list properCoversOf A B) 'CxUniverse))
        "a reverse tuple nobody stated is not a reverse tuple denied")
    (v/assert kb (list 'not (list coversOf B A)) 'CxUniverse)
    (is (true? (v/ask? kb (list properCoversOf A B) 'CxUniverse))
        "a tuple and its denied reverse make the proper tuple")))

(tu/deftest-kb a-proper-part-is-a-part-whose-whole-is-not-part-of-it
  ;; Each non-proper parthood relation has a proper counterpart below it and below
  ;; properPartOf.  The proper tuple needs the reverse tuple denied, not merely unstated.
  (tu/with-terms [Piston Engine Car]
    (v/assert kb (list 'properTangiblePartOf Piston Engine) 'CxUniverse)
    (doseq [g [(list 'tangiblePartOf Piston Engine) (list 'properPartOf Piston Engine)
               (list 'partOf Piston Engine) (list 'not (list 'tangiblePartOf Engine Piston))]]
      (is (true? (v/ask? kb g 'CxUniverse)) (str "a proper tangible part answers " (pr-str g))))
    (v/assert kb (list 'tangiblePartOf Engine Car) 'CxUniverse)
    (is (not (v/ask? kb (list 'properTangiblePartOf Engine Car) 'CxUniverse))
        "a part whose whole is not denied to be part of it is not thereby proper")
    (v/assert kb (list 'not (list 'tangiblePartOf Car Engine)) 'CxUniverse)
    (is (true? (v/ask? kb (list 'properTangiblePartOf Engine Car) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'properTangiblePartOf Piston Car) 'CxUniverse))
        "a proper part of a proper part is a proper part")
    (is (not (v/ask? kb (list 'properPartOf Piston Piston) 'CxUniverse))
        "nothing is a proper part of itself"))
  (testing "two regions each part of the other are neither proper and stay two"
    (tu/with-terms [Lot Parcel]
      (v/assert kb (list 'partOfRegion Lot Parcel) 'CxUniverse)
      (v/assert kb (list 'partOfRegion Parcel Lot) 'CxUniverse)
      (is (not (v/ask? kb (list 'properPartOfRegion Lot Parcel) 'CxUniverse)))
      (is (not (v/ask? kb (list 'equals Lot Parcel) 'CxUniverse)))
      (is (some? (v/handle-of kb '(not (anti_symmetric partOf)) 'CxUniverse))
          "and the KB states antisymmetry declined, not merely unstated")))
  (testing "a proper region part is a proper part"
    (tu/with-terms [Plot Field]
      (v/assert kb (list 'properPartOfRegion Plot Field) 'CxUniverse)
      (is (true? (v/ask? kb (list 'properPartOf Plot Field) 'CxUniverse))))))

(tu/deftest-kb a-subinterval-is-a-part-of-a-time
  ;; subintervalOf and properSubintervalOf relate time intervals, so each is parthood:
  ;; subintervalOf is reflexive and below partOf, properSubintervalOf below properPartOf.
  (tu/with-terms [Morning Day Hour Week]
    (v/assert kb (list 'subintervalOf Morning Day) 'CxUniverse)
    (is (true? (v/ask? kb (list 'time_interval Morning) 'CxUniverse)) "its arguments are time intervals")
    (is (true? (v/ask? kb (list 'partOf Morning Day) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'subintervalOf Week Week) 'CxUniverse)))
    (v/assert kb (list 'properSubintervalOf Hour Morning) 'CxUniverse)
    (is (true? (v/ask? kb (list 'properPartOf Hour Morning) 'CxUniverse)))))

;; ---- parthood invariants ----------------------------------------------------
;; A parthood relation is either non-proper, and then reflexive, or proper, and then below
;; properPartOf.  "Proper" is read off the genl edge to properPartOf, whose definition is
;; settled, and never off a relation's name.  A spec of partOf carrying neither is
;; unclassified, and the classification never defaults one to proper.

(defn- parthood-specs
  "Every spec of partOf, at any depth, partOf included."
  [kb]
  (set (map #(get % '?s) (v/ask kb '(genl ?s partOf) 'CxUniverse))))

(defn- unclassified-parthood-specs
  "The specs of partOf marked neither reflexive nor below properPartOf, sorted."
  [kb]
  (sort (remove #(or (v/has-prop? kb :reflexive %) (v/genl? kb % 'properPartOf))
                (parthood-specs kb))))

(defn- symmetric-irreflexive-parthood-specs
  "A review flag, not a proof: the specs of partOf marked both symmetric and irreflexive,
  sorted.  Such a relation holds between distinct mutual parts, which is worth a second
  look.  A relation the flag passes is certified as nothing."
  [kb]
  (sort (filter #(and (v/has-prop? kb :symmetric %) (v/has-prop? kb :irreflexive %))
                (parthood-specs kb))))

(tu/deftest-kb every-parthood-relation-is-reflexive-or-proper
  (is (= [] (unclassified-parthood-specs kb)) "the shipped parthood relations are classified")
  (testing "a spec carrying neither mark is unclassified, whatever its name says"
    (tu/with-terms [gluedTo properGluedTo]
      (v/assert kb (list 'genl gluedTo 'tangiblePartOf) 'CxUniverse)
      (v/assert kb (list 'genl properGluedTo 'tangiblePartOf) 'CxUniverse)
      (is (= (sort [gluedTo properGluedTo]) (unclassified-parthood-specs kb)))
      (v/assert kb (list 'reflexive gluedTo) 'CxUniverse)
      (v/assert kb (list 'genl properGluedTo 'properTangiblePartOf) 'CxUniverse)
      (is (= [] (unclassified-parthood-specs kb)) "and classified once marked"))))

(tu/deftest-kb a-symmetric-irreflexive-parthood-relation-is-flagged-for-review
  (is (= [] (symmetric-irreflexive-parthood-specs kb)) "no shipped parthood relation is flagged")
  (testing "symmetric and irreflexive: distinct mutual parts, flagged for review"
    (tu/with-terms [weldedTo]
      (v/assert kb (list 'genl weldedTo 'tangiblePartOf) 'CxUniverse)
      (v/assert kb (list 'symmetric weldedTo) 'CxUniverse)
      (v/assert kb (list 'irreflexive weldedTo) 'CxUniverse)
      (is (= [weldedTo] (symmetric-irreflexive-parthood-specs kb)))))
  (testing "symmetric and reflexive, as spatiallyEqual is, is not flagged"
    (tu/with-terms [coextensiveWith]
      (v/assert kb (list 'genl coextensiveWith 'partOf) 'CxUniverse)
      (v/assert kb (list 'symmetric coextensiveWith) 'CxUniverse)
      (v/assert kb (list 'reflexive coextensiveWith) 'CxUniverse)
      (is (not-any? #{coextensiveWith} (symmetric-irreflexive-parthood-specs kb))))))
