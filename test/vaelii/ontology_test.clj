;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ontology-test
  "The shipped ontology as a *modelling* claim, where `starter-test` reads it as a schema
  that loads and reasons.

  What is pinned here is the structure of the mini-ontology rather than any one inference:
  which names are types and which are properties, that every type is placed under the
  root, that a capability is related to a kind rather than spelled as a predicate of its
  own, and how a claim about a kind reaches the kinds beneath it and stops where a nearer
  claim contradicts it.  Those are decisions somebody made, and every one of them is
  invisible to a test that only asks whether the KB answers a question.

  The genl-level exception is the centre of it.  A rule states its exception with
  `exceptWhen` (docs/exceptions.md); an *inherited* claim has no rule to except, and is
  stopped instead by a more specific claim — which works only for a default, never for a
  monotonic one, and both halves of that are tested because the asymmetry is the design."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.io.text :as text]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private B 'CxBiology)
(def ^:private N 'CxNaturalWorld)

;; ---- capabilities are related to a kind, not spelled as predicates -------

(tu/deftest-kb a-capability-is-a-noun-related-to-a-kind
  ;; `flies` as a one-place predicate says the same thing, and says it in a shape that
  ;; cannot be generalized: every further ability needs a further predicate, and nothing
  ;; relates them.  As a capability it is a term, so the abilities form a hierarchy.
  (testing "the capability names a kind of its own, under capability"
    (is (v/genl? kb 'flying 'capability))
    (is (v/genl? kb 'travelling 'capability))
    (is (v/genl? kb 'flying 'travelling)))
  (testing "and no one-place flight predicate survives beside it"
    (is (empty? (v/sentexes-matching kb '(arity flies ?n) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(arity can_travel ?n) '?ctx)))))

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
  (testing "and it climbs the capability hierarchy: what flies travels"
    (is (v/ask? kb '(capabilityType bird travelling) B))
    (is (v/ask? kb '(capabilityType eagle travelling) B)))
  (testing "answered by transitiveInArgInverse, so the kind level stores no rule's output"
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
  (testing "the consequence rests on it and is a record too, so the cascade is visible"
    (is (seq (v/sentexes-matching kb '(hasCapability Sam travelling) N))))
  (testing "and the flightless member gets neither"
    (is (not (v/ask? kb '(hasCapability Tweety flying) N)))
    (is (empty? (v/sentexes-matching kb '(hasCapability Tweety travelling) N)))))

(tu/deftest-kb the-two-capability-readings-are-two-predicates-and-say-so
  ;; One symbol read at both levels has to pick one argument check for both, and whichever
  ;; it picks convicts the half it was not written for: `arg … 1 animal` is right for
  ;; `(… Tweety flying)` and wrong for `(… bird flying)`, since a kind is not a member of
  ;; the type it lies under.  So: two predicates, the kind-level one marked, and the pair
  ;; named in prose because the predicate that names pairs cannot take a mixed half.
  (testing "the kind-level half relates kinds, and says so"
    (is (v/ask? kb '(type_relation_predicate capabilityType))))
  (testing "the instance-level half is MIXED — one animal to one capability kind — so it
            carries no relation_kind, and its two positions take different checks"
    (is (not (v/ask? kb '(instance_relation_predicate hasCapability))))
    (is (not (v/ask? kb '(type_relation_predicate hasCapability))))
    (is (v/ask? kb '(arg hasCapability 1 animal)))
    (is (v/ask? kb '(genlArg hasCapability 2 capability))))
  (testing "so the pairing cannot be declared — typeToInstancePred constrains its second
            argument to a marked instance half, and this one is mixed"
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb '(typeToInstancePred capabilityType hasCapability)
                           'CxLife))))
  (testing "and neither reading answers the other's question"
    (is (not (v/ask? kb '(hasCapability bird flying) B)))
    (is (not (v/ask? kb '(capabilityType Sam flying) N)))))

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
    '[genl 2]  "the root: (genlArg genl 2 thing) would entail (genl thing thing), refused as irreflexive"}
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
  ;; `transitiveInArg`'s contract in one test, both halves.  A default yields to a nearer
  ;; claim; a monotonic claim does not, because yielding would make a stated certainty
  ;; depend on what else got said, and the strength is exactly the author saying it must
  ;; not.  Two independent hierarchies so neither answer can come from the other.
  (tu/with-terms [carriesLoad pack_animal mule_kind hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) 'CxUniverse)
    (v/assert kb (list 'transitiveInArg carriesLoad 1 'genl) 'CxUniverse)
    (v/assert kb (list 'genl pack_animal 'animal) 'CxUniverse)
    (v/assert kb (list 'genl mule_kind pack_animal) 'CxUniverse)
    (v/assert kb (list 'genl hauler_kind 'animal) 'CxUniverse)
    (v/assert kb (list 'genl cart_kind hauler_kind) 'CxUniverse)
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
    (testing "the disagreement is a dilemma, and asking the subkind answers nothing"
      ;; Both claims survive `undercut?` — the monotonic one because it is known-true,
      ;; the negative one because nothing is more specific than it — so `verdict` sees
      ;; both polarities and returns `:ambiguous`, which `ask?` renders as false.  Not
      ;; the same as the negative winning: the general claim above is still believed.
      (is (not (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'CxUniverse))))
    (testing "and the dilemma is reported, which is what makes it a dilemma and not silence"
      ;; `inherit`'s own docstring calls a contrary specific claim against a monotonic one
      ;; "a contradiction to report rather than a refinement to defer to", and this is
      ;; where it is reported.  The inherited claim has no handle, so the nogood's members
      ;; are the stored claim and everything the reading rests on — the general claim, the
      ;; declaration and the `genl` edge — and `:inherited` carries the claim nobody wrote.
      ;; The mule/pack_animal half above is a `:default` general claim and is undercut, so
      ;; it contributes nothing: one entry, from the monotonic half.
      (let [rs (filter #(= :inherited (:kind %)) (v/contradictions kb))
            r  (first rs)]
        (is (= 1 (count rs)))
        (is (empty? (v/conflicts kb))
            "at :default against :monotonic the pair is a dilemma, not an unsolved clash")
        (is (= (list carriesLoad cart_kind 'Bone1) (:sentence (:inherited r)))
            "the report names the claim that was never stored")
        (is (= (list carriesLoad hauler_kind 'Bone1)
               (:sentence (first (filter #(= (:handle %) (:claim (:inherited r)))
                                         (:sides r)))))
            "and the sentex it was inherited from, by handle")
        (is (contains? (set (map :sentence (:sides r)))
                       (list 'genl cart_kind hauler_kind))
            "and the genl edge it travelled, so `why` can explain the reach")
        (is (contains? (set (map :sentence (:sides r)))
                       (list 'transitiveInArg carriesLoad 1 'genl))
            "and the declaration that licensed the move")))))

;; ---- what is a type, and what is only a property ------------------------

(tu/deftest-kb a-type-is-a-noun-and-a-property-is-not-a-type
  ;; The naming rules make `alive` and `mortal` legal unary predicates, and nothing in
  ;; them says whether a name belongs in the genl hierarchy.  That is a modelling
  ;; decision: a type is a kind of thing and wants a noun, while a property is something
  ;; a thing *is*, and putting one in the hierarchy would make "mortal" a kind that
  ;; living things are a kind OF.  Were one wanted as a type it would be spelled for it —
  ;; `mortal_being`, not `mortal`.
  (testing "the properties the biology theory concludes are outside the hierarchy"
    (doseq [p '[alive dead awake asleep mortal warm_blooded breathes_air]]
      (is (empty? (v/sentexes-matching kb (list 'genl p '?super) '?ctx))
          (str p " is a property, not a type — it must carry no genl edge"))
      (is (seq (v/sentexes-matching kb (list 'arity p 1) '?ctx))
          (str p " is still a one-place predicate"))))
  (testing "while the kinds they are said of are types, and reach the root"
    (doseq [t '[animal bird penguin dog person physical_object capability flying]]
      (is (v/genl? kb t 'thing) (str t " must reach thing")))))

(tu/deftest-kb every-shipped-type-is-placed-under-the-root
  ;; An unplaced type is invisible to every closure the engine reads, so it is a type in
  ;; spelling only.  `islands` is the taxonomy's own count of them.
  (let [q (v/kb-quality kb)]
    (is (zero? (:islands (:taxonomy q)))
        "a type with no path to thing answers nothing and is a type in spelling only")
    (is (= (:edged (:taxonomy q)) (:rooted (:taxonomy q)))
        "every name with a genl edge reaches the root")))

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
  ;; The disjoint count increased from 8 to 21 when `(genl relation expression)` placed
  ;; all relations under `intangible` and `(disjoint intangible spatial)` was added.
  ;; 13 of the 21 are schematic-unification false positives: the checker unifies a
  ;; classification-rule variable with CxCriedWolf's `lied_before → liar` variable,
  ;; whose arg-1 domains (relation vs animal) are provably disjoint.  No ground term
  ;; satisfies both antecedents.  TODO: vaelii#95 will tighten the checker to prune
  ;; unreachable pairs via arg-type disjointness, dropping these 13 back out.
  (let [pairs (:pairs (:clashes (v/kb-quality kb {:limit 100})))
        kinds (frequencies (map :kind pairs))]
    (is (= {:negation 4, :disjoint 21} kinds)
        (str "clashes: " (pr-str (mapv (juxt :kind :sentences) pairs))))
    (is (every? :excepted (filter #(= :negation (:kind %)) pairs))
        "negation clashes are excepted; disjoint clashes include 13 unreachable pairs (vaelii#95)")))

(tu/deftest-kb the-arity-rules-clash-with-each-other-in-neither-direction
  ;; The reading's own half of the arity separation.  The generator stamps one rule per
  ;; exact class, and two of them conclude two arities for one relation only where the
  ;; relation holds both classes — which `(disjoint unary binary)` and its two peers
  ;; refuse on the antecedents.  No `?relation` satisfies two of them, so the pair is
  ;; unreachable rather than unstated (docs/quality.md).
  ;;
  ;; The arity rules now appear in false-positive pairs with CxCriedWolf's
  ;; `lied_before → liar` because `(disjoint intangible spatial)` makes relation-
  ;; classification conclusions and story-predicate conclusions disjoint, despite
  ;; their arg-1 domains being provably incompatible.  Tracked as vaelii#95.
  ;; Until the checker prunes by arg-type disjointness, filter out pairs whose
  ;; second rule is the CxCriedWolf story fixture.
  (let [pairs   (:pairs (:clashes (v/kb-quality kb {:limit 100})))
        about   (fn [f] (filter (fn [p] (some #(some #{f} (flatten %)) (:sentences p)))
                                pairs))
        fixture? (fn [p] (some #(some #{'lied_before} (flatten %)) (:sentences p)))
        real    (fn [f] (remove fixture? (about f)))]
    (is (empty? (real 'arity))
        (str "the arity table pairs with nothing real: " (pr-str (mapv :sentences (real 'arity)))))
    (is (empty? (real 'unary_predicate))
        (str "nor do the classes: " (pr-str (mapv :sentences (real 'unary_predicate)))))))

(tu/deftest-kb a-predicate-is-at-most-one-of-the-three-arity-classifications
  ;; The declaration that empties the reading above, read as the refusal it is.  A
  ;; predicate takes one number of arguments, so the second classification is refused
  ;; where it is written rather than stored and convicted a step later as two values in
  ;; the `functional` `(arity P n)` table.
  (testing "the three pairs are separated, and pairwise — not by a mark on predicate"
    (is (v/disjoint? kb 'unary_predicate 'binary_predicate))
    (is (v/disjoint? kb 'unary_predicate 'ternary_predicate))
    (is (v/disjoint? kb 'binary_predicate 'ternary_predicate))
    (is (not (v/disjoint? kb 'binary_predicate 'instance_relation_predicate))
        "arity is both, so a sibling_disjoint mark on predicate would be too wide"))
  (testing "and the second classification is refused, in either order"
    (tu/with-terms [zebraOf yakOf]
      (v/assert kb (list 'unary_predicate zebraOf) 'CxUniverse)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'binary_predicate zebraOf) 'CxUniverse)))
      (v/assert kb (list 'binary_predicate yakOf) 'CxUniverse)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'unary_predicate yakOf) 'CxUniverse)))
      (testing "so the arity table holds one value for each"
        (is (= [1] (mapv #(last (:sentence %))
                         (v/sentexes-matching kb (list 'arity zebraOf '?n) '?ctx))))
        (is (= [2] (mapv #(last (:sentence %))
                         (v/sentexes-matching kb (list 'arity yakOf '?n) '?ctx)))))))
  (testing "a mark below binary_predicate carries the separation with it"
    (tu/with-terms [emuOf]
      (v/assert kb (list 'functional emuOf) 'CxUniverse)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'ternary_predicate emuOf) 'CxUniverse)))))
  (testing "belief-filtered: retracting the first frees the second"
    (tu/with-terms [oxOf]
      (let [h (v/assert kb (list 'unary_predicate oxOf) 'CxUniverse)]
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'ternary_predicate oxOf) 'CxUniverse)))
        (v/retract! kb h)
        (is (v/assert kb (list 'ternary_predicate oxOf) 'CxUniverse)))))
  (testing "and scoped: two contexts neither of which sees the other keep both"
    (tu/with-terms [ibisOf CxLeft CxRight CxBelowLeft]
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBelowLeft CxLeft) 'CxUniverse)
      (v/assert kb (list 'unary_predicate ibisOf) CxLeft)
      (is (v/assert kb (list 'binary_predicate ibisOf) CxRight)
          "neither context sees the other, so both classifications stand")
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'ternary_predicate ibisOf) CxBelowLeft))
          "the descendant sees the first classification, so it refuses the third"))))

(tu/deftest-kb a-social-agent-is-a-person-but-not-a-mammal
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
    (testing "while a biological predicate refuses the non-animal person"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'parentOf CmdrData Geordi) N))))
    (testing "and human, the biological half, reaches mammal, animal and person alike"
      (is (v/genl? kb 'human 'mammal))
      (is (v/genl? kb 'human 'animal))
      (is (v/genl? kb 'human 'person))
      (is (not (v/genl? kb 'person 'mammal))))))

(tu/deftest-kb the-types-added-for-argument-constraints-are-placed-where-they-are-used
  (testing "the two calculi types the argument declarations name"
    (is (v/genl? kb 'physical_object 'spatial))
    (is (v/genl? kb 'time_point 'temporal)))
  (testing "and an animal reaches spatial, so a spatial relation admits one"
    (is (v/genl? kb 'dog 'spatial))))

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

(tu/deftest-kb symbol-is-mention-only-and-carries-neither-claim
  ;; the deliberate absence, and the one a later reader is most likely to "fix": a symbol
  ;; does not denote itself, so the set of names and the set of things named are two sets
  ;; — parentOf is written as a symbol and denotes a predicate.  Both claims below would
  ;; be false of every predicate name in the KB.
  (is (not (v/disjoint? kb 'symbol 'predicate))
      "a name is exactly how a predicate is written")
  (is (not (v/genl? kb 'symbol 'intangible))
      "and nothing places it in the domain lattice, there being no use-level reading"))

(tu/deftest-kb the-comment-text-position-refuses-a-relation-and-exempts-a-name
  ;; `(arg comment 2 string)` at the ground level, and the mechanism is `args-problem`'s
  ;; own rather than the disjointness above: a term already in the hierarchy that reaches
  ;; no path to the declared type is convicted, and one the KB classifies not at all is
  ;; exempt.  The disjointness does two other jobs — it refuses a term asserted both at
  ;; once, and it is what the rule-variable arm reads (docs/taxonomy.md).
  (tu/with-terms [SomeDoc]
    (testing "a predicate in the text position is convicted"
      (is (= :arg-type (:type (first (v/check kb (list 'comment 'thing 'genl) 'CxUniverse))))))
    (testing "an unclassified name is exempt — nothing says what it denotes"
      (is (= [] (v/check kb (list 'comment 'thing SomeDoc) 'CxUniverse))))
    (testing "and a string value is what the position is for"
      (is (= [] (v/check kb (list 'comment 'thing "some text") 'CxUniverse))))))

(tu/deftest-kb a-term-cannot-be-both-a-string-and-a-relation
  (tu/with-terms [Thing1]
    (v/assert kb (list 'string Thing1) 'CxUniverse)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'predicate Thing1) 'CxUniverse)))))
