;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.naming-test
  "Pure unit tests for the naming invariants, plus the KB-level policy that decides how
  hard they are enforced."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.test-util :as tu]))

(deftest temp-terms-are-valid-and-debuggable
  (testing "the role is inferred from the symbol's own shape"
    (is (= :type       (tu/term-role 'dog)))
    (is (= :individual (tu/term-role 'Muffet)))
    (is (= :predicate  (tu/term-role 'parentOf)))
    (is (= :context    (tu/term-role 'StoryContext))))
  (tu/with-terms [dog Muffet parentOf StoryContext]
    (testing "each generated term satisfies the invariant for its role"
      (is (nm/type-symbol? dog))
      (is (nm/individual? Muffet))
      (is (nm/predicate? parentOf))
      (is (nm/context? StoryContext))
      (is (empty? (nm/problems (list dog Muffet) StoryContext))))
    (testing "and embeds the symbol it was named after, so a failure is readable"
      (is (re-find #"dog"      (name dog)))
      (is (re-find #"Muffet"     (name Muffet)))
      (is (re-find #"ParentOf" (name parentOf)))
      (is (re-find #"Story"    (name StoryContext))))
    (testing "a type temp named after a bare word stays as ambiguous as the word"
      ;; `dog` satisfies both conventions and is disambiguated by arity, so the temp
      ;; is spelled to be usable either way — underscores would pin it to arity 1
      (is (nm/predicate? dog))
      (is (empty? (nm/problems (list dog Muffet) StoryContext)))
      (is (empty? (nm/problems (list dog Muffet Muffet) StoryContext))))
    (testing "roles stay distinct — a context is not an individual"
      (is (not (nm/individual? StoryContext)))))
  (testing "a base spelled snake_case is a type and only a type"
    (let [t (tu/fresh-term :type "physical object")]
      (is (nm/type-symbol? t))
      (is (not (nm/predicate? t)))
      (is (empty? (nm/problems (list t 'Rock1) 'WellContext)))
      (is (seq (nm/problems (list t 'Rock1 'Rock2) 'WellContext)))))
  (testing "the same name twice still yields distinct terms"
    (is (not= (tu/fresh-term :type "dog") (tu/fresh-term :type "dog")))))

(deftest role-predicates
  (testing "contexts"
    (is (nm/context? 'UniverseContext))
    (is (not (nm/context? 'Universe))))
  (testing "individuals are CapitalCamelCase but not contexts"
    (is (nm/individual? 'Muffet))
    (is (not (nm/individual? 'dog)))
    (is (not (nm/individual? 'UniverseContext))))
  (testing "predicates are camelCase, types are snake_case"
    (is (nm/predicate? 'parentOf))
    (is (nm/type-symbol? 'physical_object))
    (is (not (nm/predicate? 'physical_object)))          ; underscore ⇒ not a predicate
    (is (not (nm/type-symbol? 'parentOf)))))             ; uppercase ⇒ not snake_case

(deftest a-bare-lowercase-word-satisfies-both-conventions
  ;; The footing of the whole arity coupling: `problems` refuses a snake_case functor at
  ;; arity ≠ 1 *because* an underscore rules out `predicate?`, and leaves a bare word
  ;; alone *because* it satisfies both, so only arity can decide its role.  The test
  ;; harness relies on the same fact (`test-util/fresh-term`, a `:type` temp named after
  ;; a bare word).  Should these two ever stop overlapping, the design loses its footing
  ;; somewhere far from here, so it is enforced rather than left to prose.
  (doseq [w '[dog likes genl thing p q rel]]
    (testing (str w)
      (is (nm/predicate? w))
      (is (nm/type-symbol? w))
      (testing "so it is unconstrained in arity"
        (is (empty? (nm/problems (list w 'Muffet) 'WellContext)))
        (is (empty? (nm/problems (list w 'Muffet 'Rex) 'WellContext))))))
  (testing "an underscore rules out the predicate convention, and only then does arity bite"
    (doseq [t '[physical_object lives_in tmp_dog_17]]
      (testing (str t)
        (is (not (nm/predicate? t)))
        (is (nm/type-symbol? t))
        (is (empty? (nm/problems (list t 'Muffet) 'WellContext)))
        (is (seq (nm/problems (list t 'Muffet 'Rex) 'WellContext)))))))

(deftest structural-accessors
  (is (= 'parentOf (nm/functor '(parentOf Tom Bob))))
  (is (= '(Tom Bob) (nm/args '(parentOf Tom Bob))))
  (is (= 2 (nm/arity '(parentOf Tom Bob)))))

(deftest problem-detection
  (is (empty? (nm/problems '(dog Muffet) 'NaturalWorldContext)))
  (is (seq (nm/problems '(dog Muffet) 'NaturalWorld)))      ; context does not end in Context
  (is (seq (nm/problems '(Dog Muffet) 'NaturalWorldContext))))   ; functor not lowercase-initial

;; ---- the literals a sentence contains -----------------------------------
;; `problems` checks a functor per *literal*, so which positions count as literals is
;; the whole substance of the check.  A frame is descended through; an argument is not.

(deftest literals-are-found-inside-every-frame
  (testing "a plain fact is one literal"
    (is (= [[:sentence '(dog Muffet)]] (nm/literals '(dog Muffet)))))
  (testing "a rule's antecedents and consequent each carry their own role"
    (is (= [[:antecedent '(dog ?x)] [:antecedent '(pet ?x)] [:consequent '(animal ?x)]]
           (nm/literals '(implies (and (dog ?x) (pet ?x)) (animal ?x)))))
    (is (= [[:antecedent '(dog ?x)] [:consequent '(animal ?x)]]
           (nm/literals '(implies (dog ?x) (animal ?x))))))
  (testing "a `not` body is the literal, at whatever role the negation sits in"
    (is (= [[:sentence '(flies Tweety)]] (nm/literals '(not (flies Tweety)))))
    (is (= [[:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(implies (bird ?x) (not (flies ?x)))))))
  (testing "an exceptWhen query's conjuncts are literals of their own"
    (is (= [[:exception '(penguin ?x)] [:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(exceptWhen (penguin ?x)
                                     (set/defaultRule (implies (bird ?x) (flies ?x)))))))
    (testing "written as a vector conjunction"
      (is (= [[:exception '(penguin ?x)] [:exception '(sick ?x)]
              [:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
             (nm/literals '(exceptWhen [(penguin ?x) (sick ?x)]
                                       (implies (bird ?x) (flies ?x))))))))
  (testing "an `ist` redirection frames the sentence it directs"
    (is (= [[:antecedent '(arity ?p 1)] [:consequent '(unaryPredicate ?p)]]
           (nm/literals '(implies (arity ?p 1) (ist CoreContext (unaryPredicate ?p)))))))
  (testing "a negation-as-failure query is framed by `unknown` / `thereExists`"
    (is (= [[:antecedent '(bird ?x)] [:antecedent '(nestOf ?x ?y)] [:consequent '(homeless ?x)]]
           (nm/literals '(implies (and (bird ?x) (unknown (thereExists ?y (nestOf ?x ?y))))
                                  (homeless ?x))))))
  (testing "a head existential frames the consequent it quantifies"
    (is (= [[:antecedent '(person ?x)] [:consequent '(childOf ?x ?y)]]
           (nm/literals '(implies (person ?x) (exists ?y (childOf ?x ?y)))))))
  (testing "the rule wrappers nest in any order and none of them is a literal"
    (is (= [[:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(set/forwardRule
                          (set/defaultRule (implies (bird ?x) (flies ?x)))))))))

(deftest literals-stops-at-what-is-not-a-literal
  (testing "a variable in functor position is a pattern, not a named predicate"
    (is (= [] (nm/literals '(?pred . ?args))))
    (is (= [] (nm/literals '(?p ?x))))
    (testing "so the decontextualization rule's dotted rest pattern names nothing"
      (is (= [] (nm/literals '(set/inertRule
                               (implies (?pred . ?args)
                                        (ist UniverseContext (?pred . ?args)))))))))
  (testing "`(sentexHandle N)` names a stored sentex by id"
    (is (= [[:exception '(penguin ?x)]]
           (nm/literals '(exceptWhen (penguin ?x) (sentexHandle 7))))))
  (testing "a `do/` imperative is an instruction, not a predicate application"
    (is (= [] (nm/literals '(do/labeling SudokuContext)))))
  (testing "arguments are terms, and a compound one is never walked as a literal"
    (is (= [[:sentence '(evaluate ?s (+ 1 2))]] (nm/literals '(evaluate ?s (+ 1 2)))))
    (is (= [[:sentence '(comment not "the negation connective")]]
           (nm/literals '(comment not "the negation connective"))))
    (is (= [[:sentence '(mass Rock1 (QuantityFn 5 Kilogram))]]
           (nm/literals '(mass Rock1 (QuantityFn 5 Kilogram)))))))

;; ---- the invariants below the top level ---------------------------------

(deftest nested-literals-are-name-checked
  (testing "a rule consequent's functor is checked, not the outermost `implies`"
    (is (seq (nm/problems '(implies (penguin ?x) (lives_in ?x cold_place)) 'WellContext)))
    (is (seq (nm/problems '(implies (penguin ?x) (Flies ?x)) 'WellContext))))
  (testing "so is an antecedent's, an exceptWhen query's, and a `not` body's"
    (is (seq (nm/problems '(implies (lives_in ?x cold_place) (penguin ?x)) 'WellContext)))
    (is (seq (nm/problems '(exceptWhen (lives_in ?x cold_place)
                                       (implies (bird ?x) (flies ?x)))
                          'WellContext)))
    (is (seq (nm/problems '(not (lives_in Tweety cold_place)) 'WellContext))))
  (testing "an admissible rule still has no problems"
    (is (empty? (nm/problems '(implies (and (parentOf ?x ?y) (parentOf ?y ?z))
                                       (grandparentOf ?x ?z))
                             'KinshipContext)))))

(deftest snake-case-is-a-type-name-and-therefore-unary-only
  (testing "at arity 1 it is a type"
    (is (empty? (nm/problems '(physical_object Rock1) 'WellContext))))
  (testing "at any other arity it is a type name doing a relation's job"
    (is (seq (nm/problems '(lives_in penguin cold_place) 'WellContext)))
    (is (seq (nm/problems '(disjoint_with penguin fish) 'WellContext))))
  (testing "a camelCase predicate is unconstrained in arity"
    (is (empty? (nm/problems '(livesIn Tweety Antarctica) 'WellContext)))
    (is (empty? (nm/problems '(between A B C) 'WellContext))))
  (testing "an implausible *unary* name is still a well-formed type name — this check is"
    ;; about the shape of a name, never about whether the vocabulary wants it
    (is (empty? (nm/problems '(implies (penguin ?x) (has_black_and_white_feathers ?x))
                             'WellContext)))))

(deftest a-rejection-names-the-literal-and-its-frame
  ;; a repair loop is handed the message verbatim, so it has to say which literal of
  ;; which frame broke, and what to write instead
  (let [[p :as ps] (nm/problems '(implies (penguin ?x) (lives_in ?x cold_place)) 'WellContext)]
    (is (= 1 (count ps)))
    (is (re-find #"lives_in" p))
    (is (re-find #"rule consequent" p))
    (is (re-find #"\(lives_in \?x cold_place\)" p))
    (is (re-find #"livesIn" p) "and the camelCase spelling to use instead"))
  (let [[p] (nm/problems '(implies (Penguin ?x) (flies ?x)) 'WellContext)]
    (is (re-find #"rule antecedent" p))
    (is (re-find #"Penguin" p))))

(deftest an-argument-names-something-and-is-held-to-the-conventions
  ;; a model asked for a relation's second argument writes CapitalCamel-with-underscore
  ;; — a spelling that claims the individual role and the type role and fills neither
  (testing "a symbol matching no role is refused wherever it sits"
    (is (seq (nm/problems '(locatedIn penguin South_Pole) 'WellContext)))
    (is (seq (nm/problems '(genl Baby_Penguin penguin) 'WellContext)))
    (is (seq (nm/problems '(implies (penguin ?x) (locatedIn ?x Cold_Tolerant))
                          'WellContext))))
  (testing "both repairs are named, since only the author knows which role was meant"
    (let [[p] (nm/problems '(locatedIn penguin South_Pole) 'WellContext)]
      (is (re-find #"South_Pole" p))
      (is (re-find #"SouthPole" p) "the individual spelling")
      (is (re-find #"south_pole" p) "the type spelling")))
  (testing "and the frame is named, exactly as a functor rejection names it"
    (let [[p] (nm/problems '(implies (penguin ?x) (locatedIn ?x Cold_Tolerant))
                           'WellContext)]
      (is (re-find #"rule consequent" p))))
  (testing "every well-formed role passes"
    (is (empty? (nm/problems '(locatedIn penguin south_pole) 'WellContext)))
    (is (empty? (nm/problems '(locatedIn Pingu SouthPole) 'WellContext)))
    (is (empty? (nm/problems '(genl penguin bird) 'WellContext)))
    (is (empty? (nm/problems '(inverse parentOf childOf) 'WellContext))))
  (testing "what names nothing is not judged: numbers, strings, variables"
    (is (empty? (nm/problems '(arity penguin 1) 'WellContext)))
    (is (empty? (nm/problems '(argIsa eats 1 animal) 'WellContext)))
    (is (empty? (nm/problems '(comment penguin "A flightless bird.") 'WellContext)))
    (is (empty? (nm/problems '(implies (bird ?x) (flies ?x)) 'WellContext))))
  (testing "a compound argument is a term, so its head is a function and not a name"
    ;; descending into it would judge `+` and every structural NAT functor by naming rules that
    ;; were never about them
    (is (empty? (nm/problems '(evaluate Sum (+ 1 2)) 'WellContext)))
    (is (empty? (nm/problems '(termOfUnit Rod1 (QuantityFn 5 Meter)) 'WellContext)))))

(deftest ist-directs-into-a-context
  (is (empty? (nm/problems '(implies (bird ?x) (ist CoreContext (flies ?x))) 'WellContext)))
  (testing "a variable context is bound at firing time"
    (is (empty? (nm/problems '(implies (and (bird ?x) (ctxOf ?x ?c))
                                       (ist ?c (flies ?x)))
                             'WellContext))))
  (testing "anything else is not a context name"
    (is (seq (nm/problems '(implies (bird ?x) (ist Muffet (flies ?x))) 'WellContext)))))

(deftest the-dotted-marker-is-still-refused-at-the-top-level
  (is (seq (nm/problems '(parentOf Tom . Bob) 'WellContext)))
  (testing "but is legal inside a rule pattern"
    (is (empty? (nm/problems '(set/inertRule
                               (implies (?pred . ?args)
                                        (ist UniverseContext (?pred . ?args))))
                             'CoreContext)))))

;; ---- a problem is data before it is prose --------------------------------

(deftest a-violation-is-a-class-and-a-symbol-before-it-is-a-sentence
  ;; `assert` wants the sentence it refused spelled out; an audit over a corpus wants to
  ;; group.  A message embeds the literal, so it is unique per record and counting
  ;; messages counts records — which is why the class is the datum and the prose is
  ;; rendered from it.
  (testing "each shape reports its own class, naming the symbol that broke"
    (is (= [{:class :context-name :role :sentence :symbol 'NotAThing}]
           (map #(dissoc % :literal) (nm/problems* '(dog Muffet) 'NotAThing))))
    (is (= [{:class :functor :role :sentence :symbol 'Flies}]
           (map #(dissoc % :literal) (nm/problems* '(Flies Tweety) 'WellContext))))
    (is (= [{:class :functor-arity :role :sentence :symbol 'lives_in}]
           (map #(dissoc % :literal) (nm/problems* '(lives_in Tweety cold_place) 'WellContext))))
    (is (= [{:class :argument :role :sentence :symbol 'Baby_Penguin}]
           (map #(dissoc % :literal) (nm/problems* '(parentOf Baby_Penguin Tom) 'WellContext))))
    (is (= [{:class :ist-context :role :sentence :symbol 'Muffet}]
           (map #(dissoc % :literal)
                (nm/problems* '(implies (bird ?x) (ist Muffet (flies ?x))) 'WellContext)))))
  (testing "every class it can report is one `problem-classes` names"
    (is (every? nm/problem-classes
                (map :class (nm/problems* '(Flies Baby_Penguin) 'NotAThing)))))
  (testing "and `problems` is exactly those rendered, one message each, in order"
    (let [s '(Flies Baby_Penguin)]
      (is (= (mapv nm/message (nm/problems* s 'NotAThing))
             (nm/problems s 'NotAThing)))
      (is (= 3 (count (nm/problems s 'NotAThing)))
          "the context, the functor and the argument — all of them, not the first"))))

;; ---- the policy is the KB's, not the build's -----------------------------

(defn- kb-with
  "A cleared KB on the scratch space under one naming policy."
  [policy]
  (fn [] (doto (v/open-kb (assoc tu/scratch-space :naming policy)) (tu/clear-kb!))))

(def ^:private misnamed '(parentOf Baby_Penguin Tom))

(deftest the-naming-policy-belongs-to-the-kb
  ;; The conventions are how *this* KB reads a role off a spelling, so a KB holding a
  ;; corpus that spells its names differently is not malformed — it is a KB whose front
  ;; door is set differently.  Neither has to win, and both can be open at once.
  (testing ":strict is the default, and refuses with a :naming type"
    (tu/with-cleared-kb [kb (kb-with :strict)]
      (is (= :strict (:naming kb)))
      (is (= :strict (:naming (v/open-kb tu/scratch-space))) "the default, unasked for")
      (is (= :naming (:type (try (v/assert kb misnamed 'WellContext)
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))))
      (is (zero? (v/sentex-count kb)) "and nothing was stored")))

  (testing ":off stores it, and it is findable by the name that broke the convention"
    (tu/with-cleared-kb [kb (kb-with :off)]
      (let [h (v/assert kb misnamed 'WellContext)]
        (is (integer? h))
        (is (= 1 (v/sentex-count kb)))
        (is (= misnamed (:sentence (v/sentex kb h))) "stored verbatim, not repaired")
        (is (= [misnamed] (map :sentence (v/find-sentexes kb 'Baby_Penguin)))))))

  (testing ":warn stores it too — the difference is what it says, not what it keeps"
    (tu/with-cleared-kb [kb (kb-with :warn)]
      (is (integer? (v/assert kb misnamed 'WellContext)))
      (is (= 1 (v/sentex-count kb)))))

  (testing "an unknown policy is refused rather than defaulted"
    ;; on the same ground as an unknown `open-kb` key: a KB that silently took :strict
    ;; when it was told :lenient refuses content the caller expected to land
    (is (= :unknown-option
           (:type (try (v/open-kb (assoc tu/scratch-space :naming :lenient))
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))))))

(deftest two-doors-over-one-store-disagree-and-both-are-right
  ;; The policy travels with the KB, not with the records, so a lenient loader and a
  ;; strict editor can hold the same store at once — which is the whole point of it
  ;; being per-KB rather than a property of the build.
  (tu/with-cleared-kb [lenient (kb-with :off)]
    (let [strict (v/open-kb (assoc tu/scratch-space :naming :strict :recover? false))]
      (v/assert lenient misnamed 'WellContext)
      (testing "the strict KB reads what the lenient one stored"
        (is (= [misnamed] (map :sentence (v/find-sentexes strict 'Baby_Penguin)))))
      (testing "but still refuses to be the one that writes it"
        (is (= :naming (:type (try (v/assert strict '(parentOf Other_Penguin Tom) 'WellContext)
                                   (catch clojure.lang.ExceptionInfo e (ex-data e))))))))))

(deftest a-policy-moves-what-is-refused-never-how-a-role-is-read
  ;; The one cost of `:off`, stated as a test so it cannot be forgotten: the KB stores a
  ;; name it *cannot classify*, rather than classifying it differently.  Nothing
  ;; downstream starts reading `Baby_Penguin` as an individual because the door was open.
  (is (nil? (v/term-role 'Baby_Penguin)))
  (is (= :individual (v/term-role 'BabyPenguin)))
  (is (not (nm/individual? 'Baby_Penguin)))
  (testing "so the messages do not move either — only whether anyone throws them"
    (is (seq (nm/problems misnamed 'WellContext)))
    (is (seq (nm/blocking-problems :strict misnamed 'WellContext)))
    (is (empty? (nm/blocking-problems :warn misnamed 'WellContext)))
    (is (empty? (nm/blocking-problems :off  misnamed 'WellContext)))))

(deftest the-other-door-counts-what-it-does-not-check
  ;; A bulk path stores what `assert` refuses — that is what it is for — so the two
  ;; doors are reconciled by a count rather than by a check.
  (let [t (-> nm/empty-tally
              (nm/tally '(dog Muffet) 'WellContext)
              (nm/tally misnamed 'WellContext)
              (nm/tally '(Flies Tweety) 'NotAThing))]
    (is (= 3 (:checked t)))
    (is (= 2 (:refused t)) "records, not violations — one sentence can break three")
    (is (= {:argument 1 :functor 1 :context-name 1} (:by-class t)))
    (is (re-find #"2 of 3 records" (nm/tally-line t)))
    (is (re-find #"66\.7%" (nm/tally-line t))))
  (testing "and says nothing at all when the corpus and the front door agree"
    (is (nil? (nm/tally-line (nm/tally nm/empty-tally '(dog Muffet) 'WellContext))))))

(deftest a-refused-exceptWhen-leaves-no-bare-rule-behind
  ;; The exception's own literals are held to the naming invariants like every other
  ;; literal a rule carries — and the refusal is **atomic**: it runs before the rule
  ;; is stored, so a caller holds a throw and no handle, never a bare rule believed
  ;; and firing unguarded with no handle returned to retract it by.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bird flies WellContext]
      (let [rule (list 'implies (list bird '?x) (list flies '?x))
            bad  (list 'exceptWhen (list 'lives_in '?x 'cold_place) rule)]
        (is (= :naming (:type (try (v/assert kb bad WellContext) nil
                                   (catch clojure.lang.ExceptionInfo e (ex-data e)))))
            "a snake_case arity-2 functor in the exception query is refused")
        (is (= [:naming] (mapv :type (v/check kb bad WellContext)))
            "and check predicts it")
        (is (nil? (v/handle-of kb rule WellContext))
            "the bare rule was not stored — the refusal happened before the store")))))

(deftest the-membership-spelling-every-other-system-taught-is-advised-against
  ;; `(isa Muffet Dog)` breaks no invariant: `isa` is a well-formed predicate and both
  ;; arguments are well-formed individuals, so it is stored, indexed and believed —
  ;; as a two-place relation nothing reads.  The reader then asks `(isa? kb 'Muffet
  ;; 'Dog)`, gets false, and has no error to search for.  docs/naming.md calls this
  ;; out by name and CoreContext.txt says never to write it; neither is in front of
  ;; someone typing, so the front door says it.
  (testing "the shape is advised against, and the advice names the right spelling"
    (let [{:keys [id message]} (nm/advice '(isa Muffet Dog))]
      (is (= ::nm/isa-is-not-how-membership-is-written id))
      (is (re-find #"\(dog Muffet\)" message)
          "the message spells the sentence that was meant")
      (is (re-find #"unary" message))))
  (testing "it is advice and not a refusal — the sentence breaks no invariant"
    (is (empty? (nm/problems '(isa Muffet Dog) 'UniverseContext))))
  (testing "a multi-word type is spelled snake_case, not merely lower-cased"
    ;; `physicalobject` is a name the conventions refuse, so suggesting it would
    ;; trade one unusable sentence for another
    (is (re-find #"\(physical_object Muffet\)"
                 (:message (nm/advice '(isa Muffet PhysicalObject))))))
  (testing "an argument that is not a symbol gets advice, not a ClassCastException"
    ;; a number, a string and a compound are all legal in argument position, and
    ;; `clojure.core/name` throws on every one of them — advice that crashes the
    ;; assert it was meant to help is worse than no advice
    (doseq [s ['(isa Muffet 42)
               '(isa 42 Dog)
               '(isa Muffet "Dog")
               '(isa (theCatOf Tom) Dog)
               '(isa Muffet (kindOf Dog))]]
      (let [a (nm/advice s)]                       ; `is` answers a boolean, not the value
        (is (some? a) (pr-str s))
        (is (string? (:message a)) (pr-str s))
        (is (re-find #"unary type predicate" (:message a))
            "and falls back to the generic form rather than guessing a rewrite"))))
  (testing "nothing legitimate draws it"
    (doseq [s ['(dog Muffet)
               '(genl dog thing)
               '(argIsa parentOf 1 dog)          ; a different predicate entirely
               '(likes Tom Ann)
               '(isa Muffet)                        ; not the two-place shape
               '(isa Muffet Dog Extra)]]
      (is (nil? (nm/advice s)) (pr-str s))))
  (testing "advise! is silent under :naming :off, which asks for no policing"
    ;; reach past the once-per-process gate by asking the pure fn either side of it
    (is (some? (nm/advice '(isa Muffet Dog))))
    (is (nil? (nm/advise! :off '(isa Muffet Dog) 'UniverseContext)))))

;;; ── senses and lexemes ────────────────────────────────────────────────

(deftest a-sense-is-a-type-that-says-which-sense-it-is
  (testing "a word, a dash, and the disambiguator"
    (doseq [s '[abrasive-grit abandonment-romantic abandonment-dual game-theory]]
      (is (= :sense (v/term-role s)) (pr-str s))
      (is (nm/type-symbol? s) "a sense is a type — the hierarchy is built of them")))
  (testing "two senses of one word are two terms, which is the whole point"
    (is (not= 'abandonment-romantic 'abandonment-dual))
    (is (every? #(= :sense (v/term-role %)) '[abandonment-romantic abandonment-dual])))
  (testing "the split is the LAST dash, because a word may hold its own"
    (is (= :sense (v/term-role 'a--musical_note)))       ; the word is `a-`, ending in a dash
    (is (= :sense (v/term-role 'part-time-employment))))  ; the word is `part-time`
  (testing "and both halves admit what real vocabulary carries"
    (doseq [s '[.22_long_rifle-ammo .dll-library      ; a leading dot
                fool's_gold-mineral deck-ship's_floor ; an apostrophe inside
                organ_cultures-3d chiptune_composer-8bit]] ; a digit-leading disambiguator
      (is (= :sense (v/term-role s)) (pr-str s))))
  (testing "a sense is a unary predicate, like every other type"
    (is (empty? (nm/problems* '(abrasive-grit Muffet) 'UniverseContext)))
    (is (= [:functor-arity]
           (mapv :class (nm/problems* '(abrasive-grit Muffet Rex) 'UniverseContext))))))

(deftest a-lexeme-is-parse-input-and-is-marked-by-its-namespace
  (testing "the namespace decides it, and the text is not ours to spell"
    (doseq [s '[lex/thing lex/fool's_gold lex/a_la_carte]]
      (is (= :lexeme (v/term-role s)) (pr-str s))
      (is (nm/lexeme? s))))
  (testing "a marker written INTO the name could not work — the word carries the same
            character.  `fool's_gold` has an apostrophe of its own, and 333 lexemes in
            the corpus carry one inside as well as at the end."
    (is (= :lexeme (v/term-role 'lex/fool's_gold)))
    (is (= "fool's_gold" (name 'lex/fool's_gold))))
  (testing "every other namespace stays invisible to the role checks"
    (is (= :predicate (v/term-role 'agg/count)))
    (is (= :predicate (v/term-role 'set/forwardRule)))
    (is (= :predicate (v/term-role 'ex/disambiguator)))
    (is (not-any? nm/lexeme? '[agg/count set/forwardRule ex/disambiguator]))))

(deftest the-one-fence-around-a-lexeme-is-that-it-names-no-relation
  (testing "a lexeme applied to arguments is refused — a surface form is not a predicate"
    (is (= [:lexeme-functor]
           (mapv :class (nm/problems* '(lex/fools_gold Muffet) 'UniverseContext)))))
  (testing "but as an argument it is ordinary, which is what lets a sense be stated"
    (is (empty? (nm/problems* '(sense lex/fools_gold fools_gold-mineral)
                              'UniverseContext))))
  (testing "and what lets the improver's unsensified edge stand until it crafts the sense"
    ;; `(genl <sense> <lexeme>)` is the improver's input, not an error: it sensifies the
    ;; lexeme by replacing it with a sense, which is its core operation.
    (is (empty? (nm/problems* '(genl abrasive-grit lex/abrasive_tool)
                              'UniverseContext)))))

(deftest a-name-the-reader-would-not-read-back-is-refused
  (testing "a leading digit reads as a malformed number, not a symbol"
    (is (thrown? Exception (read-string "134a-gas")))
    (is (nil? (v/term-role (symbol "134a-gas")))))
  (testing "and the escaped spelling reads, and is a sense"
    (is (= :sense (v/term-role (read-string "_134a-gas")))))
  (testing "a leading apostrophe is the quote macro, so it never names anything"
    (is (seq? (read-string "'centaur'-mythical")))
    (is (= :sense (v/term-role (read-string "_'centaur'-mythical"))))))

;;; ── the roster and its renderer are one thing ─────────────────────────

(def ^:private class-samples
  "One sentence per `problem-classes` key, and the context to check it in."
  {:context-name   ['(dog Muffet)                                'NotAThing]
   :functor        ['(Flies Tweety)                            'WellContext]
   :lexeme-functor ['(lex/fools_gold Muffet)                     'WellContext]
   :functor-arity  ['(lives_in Tweety cold_place)              'WellContext]
   :argument       ['(parentOf Baby_Penguin Tom)               'WellContext]
   :ist-context    ['(implies (bird ?x) (ist Muffet (flies ?x))) 'WellContext]
   :dot-marker     ['(parentOf Tom .)                          'WellContext]})

(deftest every-problem-class-renders-a-message
  ;; `problem-classes` is a map and `message` a `case` over its keys, so the two drift in
  ;; a direction nothing else looks: a class the roster names and `problems*` emits with
  ;; no arm to render it throws `IllegalArgumentException: No matching clause` out of
  ;; `assert`, where the contract is an `ex-info` carrying `:type :naming`.  The roster
  ;; test above checks the other direction — that an emitted class is one the roster
  ;; names — and the two together are what make the pairing total.
  (testing "a new class owes this test a sentence that produces it"
    (is (= (set (keys nm/problem-classes)) (set (keys class-samples)))))
  (doseq [[cls [sentence context]] class-samples]
    (testing (str cls)
      (let [ps (nm/problems* sentence context)]
        (is (some #(= cls (:class %)) ps) "that sentence produces this class")
        (doseq [p ps]
          (let [m (nm/message p)]
            (is (string? m) "and every violation it reports renders")
            (is (seq m)))))
      ;; the composition, which is what `assert` calls and where the crash surfaced
      (is (seq (nm/problems sentence context))))))

(deftest a-sense-at-the-wrong-arity-is-not-told-to-camelcase-itself
  ;; A sense reaches `:functor-arity` for the same reason a snake_case type does — both
  ;; are types, and a type is unary — but the snake_case repair does not transfer: there
  ;; is no camelCase spelling of `abrasive-grit`, so offering one names the symbol back
  ;; and reads as advice while being none.
  (let [[m] (nm/problems '(abrasive-grit Muffet Rex) 'UniverseContext)]
    (is (re-find #"is a sense" m))
    (is (not (re-find #"snake_case" m)))
    (is (not (re-find #"camelCase as abrasive-grit" m))))
  (testing "and the snake_case repair still names the camelCase spelling"
    (let [[m] (nm/problems '(lives_in Tweety cold_place) 'UniverseContext)]
      (is (re-find #"camelCase as livesIn" m)))))

(deftest a-lexeme-functor-is-refused-as-an-ex-info-not-a-crash
  ;; The front door's contract is that every refusal is an `ex-info` carrying a `:type`
  ;; a caller can discriminate on.  A class with no `message` arm breaks it below the
  ;; level `assert` can catch, so the refusal arrives as an `IllegalArgumentException`
  ;; naming a `case` — true about the code, and no help to whoever wrote the sentence.
  (tu/with-cleared-kb [kb (kb-with :strict)]
    (let [e (try (v/assert kb '(lex/fools_gold Muffet) 'WellContext) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "a lexeme applied to arguments is refused")
      (is (= :naming (:type (ex-data e))))
      (is (re-find #"is a lexeme" (ex-message e)))
      (is (zero? (v/sentex-count kb)) "and nothing was stored"))))
