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
    (is (= :context    (tu/term-role 'CxStory))))
  (tu/with-terms [dog Muffet parentOf CxStory]
    (testing "each generated term satisfies the invariant for its role"
      (is (nm/type-symbol? dog))
      (is (nm/individual? Muffet))
      (is (nm/predicate? parentOf))
      (is (nm/context? CxStory))
      (is (empty? (nm/problems (list dog Muffet) CxStory))))
    (testing "and embeds the symbol it was named after, so a failure is readable"
      (is (re-find #"dog"      (name dog)))
      (is (re-find #"Muffet"     (name Muffet)))
      ;; a predicate temp is bare lowercase — camelCase would commit it to arity 2+
      ;; exactly as an underscore commits a type temp to arity 1 (`tu/fresh-term`)
      (is (re-find #"parentof" (name parentOf)))
      (is (re-find #"Story"    (name CxStory))))
    (testing "a type temp named after a bare word stays as ambiguous as the word"
      ;; `dog` satisfies both conventions and is disambiguated by arity, so the temp
      ;; is spelled to be usable either way — underscores would restrict it to arity 1
      (is (nm/predicate? dog))
      (is (empty? (nm/problems (list dog Muffet) CxStory)))
      (is (empty? (nm/problems (list dog Muffet Muffet) CxStory))))
    (testing "roles stay distinct — a context is not an individual"
      (is (not (nm/individual? CxStory)))))
  (testing "a base spelled snake_case is a type and only a type"
    (let [t (tu/fresh-term :type "physical object")]
      (is (nm/type-symbol? t))
      (is (not (nm/predicate? t)))
      (is (empty? (nm/problems (list t 'Rock1) 'CxWell)))
      (is (seq (nm/problems (list t 'Rock1 'Rock2) 'CxWell)))))
  (testing "the same name twice still yields distinct terms"
    (is (not= (tu/fresh-term :type "dog") (tu/fresh-term :type "dog")))))

(deftest role-predicates
  (testing "contexts"
    (is (nm/context? 'CxUniverse))
    (is (not (nm/context? 'Universe))))
  (testing "individuals are CapitalCamelCase but not contexts"
    (is (nm/individual? 'Muffet))
    (is (not (nm/individual? 'dog)))
    (is (not (nm/individual? 'CxUniverse))))
  (testing "predicates are camelCase, types are snake_case"
    (is (nm/predicate? 'parentOf))
    (is (nm/type-symbol? 'physical_object))
    (is (not (nm/predicate? 'physical_object)))          ; underscore ⇒ not a predicate
    (is (not (nm/type-symbol? 'parentOf)))))             ; uppercase ⇒ not snake_case

(deftest a-bare-lowercase-word-satisfies-both-conventions
  ;; the arity biconditional and `tu/fresh-term`'s bare-word temps both rest on this overlap
  (doseq [w '[dog likes genl thing p q rel]]
    (testing (str w)
      (is (nm/predicate? w))
      (is (nm/type-symbol? w))
      (testing "so it is unconstrained in arity"
        (is (empty? (nm/problems (list w 'Muffet) 'CxWell)))
        (is (empty? (nm/problems (list w 'Muffet 'Rex) 'CxWell))))))
  (testing "an underscore rules out the predicate convention, and only then does arity bite"
    (doseq [t '[physical_object lives_in tmp_dog_17]]
      (testing (str t)
        (is (not (nm/predicate? t)))
        (is (nm/type-symbol? t))
        (is (empty? (nm/problems (list t 'Muffet) 'CxWell)))
        (is (seq (nm/problems (list t 'Muffet 'Rex) 'CxWell)))))))

(deftest structural-accessors
  (is (= 'parentOf (nm/functor '(parentOf Tom Bob))))
  (is (= '(Tom Bob) (nm/args '(parentOf Tom Bob))))
  (is (= 2 (nm/arity '(parentOf Tom Bob)))))

;; ---- the literals a sentence contains -----------------------------------

(deftest literals-are-found-inside-every-wrapper
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
                                       (implies (bird ?x) (flies ?x)))))))
    (testing "inside the strength wrapper that states the exception's class"
      (is (= [[:exception '(penguin ?x)] [:exception '(sick ?x)]
              [:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
             (nm/literals '(exceptWhen (set/monotonic [(penguin ?x) (sick ?x)])
                                       (implies (bird ?x) (flies ?x))))))
      (is (seq (nm/problems '(exceptWhen (set/monotonic (Bad_q ?x)) (implies (bird ?x) (flies ?x)))
                            'CxUniverse)))))
  (testing "an `ist` wraps the sentence it names a context for"
    (is (= [[:sentence '(unary_predicate dog)]]
           (nm/literals '(ist CxUniverse (unary_predicate dog))))))
  (testing "a negation-as-failure query is wrapped by `unknown` / `thereExists`"
    (is (= [[:antecedent '(bird ?x)] [:antecedent '(nestOf ?x ?y)] [:consequent '(homeless ?x)]]
           (nm/literals '(implies (and (bird ?x) (unknown (thereExists ?y (nestOf ?x ?y))))
                                  (homeless ?x))))))
  (testing "a head existential wraps the consequent it quantifies"
    (is (= [[:antecedent '(person ?x)] [:consequent '(childOf ?x ?y)]]
           (nm/literals '(implies (person ?x) (exists ?y (childOf ?x ?y)))))))
  (testing "a `forall` antecedent's body and head are read in the antecedent role"
    (is (= [[:antecedent '(bird ?x)] [:antecedent '(chickOf ?x ?y)] [:antecedent '(fed ?y)]
            [:consequent '(provider ?x)]]
           (nm/literals '(implies (and (bird ?x) (forall ?y (implies (chickOf ?x ?y) (fed ?y))))
                                  (provider ?x))))))
  (testing "the rule wrappers nest in any order and none of them is a literal"
    (is (= [[:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(set/forwardRule
                          (set/defaultRule (implies (bird ?x) (flies ?x)))))))
    (is (= [[:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(set/solveRule
                          (set/forwardRule (implies (bird ?x) (flies ?x))))))))
  (testing "a brave or cautious read wraps the sentence it reads"
    (is (= [[:antecedent '(bird ?x)] [:antecedent '(pacifist ?x)] [:consequent '(calm ?x)]]
           (nm/literals '(implies (and (bird ?x) (bravely (pacifist ?x))) (calm ?x)))))
    (is (= [[:antecedent '(pacifist ?x)] [:consequent '(calm ?x)]]
           (nm/literals '(implies (cautiously (pacifist ?x)) (calm ?x))))))
  (testing "an aggregate's body is a goal, not an argument"
    (is (= [[:sentence '(likes ?y Tom)]] (nm/literals '(agg/count ?n ?y (likes ?y Tom))))))
  (testing "a generated rule's literals are tagged as generated, at every depth"
    (is (= [[:antecedent '(p ?x)] [:generated-antecedent '(q ?y)]
            [:generated-antecedent '(s ?z)] [:generated-consequent '(r ?z)]]
           (nm/literals '(implies (p ?x) (implies (q ?y) (implies (s ?z) (r ?z)))))))))

(deftest literals-stops-at-what-is-not-a-literal
  (testing "a variable in functor position is a pattern, not a named predicate"
    (is (= [] (nm/literals '(?pred . ?args))))
    (is (= [] (nm/literals '(?p ?x))))
    (testing "so a rule's dotted rest pattern names nothing"
      (is (= [] (nm/literals '(set/inertRule
                               (implies (?pred . ?args) (?pred . ?args))))))))
  (testing "`(sentexHandle N)` names a stored sentex by id"
    (is (= [[:exception '(penguin ?x)]]
           (nm/literals '(exceptWhen (penguin ?x) (sentexHandle 7))))))
  (testing "a `do/` imperative is an instruction, not a predicate application"
    (is (= [] (nm/literals '(do/labeling CxSudoku)))))
  (testing "arguments are terms, and a compound one is never walked as a literal"
    (is (= [[:sentence '(evaluate ?s (+ 1 2))]] (nm/literals '(evaluate ?s (+ 1 2)))))
    (is (= [[:sentence '(comment not "the negation connective")]]
           (nm/literals '(comment not "the negation connective"))))
    (is (= [[:sentence '(mass Rock1 (QuantityFn 5 Kilogram))]]
           (nm/literals '(mass Rock1 (QuantityFn 5 Kilogram)))))))

;; ---- the invariants below the top level ---------------------------------

(deftest nested-literals-are-name-checked
  (testing "a rule consequent's functor is checked, not the outermost `implies`"
    (is (seq (nm/problems '(implies (penguin ?x) (lives_in ?x cold_place)) 'CxWell)))
    (is (seq (nm/problems '(implies (penguin ?x) (Flies ?x)) 'CxWell))))
  (testing "so is an antecedent's, an exceptWhen query's, and a `not` body's"
    (is (seq (nm/problems '(implies (lives_in ?x cold_place) (penguin ?x)) 'CxWell)))
    (is (seq (nm/problems '(exceptWhen (lives_in ?x cold_place)
                                       (implies (bird ?x) (flies ?x)))
                          'CxWell)))
    (is (seq (nm/problems '(not (lives_in Tweety cold_place)) 'CxWell))))
  (testing "an admissible rule still has no problems"
    (is (empty? (nm/problems '(implies (and (parentOf ?x ?y) (parentOf ?y ?z))
                                       (grandparentOf ?x ?z))
                             'CxKinship)))))

(deftest snake-case-is-a-type-name-and-therefore-unary-only
  (testing "at arity 1 it is a type"
    (is (empty? (nm/problems '(physical_object Rock1) 'CxWell))))
  (testing "at any other arity it is a type name doing a relation's job"
    (is (seq (nm/problems '(lives_in penguin cold_place) 'CxWell)))
    (is (seq (nm/problems '(disjoint_with penguin fish) 'CxWell))))
  (testing "a camelCase predicate is unconstrained in arity"
    (is (empty? (nm/problems '(livesIn Tweety Antarctica) 'CxWell)))
    (is (empty? (nm/problems '(between A B C) 'CxWell))))
  (testing "an implausible *unary* name is still a well-formed type name — this check is"
    ;; about the structure of a name, never about whether the vocabulary wants it
    (is (empty? (nm/problems '(implies (penguin ?x) (has_black_and_white_feathers ?x))
                             'CxWell)))))

(deftest a-rejection-names-the-literal-and-its-wrapper
  (let [[p :as ps] (nm/problems '(implies (penguin ?x) (lives_in ?x cold_place)) 'CxWell)]
    (is (= 1 (count ps)))
    (is (re-find #"lives_in" p))
    (is (re-find #"rule consequent" p))
    (is (re-find #"\(lives_in \?x cold_place\)" p))
    (is (re-find #"livesIn" p) "and the camelCase spelling to use instead"))
  (let [[p] (nm/problems '(implies (Penguin ?x) (flies ?x)) 'CxWell)]
    (is (re-find #"rule antecedent" p))
    (is (re-find #"Penguin" p))))

(deftest an-argument-names-something-and-is-held-to-the-conventions
  ;; a model asked for a relation's second argument writes CapitalCamel-with-underscore
  ;; — a spelling that claims the individual role and the type role and fills neither
  (testing "a symbol matching no role is refused wherever it sits"
    (is (seq (nm/problems '(locatedIn penguin South_Pole) 'CxWell)))
    (is (seq (nm/problems '(genl Baby_Penguin penguin) 'CxWell)))
    (is (seq (nm/problems '(implies (penguin ?x) (locatedIn ?x Cold_Tolerant))
                          'CxWell))))
  (testing "both repairs are named, since only the author knows which role was meant"
    (let [[p] (nm/problems '(locatedIn penguin South_Pole) 'CxWell)]
      (is (re-find #"South_Pole" p))
      (is (re-find #"SouthPole" p) "the individual spelling")
      (is (re-find #"south_pole" p) "the type spelling")))
  (testing "and the wrapper is named, as a functor rejection names it"
    (let [[p] (nm/problems '(implies (penguin ?x) (locatedIn ?x Cold_Tolerant))
                           'CxWell)]
      (is (re-find #"rule consequent" p))))
  (testing "every well-formed role passes"
    (is (empty? (nm/problems '(locatedIn penguin south_pole) 'CxWell)))
    (is (empty? (nm/problems '(locatedIn Pingu SouthPole) 'CxWell)))
    (is (empty? (nm/problems '(genl penguin bird) 'CxWell)))
    (is (empty? (nm/problems '(inverse parentOf childOf) 'CxWell))))
  (testing "what names nothing is not judged: numbers, strings, variables"
    (is (empty? (nm/problems '(arity penguin 1) 'CxWell)))
    (is (empty? (nm/problems '(arg eats 1 animal) 'CxWell)))
    (is (empty? (nm/problems '(comment penguin "A flightless bird.") 'CxWell)))
    (is (empty? (nm/problems '(implies (bird ?x) (flies ?x)) 'CxWell))))
  (testing "a compound argument is a term, so its head is a function and not a name"
    (is (empty? (nm/problems '(evaluate Sum (+ 1 2)) 'CxWell)))
    (is (empty? (nm/problems '(natFormula Rod1 (QuantityFn 5 Meter)) 'CxWell)))))

(deftest ist-names-a-context
  (is (empty? (nm/problems '(ist CxUniverse (flies Tweety)) 'CxWell)))
  (testing "a variable in the slot is a pattern position and is not judged"
    (is (empty? (nm/problems '(implies (storyOf ?s ?c) (ist ?c (flies Tweety))) 'CxWell))))
  (testing "anything else is not a context name"
    (is (seq (nm/problems '(ist Muffet (flies Tweety)) 'CxWell)))))

(deftest a-rest-pattern-in-a-rule-passes-naming
  (is (empty? (nm/problems '(set/inertRule
                             (implies (?pred . ?args) (?pred . ?args)))
                           'CxUniverse))))

;; ---- a problem is data before it is prose --------------------------------

(deftest a-violation-is-a-class-and-a-symbol-before-it-is-a-sentence
  (testing "every class it can report is one `problem-classes` names"
    (is (every? nm/problem-classes
                (map :class (nm/problems* '(Flies Baby_Penguin) 'NotAThing)))))
  (testing "every violation is reported, in the documented order"
    (is (= [:context-name :functor :argument :ist-context]
           (mapv :class (nm/problems* '(ist Muffet (Flies Baby_Penguin)) 'NotAThing)))))
  (testing "and `problems` is exactly those rendered, one message each, in order"
    (let [s '(Flies Baby_Penguin)]
      (is (= (mapv nm/message (nm/problems* s 'NotAThing))
             (nm/problems s 'NotAThing)))
      (is (= 3 (count (nm/problems s 'NotAThing)))))))

;; ---- the policy is the KB's, not the build's -----------------------------

(defn- kb-with
  "An empty KB on the scratch space under one naming policy."
  [policy]
  (fn [] (tu/fresh {:naming policy})))

(def ^:private misnamed '(parentOf Baby_Penguin Tom))

(deftest the-naming-policy-belongs-to-the-kb
  (testing ":strict is the default, and refuses with a :naming type"
    (tu/with-cleared-kb [kb (kb-with :strict)]
      (is (= :strict (:naming kb)))
      (is (= :strict (:naming (v/open-kb (tu/scratch-space)))) "the default, unasked for")
      (is (= :naming (:type (try (v/assert kb misnamed 'CxWell)
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))))
      (is (zero? (v/sentex-count kb)) "and nothing was stored")))

  (testing ":off stores it, and it is findable by the name that broke the convention"
    (tu/with-cleared-kb [kb (kb-with :off)]
      (let [h (v/assert kb misnamed 'CxWell)]
        (is (integer? h))
        (is (= 1 (v/sentex-count kb)))
        (is (= misnamed (:sentence (v/sentex kb h))) "stored verbatim, not repaired")
        (is (= [misnamed] (map :sentence (v/find-sentexes kb 'Baby_Penguin)))))))

  (testing ":warn stores it too — the difference is what it says, not what it keeps"
    (tu/with-cleared-kb [kb (kb-with :warn)]
      (is (integer? (v/assert kb misnamed 'CxWell)))
      (is (= 1 (v/sentex-count kb)))))

  (testing "an unknown policy is refused rather than defaulted"
    (is (= :unknown-option
           (:type (try (v/open-kb (assoc (tu/scratch-space) :naming :lenient))
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))))))

(deftest two-entry-points-over-one-store-disagree-and-both-are-right
  (tu/with-cleared-kb [lenient (kb-with :off)]
    (let [strict (v/open-kb (assoc (tu/scratch-space) :naming :strict :recover? false))]
      (v/assert lenient misnamed 'CxWell)
      (testing "the strict KB reads what the lenient one stored"
        (is (= [misnamed] (map :sentence (v/find-sentexes strict 'Baby_Penguin)))))
      (testing "but still refuses to be the one that writes it"
        (is (= :naming (:type (try (v/assert strict '(parentOf Other_Penguin Tom) 'CxWell)
                                   (catch clojure.lang.ExceptionInfo e (ex-data e))))))))))

(deftest a-functor-a-firing-forms-is-held-to-the-naming-policy
  ;; `(?f ?x)` passes the rule's own check, since a variable names nothing, so the functor
  ;; a binding forms is first read when the conclusion is placed.  Both arrival orders,
  ;; because the retroactive join places through the same path as a fresh firing.
  (tu/with-terms [appliesTo Fido Rex dog]
    (let [rule      (list 'set/forwardRule (list 'implies (list appliesTo '?x '?f) (list '?f '?x)))
          facts     [(list appliesTo Fido Rex) (list appliesTo Fido dog)]
          misnamed  (list Rex Fido)
          admitted  (list dog Fido)
          naming-of (fn [kb] (into #{} (comp (filter #(= :naming (:violation %)))
                                             (map :sentence))
                                   (v/violations kb)))]
      (doseq [[label order] [["rule first" (cons rule facts)]
                             ["facts first" (conj facts rule)]]]
        (testing (str ":strict drops and reports it, " label)
          (tu/with-cleared-kb [kb (kb-with :strict)]
            (doseq [s order] (v/assert kb s 'CxWell))
            (is (nil? (v/handle-of kb misnamed 'CxWell)))
            (is (= #{misnamed} (naming-of kb)))
            (is (some? (v/handle-of kb admitted 'CxWell))
                "a conclusion the invariants admit is stored beside it"))))
      (doseq [policy [:warn :off]]
        (testing (str policy " stores it and reports nothing")
          (tu/with-cleared-kb [kb (kb-with policy)]
            (doseq [s (cons rule facts)] (v/assert kb s 'CxWell))
            (is (some? (v/handle-of kb misnamed 'CxWell)))
            (is (empty? (naming-of kb)))))))))

(deftest a-policy-moves-what-is-refused-never-how-a-role-is-read
  (is (nil? (v/term-role 'Baby_Penguin)))
  (is (= :individual (v/term-role 'BabyPenguin)))
  (is (not (nm/individual? 'Baby_Penguin)))
  (testing "so the messages do not move either — only whether anyone throws them"
    (is (seq (nm/problems misnamed 'CxWell)))
    (is (= (nm/problems misnamed 'CxWell) (nm/blocking-problems :strict misnamed 'CxWell)))
    (is (empty? (nm/blocking-problems :warn misnamed 'CxWell)))
    (is (empty? (nm/blocking-problems :off  misnamed 'CxWell)))))

(deftest the-other-entry-point-counts-what-it-does-not-check
  (let [t (-> nm/empty-tally
              (nm/tally '(dog Muffet) 'CxWell)
              (nm/tally misnamed 'CxWell)
              (nm/tally '(Flies Tweety) 'NotAThing))]
    (is (= 3 (:checked t)))
    (is (= 2 (:refused t)) "records, not violations — one sentence can break three")
    (is (= {:argument 1 :functor 1 :context-name 1} (:by-class t)))
    (is (re-find #"2 of 3 records" (nm/tally-line t)))
    (is (re-find #"66\.7%" (nm/tally-line t)))
    (is (= {:argument 1} (:by-class (nm/tally nm/empty-tally '(parentOf Baby_Penguin Other_Penguin) 'CxWell)))
        "a class counts a record once, however many of its violations it holds"))
  (testing "and says nothing at all when the corpus and the public entry point agree"
    (is (nil? (nm/tally-line (nm/tally nm/empty-tally '(dog Muffet) 'CxWell))))))

(deftest a-refused-exceptWhen-leaves-no-bare-rule-behind
  ;; the exception query is checked before the rule is stored, so a refusal leaves no
  ;; unguarded rule without a handle to retract it by
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bird flies CxWell]
      (let [rule (list 'implies (list bird '?x) (list flies '?x))
            bad  (list 'exceptWhen (list 'lives_in '?x 'cold_place) rule)]
        (is (= :naming (:type (try (v/assert kb bad CxWell) nil
                                   (catch clojure.lang.ExceptionInfo e (ex-data e)))))
            "a snake_case arity-2 functor in the exception query is refused")
        (is (= [:naming] (mapv :type (v/check kb bad CxWell)))
            "and check predicts it")
        (is (nil? (v/handle-of kb rule CxWell))
            "the bare rule was not stored — the refusal happened before the store")))))

(deftest the-membership-spelling-every-other-system-taught-is-advised-against
  (testing "the shape is advised against, and the advice names the right spelling"
    (let [{:keys [id message]} (nm/advice '(isa Muffet Dog))]
      (is (= ::nm/isa-is-not-how-membership-is-written id))
      (is (re-find #"\(dog Muffet\)" message)
          "the message spells the sentence that was meant")
      (is (re-find #"unary" message))))
  (testing "it is advice and not a refusal — the sentence breaks no invariant"
    (is (empty? (nm/problems '(isa Muffet Dog) 'CxUniverse))))
  (testing "a multi-word type is spelled snake_case, not merely lower-cased"
    (is (re-find #"\(warm_blooded Muffet\)"
                 (:message (nm/advice '(isa Muffet WarmBlooded))))))
  (testing "an argument that is not a symbol gets advice, not a ClassCastException"
    (doseq [s ['(isa Muffet 42)
               '(isa 42 Dog)
               '(isa Muffet "Dog")
               '(isa (the_cat_of Tom) Dog)
               '(isa Muffet (kind_of Dog))]]
      (let [a (nm/advice s)]                       ; `is` answers a boolean, not the value
        (is (some? a) (pr-str s))
        (is (string? (:message a)) (pr-str s))
        (is (re-find #"unary type predicate" (:message a))
            "and falls back to the generic form rather than guessing a rewrite"))))
  (testing "nothing legitimate draws it"
    (doseq [s ['(dog Muffet)
               '(genl dog thing)
               '(arg parentOf 1 dog)          ; a different predicate entirely
               '(likes Tom Ann)
               '(isa Muffet)                        ; not the two-place shape
               '(isa Muffet Dog Extra)]]
      (is (nil? (nm/advice s)) (pr-str s))))
  (testing "advise! is silent under :naming :off, which asks for no policing"
    ;; reach past the once-per-process check by asking the pure fn either side of it
    (is (some? (nm/advice '(isa Muffet Dog))))
    (is (nil? (nm/advise! :off '(isa Muffet Dog) 'CxUniverse)))))

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
    (is (empty? (nm/problems* '(abrasive-grit Muffet) 'CxUniverse)))
    (is (= [:functor-arity]
           (mapv :class (nm/problems* '(abrasive-grit Muffet Rex) 'CxUniverse))))))

(deftest a-lexeme-is-parse-input-and-is-marked-by-its-namespace
  (testing "the namespace decides it, and the text is not ours to spell"
    (doseq [s '[lex/thing lex/fool's_gold lex/a_la_carte]]
      (is (= :lexeme (v/term-role s)) (pr-str s))
      (is (nm/lexeme? s))))
  (testing "the name half keeps characters a spelling marker would collide with"
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
           (mapv :class (nm/problems* '(lex/fools_gold Muffet) 'CxUniverse)))))
  (testing "but as an argument it is ordinary, which is what lets a sense be stated"
    (is (empty? (nm/problems* '(sense lex/fools_gold fools_gold-mineral)
                              'CxUniverse))))
  (testing "and what lets an unsensified edge stand until a sense is crafted for it"
    (is (empty? (nm/problems* '(genl abrasive-grit lex/abrasive_tool)
                              'CxUniverse)))))

(deftest a-name-the-reader-would-not-read-back-is-refused
  (testing "a leading digit is parsed as a malformed number, not a symbol"
    (is (thrown? Exception (read-string "134a-gas")))
    (is (nil? (v/term-role (symbol "134a-gas")))))
  (testing "and the escaped spelling reads, and is a sense"
    (is (= :sense (v/term-role (read-string "_134a-gas")))))
  (testing "a leading apostrophe is the quote macro, so it never names anything"
    (is (seq? (read-string "'centaur'-mythical")))
    (is (= :sense (v/term-role (read-string "_'centaur'-mythical"))))))

;;; ── the class table and its renderer are one thing ────────────────────

(def ^:private class-samples
  "One sentence per `problem-classes` key, the context to check it in, and the symbol
  the violation names."
  {:context-name   ['(dog Muffet)                  'NotAThing 'NotAThing]
   :functor        ['(Flies Tweety)                'CxWell    'Flies]
   :lexeme-functor ['(lex/fools_gold Muffet)       'CxWell    'lex/fools_gold]
   :functor-arity  ['(lives_in Tweety cold_place)  'CxWell    'lives_in]
   :functor-unary  ['(warmBlooded Muffet)          'CxWell    'warmBlooded]
   :argument       ['(parentOf Baby_Penguin Tom)   'CxWell    'Baby_Penguin]
   :ist-context    ['(ist Muffet (flies Tweety))   'CxWell    'Muffet]})

(deftest every-problem-class-renders-a-message
  ;; `message` is a `case` over the `problem-classes` keys: a class with no arm would throw
  ;; IllegalArgumentException out of `assert` instead of an `ex-info` carrying `:naming`
  (testing "a new class owes this test a sentence that produces it"
    (is (= (set (keys nm/problem-classes)) (set (keys class-samples)))))
  (doseq [[cls [sentence context sym]] class-samples]
    (testing (str cls)
      (let [ps (nm/problems* sentence context)]
        (is (= [{:class cls :role :sentence :symbol sym}] (map #(dissoc % :literal) ps))
            "that sentence produces this class alone, naming the symbol that broke")
        (doseq [p ps]
          (is (seq (nm/message p)) "and every violation it reports renders")))
      (is (seq (nm/problems sentence context))))))

(deftest a-sense-at-the-wrong-arity-is-not-told-to-camelcase-itself
  ;; a sense has no camelCase spelling, so the snake_case repair would name it back
  (let [[m] (nm/problems '(abrasive-grit Muffet Rex) 'CxUniverse)]
    (is (re-find #"is a sense" m))
    (is (not (re-find #"snake_case" m)))
    (is (not (re-find #"camelCase as abrasive-grit" m))))
  (testing "and the snake_case repair still names the camelCase spelling"
    (let [[m] (nm/problems '(lives_in Tweety cold_place) 'CxUniverse)]
      (is (re-find #"camelCase as livesIn" m)))))

(deftest a-lexeme-functor-is-refused-as-an-ex-info-not-a-crash
  (tu/with-cleared-kb [kb (kb-with :strict)]
    (let [e (try (v/assert kb '(lex/fools_gold Muffet) 'CxWell) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "a lexeme applied to arguments is refused")
      (is (= :naming (:type (ex-data e))))
      (is (re-find #"is a lexeme" (ex-message e)))
      (is (zero? (v/sentex-count kb)) "and nothing was stored"))))
