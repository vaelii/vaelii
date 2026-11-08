;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.shipped-rigidity-test
  "The rigidity kinds the shipped ontology states for its own relations.

  Each family is read through one or more representative members, in the context that
  sees the family's definitions.  A relation of one kind is believed of no other, so each
  check reads all three kinds."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private kinds
  '[time_invariant_relation time_agnostic_relation time_varying_relation])

(defn- kinds-of
  "The rigidity kinds `relation` is believed to have in `context`."
  [kb relation context]
  (set (filter #(v/ask? kb (list % relation) context) kinds)))

(defn- all-of-kind
  [kb kind relations context]
  (doseq [r relations]
    (is (= #{kind} (kinds-of kb r context)) (str r " is " kind " and of no other kind"))))

(defn- all-eternal
  "Each of `relations` is eternal in `context`, and so time-invariant and of no other kind."
  [kb relations context]
  (all-of-kind kb 'time_invariant_relation relations context)
  (doseq [r relations]
    (is (true? (v/ask? kb (list 'eternal_predicate r) context)) (str r " is eternal"))))

(tu/deftest-kb eternal-documentation-does-not-assert-its-quoted-example
  (tu/with-terms [example_kind ExamplePerson]
    (v/assert kb (list 'unary_predicate example_kind) 'CxUniverse)
    (v/assert kb (list 'genl example_kind 'tangible) 'CxUniverse)
    (v/assert kb (list 'time_varying_relation example_kind) 'CxUniverse)
    (is (true? (v/ask? kb '(eternal_predicate positiveExample) 'CxUniverse)))
    (v/assert kb (list 'positiveExample example_kind
                       (list 'Quote (list example_kind ExamplePerson)))
              'CxUniverse)
    (is (not (v/ask? kb (list example_kind ExamplePerson) 'CxUniverse))
        "an eternal annotation does not establish its quoted example")
    (is (not (v/ask? kb (list 'eternal_predicate example_kind) 'CxUniverse))
        "documenting a time-varying kind does not make that kind eternal")))

(tu/deftest-kb atemporal-members-need-rigidity-for-the-eternal-bridge
  (tu/with-terms [fixed_number_type selected_number_type eternal_time_type]
    (doseq [sentence [(list 'unary_predicate fixed_number_type)
                      (list 'genl fixed_number_type 'number)
                      (list 'time_invariant_relation fixed_number_type)
                      (list 'unary_predicate selected_number_type)
                      (list 'genl selected_number_type 'number)
                      (list 'time_varying_relation selected_number_type)
                      (list 'unary_predicate eternal_time_type)
                      (list 'genl eternal_time_type 'time_interval)
                      (list 'eternal_predicate eternal_time_type)]]
      (v/assert kb sentence 'CxUniverse))
    (is (true? (v/ask? kb (list 'eternal_predicate fixed_number_type) 'CxUniverse))
        "invariant unary membership over atemporal things is eternal")
    (is (not (v/ask? kb (list 'eternal_predicate selected_number_type) 'CxUniverse))
        "atemporal members do not make changing membership eternal")
    (is (not (v/ask? kb (list 'genl eternal_time_type 'atemporal) 'CxUniverse))
        "eternal unary membership does not imply atemporal members")
    (v/retract! kb (v/handle-of kb (list 'time_invariant_relation fixed_number_type) 'CxUniverse))
    (is (not (v/ask? kb (list 'eternal_predicate fixed_number_type) 'CxUniverse))
        "withdrawing rigidity removes the derived eternal mark despite the invariant supertype")))

(tu/deftest-kb sempiternal-bridge-covers-time-and-situation
  (tu/with-terms [fixed_time_type fixed_situation_type varying_situation_type]
    (doseq [sentence [(list 'unary_predicate fixed_time_type)
                      (list 'genl fixed_time_type 'time)
                      (list 'time_invariant_relation fixed_time_type)
                      (list 'unary_predicate fixed_situation_type)
                      (list 'genl fixed_situation_type 'situation)
                      (list 'time_invariant_relation fixed_situation_type)
                      (list 'unary_predicate varying_situation_type)
                      (list 'genl varying_situation_type 'situation)]]
      (v/assert kb sentence 'CxUniverse))
    (is (true? (v/ask? kb (list 'eternal_predicate fixed_time_type) 'CxUniverse))
        "a time-invariant spec of time is eternal through the sempiternal bridge")
    (is (true? (v/ask? kb (list 'eternal_predicate fixed_situation_type) 'CxUniverse))
        "a time-invariant spec of situation is eternal through the sempiternal bridge")
    ;; Every spec of situation is concluded time_invariant_relation unconditionally (the
    ;; forward rule above, pre-existing and unconditioned on this bridge), so an ordinary
    ;; default-strength (time_varying_relation ...) on a genl of situation only ties with
    ;; that conclusion instead of beating it.  Asserted :monotonic, it wins outright, and
    ;; the sempiternal bridge correctly stays one-way: time-varying membership over a
    ;; sempiternal type is not swept into eternal_predicate.
    (v/assert kb (list 'time_varying_relation varying_situation_type) 'CxUniverse
              {:strength :monotonic})
    (is (not (v/ask? kb (list 'time_invariant_relation varying_situation_type) 'CxUniverse))
        "a monotonic time-varying mark defeats the inherited time-invariant conclusion")
    (is (not (v/ask? kb (list 'eternal_predicate varying_situation_type) 'CxUniverse))
        "a time-varying spec of situation is not eternal")))

(tu/deftest-kb selected-value-and-metatype-kinds-are-time-invariant
  (testing "the shipped fixed value and expression kinds"
    (all-of-kind kb 'time_invariant_relation
                 '[number non_positive_integer atomic_expression open_expression
                   ill_formed_expression logical aspatial atemporal]
                 'CxUniverse))
  (testing "types over relations, functions and types"
    (all-of-kind kb 'time_invariant_relation
                 '[relation unary_function binary_predicate symmetric type
                   time_varying_relation]
                 'CxUniverse))
  (testing "every member of arity_type, through one genl edge"
    (is (v/ask? kb '(genl arity_type time_invariant_relation) 'CxUniverse))
    (all-of-kind kb 'time_invariant_relation '[unary binary at_least_binary variable_arity]
                 'CxUniverse))
  (testing "metatypes"
    (all-of-kind kb 'time_invariant_relation
                 '[stuff_type_by_state_of_matter folk_species vertebrate_class rigidity_kind
                   at_least_metatype arity_type]
                 'CxUniverse)))

(tu/deftest-kb folk-kinds-are-time-invariant
  (is (v/ask? kb '(genl folk_species time_invariant_relation) 'CxUniverse))
  (is (v/ask? kb '(genl folk_biological_class time_invariant_relation) 'CxUniverse))
  (all-of-kind kb 'time_invariant_relation
               '[mouse human dog rose oak flower mammal bird insect arachnid tree]
               'CxUniverse))

(tu/deftest-kb meta-and-logical-predicates-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[arity admitsArgnum arityMin functionCorrespondingPredicate implies not and
                 forall thereExists equals different lessThan termsRelated
                 borderlineExample comment]
               'CxUniverse))

(tu/deftest-kb equality-predicates-are-eternal-like-rewriteOf
  (all-eternal kb '[sameAs equals different rewriteOf] 'CxUniverse)
  (doseq [r '[sameAs equals different]]
    (is (not (v/ask? kb (list 'not (list 'eternal_predicate r)) 'CxUniverse))
        (str r " carries no non-eternal mark"))))

(tu/deftest-kb interpretation-predicates-are-time-agnostic
  (all-of-kind kb 'time_agnostic_relation '[means denotes] 'CxUniverse))

(tu/deftest-kb kinship-and-biology-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[parentOf childOf motherOf fatherOf ancestorOf siblingOf birthYearOf mortal
                 warm_blooded MotherFn FatherFn]
               'CxUniverse))

(tu/deftest-kb social-relations-are-time-varying
  (all-of-kind kb 'time_varying_relation
               '[worksFor friendOf likes owns memberOf marriedTo speaks]
               'CxUniverse)
  (testing "CxSocial's own relations, in the context that defines them"
    (all-of-kind kb 'time_varying_relation '[coworkerOf roommateOf romanticPartnerOf]
                 'CxSocial)))

(tu/deftest-kb a-quantitys-sign-trend-and-derivative-are-time-varying
  (all-of-kind kb 'time_varying_relation '[signOf trendOf derivativeOf] 'CxUniverse))

(tu/deftest-kb spatial-relations-are-time-agnostic
  ;; A ship very far from its home port can sail home, and two points of a mathematical
  ;; plane can never move, so some instances could lose the relation and some could not.
  (all-of-kind kb 'time_agnostic_relation
               '[veryFarFrom moderatelyFarFrom northwestOf behindRightOf eastOf
                 withinNearDistanceOf]
               'CxUniverse)
  (all-of-kind kb 'time_invariant_relation '[regionConnectedTo] 'CxUniverse)
  (is (v/ask? kb '(eternal_predicate regionConnectedTo) 'CxUniverse)))

(tu/deftest-kb taxonomy-is-agnostic-and-argument-declarations-remain-invariant
  (all-of-kind kb 'time_agnostic_relation
               '[disjoint partition covering separating orthogonal genl typeGenl typeOrthogonal]
               'CxUniverse)
  (all-of-kind kb 'time_invariant_relation
               '[intersection genlCx arg genlArg result defnIff transitiveInArg]
               'CxUniverse))

(tu/deftest-kb every-spec-of-time-and-of-situation-is-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[time uninterrupted_time intermittent_time time_interval time_point
                 situation uninterrupted_situation fluent happening event static_situation
                 causal_event]
               'CxUniverse)
  (testing "a spec stated after the rules"
    (tu/with-terms [lunchHour lunchBreak]
      (doseq [t [lunchHour lunchBreak]]
        (v/assert kb (list 'unary_predicate t) 'CxUniverse))
      (v/assert kb (list 'genl lunchHour 'time_interval) 'CxUniverse)
      (v/assert kb (list 'genl lunchBreak 'event) 'CxUniverse)
      (all-of-kind kb 'time_invariant_relation [lunchHour lunchBreak] 'CxUniverse))))

(tu/deftest-kb permanent-parthood-is-a-time-invariant-spec-of-partOf
  (all-of-kind kb 'time_invariant_relation '[permanentPartOf partOfRegion] 'CxUniverse)
  (is (v/genl? kb 'permanentPartOf 'partOf))
  (is (v/genl? kb 'partOfRegion 'permanentPartOf))
  (is (v/genl? kb 'subSituationOf 'permanentPartOf))
  (is (not (v/genl? kb 'tangiblePartOf 'permanentPartOf)) "a wheel can come off a car")
  (tu/with-terms [Kitchen House]
    (v/assert kb (list 'partOfRegion Kitchen House) 'CxUniverse)
    (is (true? (v/ask? kb (list 'permanentPartOf Kitchen House) 'CxUniverse)))))

(tu/deftest-kb stable-once-true-and-stable-once-false-are-time-varying-and-never-invariant
  ;; Once an organism is dead it stays dead, and once it is not alive it is never alive
  ;; again.  Each persistence kind is a kind of time-varying relation: a relation no
  ;; instance could lose is not one of them.
  (doseq [k '[stable_once_true stable_once_false]]
    (is (seq (v/ask kb (list 'comment k '?c) 'CxUniverse)) (str k " is commented"))
    (is (v/genl? kb k 'time_varying_relation) (str k " is below time_varying_relation"))
    (is (v/disjoint? kb k 'time_invariant_relation 'CxUniverse)
        (str "no time-invariant relation is " k)))
  (is (v/ask? kb '(stable_once_true dead) 'CxUniverse))
  (is (v/ask? kb '(stable_once_false alive) 'CxUniverse))
  (all-of-kind kb 'time_varying_relation '[dead alive] 'CxUniverse)
  (doseq [r '[parentOf birthYearOf]]
    (is (not (v/ask? kb (list 'stable_once_true r) 'CxUniverse)))
    (is (not (v/ask? kb (list 'stable_once_false r) 'CxUniverse)))))

(tu/deftest-kb biological-history-is-fixed-but-current-chosen-kinship-can-change
  (all-of-kind kb 'time_invariant_relation '[grandparentOf madeOf] 'CxUniverse)
  (all-of-kind kb 'time_invariant_relation '[originatorOf] 'CxSocial)
  (all-of-kind kb 'time_agnostic_relation '[relativeOf] 'CxSocial)
  (is (v/ask? kb '(not (eternal_predicate relativeOf)) 'CxSocial))
  (all-of-kind kb 'time_varying_relation '[breathes_air preysOn] 'CxUniverse))

(tu/deftest-kb contains-and-the-durations-are-time-invariant
  (all-of-kind kb 'time_invariant_relation '[contains length totalDuration overlapDuration]
               'CxUniverse))

(tu/deftest-kb the-integrity-requirements-placeholders-and-contradicts-are-classified
  (all-of-kind kb 'time_varying_relation
               '[typeAllSpecified predAllSpecified predSpecifiedAll]
               'CxUniverse)
  (all-of-kind kb 'time_invariant_relation
               '[predAllExistsPlaceholder predExistsAllPlaceholder
                 predExistsInstancePlaceholder predInstanceExistsPlaceholder]
               'CxUniverse)
  (testing "each Pred...Fn takes its placeholder's kind through the correspondence"
    (all-of-kind kb 'time_invariant_relation
                 '[PredAllExistsFn PredExistsAllFn PredExistsInstanceFn PredInstanceExistsFn]
                 'CxUniverse))
  (all-of-kind kb 'time_agnostic_relation
               '[predAllExists predAllInstance predExistsAll predExistsInstance
                 predInstanceAll predInstanceExists contradicts]
               'CxUniverse))

(tu/deftest-kb magnitude-comparison-and-qualitative-arithmetic-are-time-varying
  (all-of-kind kb 'time_varying_relation
               '[greaterInMagnitudeThan qualitativeSum qualitativeProduct qualitativeDifference]
               'CxUniverse))

(tu/deftest-kb a-software-tool-is-time-invariant-and-a-phase-of-matter-time-varying
  (is (v/ask? kb '(genl stuff_type_by_state_of_matter time_varying_relation) 'CxUniverse))
  (all-of-kind kb 'time_varying_relation '[solid liquid gas plasma] 'CxUniverse)
  (all-of-kind kb 'time_invariant_relation '[software_tool] 'CxTra))

(tu/deftest-kb acquaintance-place-eating-capability-and-sleep-are-time-varying
  (all-of-kind kb 'time_varying_relation
               '[knows livesIn locatedIn eats hasCapability asleep awake]
               'CxUniverse)
  (all-of-kind kb 'time_varying_relation '[chosenSiblingOf nestingPartnerOf]
               'CxTra))

(tu/deftest-kb the-upper-categories-and-biological-kinds-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[thing spatial temporal spatiotemporal physical tangible intangible causal
                 acausal uninterrupted intermittent biological organism animal plant
                 vertebrate invertebrate person body_part feather fin fur leaf leg petal
                 root wing]
               'CxUniverse))

(tu/deftest-kb made-things-stuffs-and-media-are-time-invariant-and-dwelling-and-access-time-varying
  (all-of-kind kb 'time_invariant_relation
               '[made natural formation machine vehicle building container furniture
                 clothing substance metal_stuff stone wood glass_stuff mercury organization]
               'CxUniverse)
  (all-of-kind kb 'time_agnostic_relation '[food] 'CxUniverse)
  (all-of-kind kb 'time_varying_relation '[dwelling] 'CxSocial)
  (all-of-kind kb 'time_invariant_relation
               '[computational_system command_line_tool mcp_tool information
                 digital_artifact media_resource image video]
               'CxTra)
  (all-of-kind kb 'time_varying_relation
               '[read_only_software_tool write_capable_software_tool]
               'CxTra))

(tu/deftest-kb the-event-calculus-relations-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[holdsAt happens initiates terminates clipped clippedBefore causes]
               'CxUniverse)
  (testing "CxTra's happening kinds are specs of situation"
    (all-of-kind kb 'time_invariant_relation '[tool_invocation tool_receipt image_viewing]
                 'CxTra)))

(tu/deftest-kb the-calendar-and-time-point-relations-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[calendarDay calendarInstant calendarMonth calendarYear datetimeOf timeOf
                 startOf endOf earliestStartOf earliestEndOf latestStartOf latestEndOf
                 temporalDistance]
               'CxUniverse)
  (testing "each time-point function takes its predicate's kind through the correspondence"
    (all-of-kind kb 'time_invariant_relation
                 '[DayFn InstantFn MonthFn YearFn DatetimeFn TimeOfFn StartFn EndFn
                   EarliestStartFn EarliestEndFn LatestStartFn LatestEndFn]
                 'CxUniverse)))

(tu/deftest-kb the-kb-state-relations-are-time-varying-and-implementationNote-time-invariant
  ;; Each tracks a store or a mind that changes.  An implementation note is about a term,
  ;; as a comment is.
  (all-of-kind kb 'time_varying_relation
               '[empty nonempty believes indeterminate_term agg/avg agg/count agg/max agg/min
                 agg/sum]
               'CxUniverse)
  (all-of-kind kb 'time_varying_relation '[toolName] 'CxTra)
  (all-of-kind kb 'time_invariant_relation '[implementationNote] 'CxUniverse))

(tu/deftest-kb the-temporal-order-relations-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[after before during meets metBy overlaps overlappedBy starts startedBy
                 finishes finishedBy precedes precededBy subintervalOf properSubintervalOf
                 hasSubinterval includesInstant intervalEqual instantAfter instantBefore
                 instantEqual instantNotAfter instantNotBefore instantNotEqual sharesTimeWith
                 temporallyDisjoint]
               'CxUniverse))

(tu/deftest-kb quantities-their-comparators-and-birth-order-are-time-invariant
  (all-of-kind kb 'time_invariant_relation
               '[quantity measureInUnit measureRangeInUnit quantityGreaterThan
                 quantityGreaterThanOrEqual quantityLessThan quantityLessThanOrEqual
                 sameQuantity olderThan]
               'CxUniverse)
  (testing "each quantity function takes its predicate's kind through the correspondence"
    (all-of-kind kb 'time_invariant_relation '[QuantityFn QuantityIntervalFn] 'CxUniverse)))

(tu/deftest-kb height-weight-and-their-comparisons-are-time-varying
  (all-of-kind kb 'time_varying_relation '[heightOf weightOf tallerThan heavierThan]
               'CxUniverse))

(tu/deftest-kb kind-level-parts-and-capabilities-allow-slice-dependent-profiles
  (all-of-kind kb 'time_agnostic_relation '[partType capabilityType] 'CxUniverse))

(tu/deftest-kb parthood-is-time-agnostic-tangible-parthood-time-varying-and-situation-parthood-time-invariant
  ;; A wheel can come off a car and both go on existing, while a part of an event or a
  ;; region cannot stop being one.
  (all-of-kind kb 'time_agnostic_relation '[partOf] 'CxUniverse)
  (all-of-kind kb 'time_varying_relation '[tangiblePartOf] 'CxUniverse)
  (all-of-kind kb 'time_invariant_relation '[subSituationOf] 'CxUniverse)
  (testing "properTangiblePartOf is time-varying through its genl edge to tangiblePartOf"
    (all-of-kind kb 'time_varying_relation '[properTangiblePartOf] 'CxUniverse)))

(tu/deftest-kb mechanisms-are-time-invariant-and-hollow-time-varying
  ;; A stopped clock is still a mechanism and a dead phone still an electronic device,
  ;; but a box crushed flat is no longer hollow and is still a box.
  (all-of-kind kb 'time_invariant_relation '[mechanism electronic_device] 'CxUniverse)
  (all-of-kind kb 'time_varying_relation '[hollow] 'CxUniverse))

(tu/deftest-kb every-life-stage-is-time-varying
  ;; A caterpillar stops being a caterpillar and goes on existing as a butterfly.  One
  ;; genl edge classifies every member of life_stage_type, and the metatype itself is
  ;; one of the shipped invariant classifiers.
  (is (seq (v/ask kb '(comment life_stage_type ?c) 'CxUniverse)) "life_stage_type is commented")
  (is (v/ask? kb '(genl life_stage_type time_varying_relation) 'CxUniverse))
  (all-of-kind kb 'time_invariant_relation '[life_stage_type] 'CxUniverse)
  (doseq [s '[caterpillar butterfly]]
    (is (true? (v/ask? kb (list 'life_stage_type s) 'CxUniverse)) (str s " is a life stage")))
  (all-of-kind kb 'time_varying_relation '[caterpillar butterfly] 'CxUniverse))

(tu/deftest-kb tool-invocations-and-tool-declarations-are-time-invariant-and-tool-access-time-varying
  ;; A call is of the tool it called and produced the receipt it produced, and a tool
  ;; version's declared arguments and probed predicates are fixed.  An agent can gain or
  ;; lose a tool and go on existing.
  (all-of-kind kb 'time_invariant_relation
               '[toolInvoked receipt probesPredicate toolArgComment toolArgType]
               'CxTra)
  (all-of-kind kb 'time_varying_relation '[agentHasTool] 'CxTra))

(tu/deftest-kb name-resolution-addresses-and-relationship-labels-are-time-varying
  ;; A host name can be pointed at a new address and a resource moved to a new URL, and
  ;; a person can start calling a relationship by another name.
  (all-of-kind kb 'time_varying_relation '[dnsResolvesTo resourceUrl] 'CxTra)
  (all-of-kind kb 'time_varying_relation '[relationshipLabel] 'CxSocial))

(tu/deftest-kb perceiving-is-time-varying-and-a-viewing-time-invariant
  ;; Someone who sees a thing can look away and go on existing, but a viewing of an
  ;; image or a video that happened stays happened.
  (all-of-kind kb 'time_varying_relation '[perceives sees] 'CxTra)
  (all-of-kind kb 'time_invariant_relation '[seeImage watchVideo] 'CxTra))

(tu/deftest-kb the-time-slice-and-monad-vocabulary-is-eternal-and-cxtimefn-time-invariant
  ;; CxTimeFn is a function, so it takes the invariant kind and no eternal_predicate mark.
  (all-eternal kb '[cxMonadOf cxTimeOf datetimeRangeOf genlMonad intervalAfterOf
                    intervalBeforeOf monad_context subtimeOf timeIntersectionOf
                    time_slice_context]
               'CxUniverse)
  (all-of-kind kb 'time_invariant_relation '[CxTimeFn timezone zonedDatetimeOf] 'CxUniverse)
  (is (not (v/ask? kb '(eternal_predicate CxTimeFn) 'CxUniverse)) "CxTimeFn is not eternal")
  (testing "timezone, invariant over strings, is eternal through the sempiternal bridge"
    (is (true? (v/ask? kb '(eternal_predicate timezone) 'CxUniverse)))))

(tu/deftest-kb data-structures-and-their-structural-relations-are-eternal
  (all-eternal kb '[data_structure finite_set list map map_entry multiset entryOf listOf mapOf
                    multisetOf setOf elementOf cardinalityOf multiplicityOf valueAt]
               'CxUniverse))

(tu/deftest-kb counterparts-type-orders-rule-pairs-and-syntax-kinds-are-eternal
  (all-eternal kb '[properCounterpart successorTypeOrder rulePairOf sentex_handle_term
                    syncategorematic]
               'CxUniverse))

(tu/deftest-kb taxonomy-computations-and-life-stage-forms-are-time-agnostic
  (all-of-kind kb 'time_agnostic_relation
               '[maxCommonSpec minCommonGenl negates typeLargerThan adultFormOf larvalFormOf]
               'CxUniverse))

(tu/deftest-kb identity-fixed-computational-resources-are-time-invariant-and-seat-and-construct-time-varying
  ;; A pull request stays the same request through every push, and a Discord message
  ;; the same message through every edit.  A seat can stop hosting a construct, and a
  ;; person's computational realization is not essential to it.
  (all-of-kind kb 'time_invariant_relation
               '[communication_channel computer conceptual_work discord_channel discord_message
                 file_path_reference filesystem_namespace forge_repository kubernetes_namespace
                 pull_request virtual_machine software_container kubernetes_cluster network]
               'CxTra)
  (all-of-kind kb 'time_varying_relation '[seat construct] 'CxTra))
