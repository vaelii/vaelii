;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.meta-test
  "The vocabulary context and meta-level features over the starter schema (with
  the test-world beneath it):

    * the context *spindle* — CoreContext ⊏ upper ⊏ UniverseContext ⊏ middle ⊏ WellContext;
    * the predicate meta-ontology — predicates classified by arity and by the
      algebraic properties their metadata declares (derived into CoreContext by rules
      whose consequent is an ist form);
    * decontextualizedPredicate — a fact stated in one context deduced into
      UniverseContext and thereby visible everywhere."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb the-context-spindle-core-upper-universe-middle-well
  (testing "upper rides between Core and Universe: an upper context sees Core, Universe sees it"
    (is (seq (v/sentexes-matching kb '(genlContext OrganismContext CoreContext) '?ctx)))
    (is (seq (v/sentexes-matching kb '(genlContext UniverseContext OrganismContext) '?ctx))))
  (testing "middle rides between Universe and Well"
    (is (seq (v/sentexes-matching kb '(genlContext BiologyContext UniverseContext) '?ctx)))
    (is (seq (v/sentexes-matching kb '(genlContext WellContext BiologyContext) '?ctx))))
  (testing "there is no direct Well→Core edge, but Core is transitively visible from Well"
    (is (empty? (v/sentexes-matching kb '(genlContext WellContext CoreContext) '?ctx)))
    (is (tax/sees? (:taxonomy kb) 'WellContext 'CoreContext)))
  (testing "CoreContext vocabulary is visible from the collector and the data contexts"
    (is (v/ask? kb '(binaryPredicate genl) 'UniverseContext))
    (is (v/ask? kb '(binaryPredicate parentOf) 'NaturalWorldContext)))
  (testing "the upper ontology rides in the upper contexts, not the collector"
    (is (seq   (v/sentexes-matching kb '(genl dog mammal) 'OrganismContext)))
    (is (empty? (v/sentexes-matching kb '(genl dog mammal) 'UniverseContext)))
    (is (seq   (v/sentexes-matching kb '(person Tom) 'NaturalWorldContext)))))

(tu/deftest-kb predicates-classified-by-arity
  (testing "unary — every type, and one-place properties"
    (is (v/isa? kb 'dog 'unaryPredicate))
    (is (v/isa? kb 'thing 'unaryPredicate))
    (is (v/isa? kb 'flies 'unaryPredicate)))
  (testing "binary and ternary"
    (is (v/isa? kb 'parentOf 'binaryPredicate))
    (is (v/isa? kb 'genl 'binaryPredicate))
    (is (v/isa? kb 'argIsa 'ternaryPredicate)))
  (testing "everything classified is a predicate, hence a thing"
    (is (v/isa? kb 'parentOf 'predicate))
    (is (v/isa? kb 'dog 'predicate))
    (is (v/isa? kb 'parentOf 'thing)))
  (testing "negatives"
    (is (not (v/isa? kb 'dog 'binaryPredicate)))
    (is (not (v/isa? kb 'siblingOf 'unaryPredicate)))))

(tu/deftest-kb arity-and-predicate-type-derive-each-other
  ;; (arity P N) and the N-ary predicate-type membership conclude each other, each
  ;; landing where the declaration it was read off lives — the ordinary placement.
  (testing "arity is itself a binary predicate"
    (is (v/isa? kb 'arity 'binaryPredicate)))
  (testing "an asserted predicate-type concludes the arity, in the declaration's context"
    (is (seq (v/sentexes-matching kb '(arity dog 1) 'CoreContext)))        ; a type is unary
    (is (seq (v/sentexes-matching kb '(arity flies 1) 'LifeContext)))      ; a one-place property
    (is (seq (v/sentexes-matching kb '(arity parentOf 2) 'LifeContext)))
    (is (seq (v/sentexes-matching kb '(arity siblingOf 2) 'LifeContext)))  ; symmetric -> binary -> arity 2
    (is (seq (v/sentexes-matching kb '(arity argIsa 3) 'CoreContext))))
  (testing "the derived arity is a claim of the context that declared the predicate,
            not of the vocabulary head — a private declaration stays private"
    (is (empty? (v/sentexes-matching kb '(arity parentOf 2) 'CoreContext)))
    (is (empty? (v/sentexes-matching kb '(arity parentOf 2) 'NaturalWorldContext)))
    (is (v/isa? kb 'parentOf 'binaryPredicate 'NaturalWorldContext)
        "but a data context below Well still sees it, since it sees LifeContext"))
  (testing "an asserted arity concludes the predicate-type, hence a predicate"
    (tu/with-terms [fooPred]
      (v/assert kb (list 'arity fooPred 2) 'CoreContext)
      (is (v/isa? kb fooPred 'binaryPredicate))
      (is (v/isa? kb fooPred 'predicate))
      (is (seq (v/sentexes-matching kb (list 'binaryPredicate fooPred) 'CoreContext)))))
  (testing "the derived membership is justified by the arity fact and the rule"
    (tu/with-terms [barPred]
      (v/assert kb (list 'arity barPred 3) 'CoreContext)
      (let [h (:id (first (v/sentexes-matching kb (list 'ternaryPredicate barPred) 'CoreContext)))
            d (first (v/supporting-justifications kb h))]
        (is (some #(= (list 'arity barPred 3) (:sentence (v/sentex kb %)))
                  (:antecedents d)))))))

(tu/deftest-kb arity-cycle-is-self-preserving-only-with-an-asserted-member
  ;; the two directions form a positive cycle: (arity P N) <-> (N-ary predicate P).
  ;; A member asserted as a premise grounds the whole cycle; the derived twin cannot
  ;; ground itself, so retracting the sole premise collapses both (well-founded).
  (testing "asserting the arity keeps both the arity and the type believed"
    (tu/with-terms [pPred]
      (let [h (v/assert kb (list 'arity pPred 2) 'CoreContext)]
        (is (seq (v/sentexes-matching kb (list 'arity pPred 2) 'CoreContext)))
        (is (seq (v/sentexes-matching kb (list 'binaryPredicate pPred) 'CoreContext)))
        (testing "retracting the sole premise collapses the whole cycle"
          (v/retract! kb h)
          (is (empty? (v/sentexes-matching kb (list 'binaryPredicate pPred) 'CoreContext)))
          (is (empty? (v/sentexes-matching kb (list 'arity pPred 2) 'CoreContext)))))))
  (testing "asserting the type keeps both the type and the arity believed"
    (tu/with-terms [qPred]
      (let [h (v/assert kb (list 'unaryPredicate qPred) 'CoreContext)]
        (is (seq (v/sentexes-matching kb (list 'arity qPred 1) 'CoreContext)))
        (testing "and retracting it collapses the derived arity"
          (v/retract! kb h)
          (is (empty? (v/sentexes-matching kb (list 'arity qPred 1) 'CoreContext))))))))

(tu/deftest-kb algebraic-predicate-types-derived-from-metadata
  ;; (symmetric siblingOf) etc. drive both the provers AND, via CoreContext rules whose
  ;; consequent is (ist CoreContext (..Predicate ?p)), the predicate-type membership.
  (testing "the property memberships are derived"
    (is (v/isa? kb 'siblingOf 'symmetricPredicate))
    (is (v/isa? kb 'marriedTo 'symmetricPredicate))
    (is (v/isa? kb 'ancestorOf 'transitivePredicate))
    (is (v/isa? kb 'partOf 'transitivePredicate))
    (is (v/isa? kb 'birthYearOf 'functionalPredicate)))
  (testing "and inherit binaryPredicate / predicate through genl"
    (is (v/isa? kb 'siblingOf 'binaryPredicate))
    (is (v/isa? kb 'ancestorOf 'predicate)))
  (testing "the derived membership lands where the metadata was declared, not in the
            vocabulary head — so a context's own (symmetric P) stays its own"
    (is (seq (v/sentexes-matching kb '(symmetricPredicate siblingOf) 'LifeContext)))
    (is (empty? (v/sentexes-matching kb '(symmetricPredicate siblingOf) 'CoreContext)))
    (is (empty? (v/sentexes-matching kb '(symmetricPredicate siblingOf) 'SocialWorldContext)))))

(tu/deftest-kb predicate-type-provers-answer-from-metadata
  (testing "membership is answered directly from the cached metadata"
    (is (v/ask? kb '(symmetricPredicate siblingOf)))
    (is (v/ask? kb '(transitivePredicate ancestorOf)))
    (is (v/ask? kb '(functionalPredicate birthYearOf)))
    (is (not (v/ask? kb '(symmetricPredicate parentOf)))))
  (testing "and enumerated"
    (is (= '#{siblingOf marriedTo friendOf}
           (set (map #(get % '?p) (v/ask kb '(symmetricPredicate ?p) '?ctx)))))
    ;; `genl` and `genlContext` are in the enumeration because CoreContext says so
    ;; outright.  They *are* transitive predicates; answering them from cached closures
    ;; instead of the generic prover is an implementation choice, not a difference in
    ;; what they mean — and saying so is what lets them be named as the relation an
    ;; argument position is preserved along (docs/inherit.md).  The `transitive` *mark*
    ;; is still deliberately not asserted of them, which is why they do not appear in
    ;; `(props kb :transitive)`.
    (is (= '#{ancestorOf partOf locatedIn largerThan causes beforeEvent genl genlContext}
           (set (map #(get % '?p) (v/ask kb '(transitivePredicate ?p) '?ctx)))))
    (is (not (v/has-prop? kb :transitive 'genl)))))

(tu/deftest-kb genlcontext-is-a-forced-decontextualized-predicate
  (testing "a genlContext edge is forced to live in UniverseContext, wherever asserted"
    (is (seq   (v/sentexes-matching kb '(genlContext UniverseContext OrganismContext) 'UniverseContext)))
    (is (empty? (v/sentexes-matching kb '(genlContext UniverseContext OrganismContext) 'CoreContext))))    ; forced away from CoreContext
  (testing "the closure is intact — CoreContext vocabulary is still visible from UniverseContext"
    (is (v/ask? kb '(binaryPredicate genl) 'UniverseContext))))

;; ---- decontextualizedPredicate: a fact that belongs to the KB, not to one theory --
;;
;; `(decontextualizedPredicate P)` deduces every `(P ...)` into UniverseContext, which
;; every context sees.  UniverseContext and not a named target: the definitional
;; checks are context-scoped and run where the fact is stated, so a target the stating
;; context cannot see is a place those checks never look — two facts, each admissible
;; where it was stated, could meet there as a disjointness violation nothing reports.

(tu/deftest-kb the-lift-is-documented-as-an-inert-dotted-rule
  (testing "the dotted rule the code implements is stored (as documentation)"
    (is (seq (v/sentexes-matching kb '(implies (?pred . ?args) (ist UniverseContext (?pred . ?args))) 'CoreContext)))))

(tu/deftest-kb a-decontextualized-fact-reaches-the-universe
  ;; birthPlaceOf is used here as a defensibly decontextualized predicate:
  ;; a birthplace, unlike a marriage, is genuinely context-independent.
  (tu/with-terms [birthPlaceOf Ann Springfield AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'binaryPredicate birthPlaceOf) 'CoreContext)
    (v/assert kb (list 'decontextualizedPredicate birthPlaceOf) 'UniverseContext)
    (v/assert kb (list birthPlaceOf Ann Springfield) AlphaContext)
    (testing "the fact is copied into UniverseContext"
      (is (seq (v/sentexes-matching kb (list birthPlaceOf Ann Springfield) 'UniverseContext))))
    (testing "the copy is justified by the placement sentex and the declaration"
      (let [u (:id (first (v/sentexes-matching kb (list birthPlaceOf Ann Springfield) 'UniverseContext)))
            d (first (v/supporting-justifications kb u))]
        (is (= 'decontextualizedPredicate (:informant d)))
        (is (= 2 (count (:antecedents d))))
        (is (some #(= (list 'decontextualizedPredicate birthPlaceOf) (:sentence (v/sentex kb %)))
                  (:antecedents d)))))
    (testing "and the declaration reads back as predicate metadata"
      (is (v/has-prop? kb :decontextualized birthPlaceOf))
      (is (not (v/has-prop? kb :decontextualized 'owns))))))

(tu/deftest-kb declaring-it-lifts-facts-already-asserted
  ;; The retroactive sweep, the half a declaration-then-facts test never exercises: a
  ;; broken one looks like it works for everything asserted afterwards.
  (tu/with-terms [rulesOver Ann Bob Cid Dee AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list rulesOver Ann Bob) AlphaContext)
    (testing "before the declaration the fact is confined to its own context"
      (is (empty? (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext))))

    (v/assert kb (list 'decontextualizedPredicate rulesOver) 'UniverseContext)
    (testing "declaring it lifts the fact that was already there"
      (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext))))
    (testing "and facts asserted afterwards are lifted too"
      (v/assert kb (list rulesOver Cid Dee) AlphaContext)
      (is (seq (v/sentexes-matching kb (list rulesOver Cid Dee) 'UniverseContext))))))

(tu/deftest-kb retracting-the-declaration-withdraws-the-lifted-copies
  (tu/with-terms [rulesOver Ann Bob AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (let [dh (v/assert kb (list 'decontextualizedPredicate rulesOver) 'UniverseContext)]
      (v/assert kb (list rulesOver Ann Bob) AlphaContext)
      (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext)))

      (v/retract! kb dh)
      (testing "the copy goes with the declaration that licensed it"
        (is (empty? (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext))))
      (testing "and the metadata follows"
        (is (not (v/has-prop? kb :decontextualized rulesOver))))
      (testing "the fact itself is untouched — only the copy rested on the declaration"
        (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) AlphaContext)))))))

;; ---- the lift reaches derived content, in any order ---------------------
;;
;; A decontextualized predicate is a claim about the *predicate*, so what a rule
;; concludes is lifted exactly as what a caller asserts.  Lifting only asserted content
;; made belief depend on arrival order — declare-then-derive left the conclusion where
;; it was concluded, while derive-then-declare lifted it through the retroactive sweep —
;; and the two are the same knowledge.

(tu/deftest-kb a-derived-conclusion-is-lifted-like-an-asserted-fact
  (tu/with-terms [bornInFrance speaksFrench Ann AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'decontextualizedPredicate speaksFrench) 'UniverseContext)
    (v/assert-rule kb [(list bornInFrance '?x)] (list speaksFrench '?x) AlphaContext)
    (v/assert kb (list bornInFrance Ann) AlphaContext)

    (testing "the rule concludes in its own context"
      (is (seq (v/sentexes-matching kb (list speaksFrench Ann) AlphaContext))))
    (testing "and the conclusion is lifted, exactly as an asserted fact would be"
      (is (seq (v/sentexes-matching kb (list speaksFrench Ann) 'UniverseContext))))
    (testing "the copy names the declaration that licensed it, so `why` points at what to retract"
      (let [u (:id (first (v/sentexes-matching kb (list speaksFrench Ann) 'UniverseContext)))
            d (first (v/supporting-justifications kb u))]
        (is (= 'decontextualizedPredicate (:informant d)))
        (is (some #(= (list 'decontextualizedPredicate speaksFrench)
                      (:sentence (v/sentex kb %)))
                  (:antecedents d)))))
    (testing "retracting the fact takes the conclusion and its copy with it"
      (v/retract! kb (:id (first (v/sentexes-matching kb (list bornInFrance Ann) AlphaContext))))
      (is (empty? (v/sentexes-matching kb (list speaksFrench Ann) AlphaContext)))
      (is (empty? (v/sentexes-matching kb (list speaksFrench Ann) 'UniverseContext))))))

(tu/deftest-kb the-lift-is-independent-of-the-order-its-parts-arrive
  ;; Declaration, rule and fact in all six orders: same beliefs, or the engine's
  ;; order-independence invariant is broken by the lift.
  (let [outcomes (mapv (fn [order]
                         (tu/with-terms [bornInFrance speaksFrench Ann AlphaContext]
                           (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
                           (doseq [step order]
                             (case step
                               :decl (v/assert kb (list 'decontextualizedPredicate speaksFrench)
                                               'UniverseContext)
                               :rule (v/assert-rule kb [(list bornInFrance '?x)] (list speaksFrench '?x) AlphaContext)
                               :fact (v/assert kb (list bornInFrance Ann) AlphaContext)))
                           [(boolean (seq (v/sentexes-matching kb (list speaksFrench Ann) AlphaContext)))
                            (boolean (seq (v/sentexes-matching kb (list speaksFrench Ann) 'UniverseContext)))]))
                       [[:decl :rule :fact] [:decl :fact :rule]
                        [:rule :decl :fact] [:rule :fact :decl]
                        [:fact :decl :rule] [:fact :rule :decl]])]
    (is (= [[true true]] (distinct outcomes))
        "every order concludes in the rule's context and lifts into UniverseContext")))

(tu/deftest-kb a-rule-over-a-lifted-predicate-reaches-a-fixpoint
  ;; The copy is a new datum in a context the rule can see, so it goes back on the
  ;; agenda and the rule fires on it.  Justification dedup is what stops that being a
  ;; loop: re-deriving a sentence already stored adds no handle, so the agenda drains.
  (tu/with-terms [connects A B C D AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'decontextualizedPredicate connects) 'UniverseContext)
    (v/assert-rule kb [(list connects '?x '?y) (list connects '?y '?z)]
                   (list connects '?x '?z) AlphaContext)
    (v/assert kb (list connects A B) AlphaContext)
    (v/assert kb (list connects B C) AlphaContext)
    (v/assert kb (list connects C D) AlphaContext)
    (testing "the transitive closure of a 3-edge path is 6 edges, derived once"
      (is (= 6 (count (v/sentexes-matching kb (list connects '?x '?y) AlphaContext))))
      (is (= 6 (count (v/sentexes-matching kb (list connects '?x '?y) 'UniverseContext)))))
    (testing "and the run completed rather than hitting the depth guard"
      (is (not (:truncated? (:last (v/chain-stats kb))))))))

(tu/deftest-kb an-exception-in-the-universe-sees-the-lifted-copy
  ;; The copy goes through the derivation-path choke point, so its arrival is a
  ;; re-check trigger like any other fact's.  Without that the exception would never be
  ;; re-evaluated and the conclusion it should block would stand.
  (tu/with-terms [bird flies penguin Opus AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'decontextualizedPredicate penguin) 'UniverseContext)
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule
                             (list 'implies (list 'and (list bird '?x)) (list flies '?x))))
              'UniverseContext)
    (v/assert kb (list bird Opus) 'UniverseContext)
    (is (v/ask? kb (list flies Opus) 'UniverseContext) "nothing excepts it yet")

    ;; the penguin fact is stated in a context the rule cannot see; only the lift
    ;; brings it into range
    (v/assert kb (list penguin Opus) AlphaContext)
    (is (seq (v/sentexes-matching kb (list penguin Opus) 'UniverseContext)) "lifted into the rule's context")
    (is (not (v/ask? kb (list flies Opus) 'UniverseContext))
        "the arriving copy re-triggered the exception, which now blocks")))

(tu/deftest-kb two-declarations-are-two-witnesses-for-one-copy
  ;; The declaration is not forced-decontextualized, so the same claim stated in two
  ;; contexts is two sentexes.  One copy, justified once per declaration — as a migrated
  ;; twin is justified once per equality — so dropping one leaves the copy standing.
  (tu/with-terms [rulesOver Ann Bob AlphaContext BetaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext BetaContext 'UniverseContext) 'UniverseContext)
    (let [d1 (v/assert kb (list 'decontextualizedPredicate rulesOver) AlphaContext)
          d2 (v/assert kb (list 'decontextualizedPredicate rulesOver) BetaContext)]
      (is (not= d1 d2) "two contexts, two sentexes")
      (v/assert kb (list rulesOver Ann Bob) AlphaContext)
      (let [u (:id (first (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext)))]
        (is (= 2 (count (v/supporting-justifications kb u))) "one witness per declaration")
        (v/retract! kb d1)
        (is (seq (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext))
            "the copy stands on the surviving declaration")
        (v/retract! kb d2)
        (is (empty? (v/sentexes-matching kb (list rulesOver Ann Bob) 'UniverseContext))
            "and goes when the last one does")))))

(tu/deftest-kb a-consequence-of-a-lifted-fact-is-lifted-in-turn
  ;; The copy is a chaining seed, and what that buys is **placement**: forward chaining
  ;; already matches antecedents across contexts, so firing on the copy does not find
  ;; anything new — it places the conclusion in UniverseContext rather than only in the
  ;; context the fact came from.  A consequence of a fact true everywhere is true
  ;; everywhere too.
  (tu/with-terms [edgeTo reachesFrom A B AlphaContext SiblingContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext SiblingContext 'UniverseContext) 'UniverseContext)
    (v/assert-rule kb [(list edgeTo '?x '?y)] (list reachesFrom '?y '?x) 'UniverseContext)
    (v/assert kb (list 'decontextualizedPredicate edgeTo) 'UniverseContext)
    (v/assert kb (list edgeTo A B) AlphaContext)
    (testing "the conclusion is placed both where the fact was stated and in the universe"
      (is (= #{AlphaContext 'UniverseContext}
             (set (map :context (v/sentexes-matching kb (list reachesFrom B A) '?ctx))))))
    (testing "so a sibling context sees it, which it would not without the lift"
      (is (v/ask? kb (list reachesFrom B A) SiblingContext)))))

(tu/deftest-kb a-negative-fact-is-not-lifted
  ;; `(not (P a))` has functor `not`, so a declaration about `P` does not reach it: the
  ;; positive extent becomes universal and the negative one stays in its context.
  ;; Deliberate, and pinned here so changing it has to be a decision.
  (tu/with-terms [flies Tweety Opus AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'decontextualizedPredicate flies) 'UniverseContext)
    (v/assert kb (list flies Tweety) AlphaContext)
    (v/assert kb (list 'not (list flies Opus)) AlphaContext)
    (is (seq (v/sentexes-matching kb (list flies Tweety) 'UniverseContext)) "the positive literal lifts")
    (is (empty? (v/sentexes-matching kb (list 'not (list flies Opus)) 'UniverseContext))
        "the negative literal does not")))

(tu/deftest-kb a-lift-out-of-sight-of-the-universe-is-checked-on-the-copy
  ;; The definitional checks run where a fact is stated, against what is visible from
  ;; there — so they cover the UniverseContext copy for free whenever the stating
  ;; context sees UniverseContext, which in a spindle-shaped KB is every context.  Two
  ;; contexts wired outside the spindle do not: neither sees the other's fact, nor the
  ;; copy, so each assert passes and the copies meet in UniverseContext as a violation
  ;; nobody looked for.  That case, and only that case, re-runs the check on the copy.
  (tu/with-terms [dog cat Rex OffAContext OffBContext]
    (v/assert kb (list 'genlContext OffAContext 'CoreContext) 'UniverseContext)
    (v/assert kb (list 'genlContext OffBContext 'CoreContext) 'UniverseContext)
    (is (not (v/sees? kb OffAContext 'UniverseContext)) "wired outside the spindle")
    (v/assert kb (list 'genl dog 'thing) 'CoreContext)
    (v/assert kb (list 'genl cat 'thing) 'CoreContext)
    (v/assert kb (list 'disjoint dog cat) 'CoreContext)
    (v/assert kb (list 'decontextualizedPredicate dog) 'UniverseContext)
    (v/assert kb (list 'decontextualizedPredicate cat) 'UniverseContext)
    (v/clear-violations! kb)

    (v/assert kb (list dog Rex) OffAContext)
    (testing "each fact is admissible where it is stated — neither context sees the other"
      (is (v/assert kb (list cat Rex) OffBContext)))
    (testing "but the second copy is refused rather than silently making Rex both"
      (is (not (and (seq (v/sentexes-matching kb (list dog Rex) 'UniverseContext))
                    (seq (v/sentexes-matching kb (list cat Rex) 'UniverseContext))))))
    (testing "and the refusal is reported, naming the context it was lifted from"
      (let [v (first (filter #(= :disjoint (:violation %)) (v/violations kb)))]
        (is (some? v))
        (is (= 'UniverseContext (:context v)))
        (is (= OffBContext (get-in v [:detail :lifted-from])))))))

(tu/deftest-kb the-declaration-marks-a-predicate-and-takes-one-argument
  ;; It routes through `prop-problems` like the other unary metadata marks: a second
  ;; argument is not a target to lift into, it is a mistake.
  (tu/with-terms [rulesOver Somewhere]
    (testing "an individual is not a predicate"
      (is (= :not-well-formed
             (:type (try (v/assert kb (list 'decontextualizedPredicate Somewhere) 'UniverseContext)
                         (catch clojure.lang.ExceptionInfo e (ex-data e)))))))
    (testing "and it takes exactly one argument"
      (is (= :not-well-formed
             (:type (try (v/assert kb (list 'decontextualizedPredicate rulesOver 'UniverseContext)
                                   'UniverseContext)
                         (catch clojure.lang.ExceptionInfo e (ex-data e)))))))))
