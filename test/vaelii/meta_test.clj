;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.meta-test
  "The vocabulary context and meta-level features over the starter schema (with
  the test-world beneath it):

    * the context *spindle* — CxCore ⊏ upper ⊏ CxUniverse ⊏ middle ⊏ CxWell;
    * the predicate meta-ontology — predicates classified by arity and by the
      algebraic properties their metadata declares (each mark is itself a
      binary_predicate type, so the property is the classification);
    * decontextualized_predicate — a fact stated in one context deduced into
      CxUniverse and thereby visible everywhere."
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
    (is (seq (v/sentexes-matching kb '(genlCx CxOrganism CxCore) '?ctx)))
    (is (seq (v/sentexes-matching kb '(genlCx CxUniverse CxOrganism) '?ctx))))
  (testing "middle rides between Universe and Well"
    (is (seq (v/sentexes-matching kb '(genlCx CxBiology CxUniverse) '?ctx)))
    (is (seq (v/sentexes-matching kb '(genlCx CxWell CxBiology) '?ctx))))
  (testing "there is no direct Well→Core edge, but Core is transitively visible from Well"
    (is (empty? (v/sentexes-matching kb '(genlCx CxWell CxCore) '?ctx)))
    (is (tax/sees? (:taxonomy kb) 'CxWell 'CxCore)))
  (testing "CxCore vocabulary is visible from the collector and the data contexts"
    (is (v/ask? kb '(binary_predicate genl) 'CxUniverse))
    (is (v/ask? kb '(binary_predicate parentOf) 'CxNaturalWorld)))
  (testing "the upper ontology rides in the upper contexts, not the collector"
    (is (seq   (v/sentexes-matching kb '(genl dog mammal) 'CxOrganism)))
    (is (empty? (v/sentexes-matching kb '(genl dog mammal) 'CxUniverse)))
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

(tu/deftest-kb arity-and-relation-type-derive-each-other
  ;; (arity R N) and the N-ary relation-type membership conclude each other, each
  ;; landing where the declaration it was read off lives — the ordinary placement.
  (testing "arity is itself a binary predicate"
    (is (v/isa? kb 'arity 'binary_predicate)))
  (testing "an asserted predicate specialization concludes the arity, in its context"
    (is (seq (v/sentexes-matching kb '(arity dog 1) 'CxCore)))        ; a type is unary
    (is (seq (v/sentexes-matching kb '(arity awake 1) 'CxLife)))      ; a one-place property
    (is (seq (v/sentexes-matching kb '(arity parentOf 2) 'CxLife)))
    (is (seq (v/sentexes-matching kb '(arity siblingOf 2) 'CxLife)))  ; symmetric -> binary -> arity 2
    (is (seq (v/sentexes-matching kb '(arity arg 3) 'CxCore))))
  (testing "the derived arity is a claim of the context that declared the predicate,
            not of the vocabulary head — a private declaration stays private"
    (is (empty? (v/sentexes-matching kb '(arity parentOf 2) 'CxCore)))
    (is (empty? (v/sentexes-matching kb '(arity parentOf 2) 'CxNaturalWorld)))
    (is (v/isa? kb 'parentOf 'binary_predicate 'CxNaturalWorld)
        "but a data context below Well still sees it, since it sees CxLife"))
  (testing "an asserted arity concludes the relation-wide type and fixed policy"
    (tu/with-terms [fooRelation]
      (v/assert kb (list 'arity fooRelation 2) 'CxCore)
      (is (v/isa? kb fooRelation 'binary))
      (is (v/isa? kb fooRelation 'relation))
      (is (v/isa? kb fooRelation 'fixed_arity))
      (is (seq (v/sentexes-matching kb (list 'binary fooRelation) 'CxCore)))))
  (testing "the derived membership is justified by the arity fact and the rule"
    (tu/with-terms [barRelation]
      (v/assert kb (list 'arity barRelation 3) 'CxCore)
      (let [h (v/handle-of kb (list 'ternary barRelation) 'CxCore)
            d (first (v/supporting-justifications kb h))]
        (is (some #(= (list 'arity barRelation 3) (:sentence (v/sentex kb %)))
                  (:antecedents d)))))))

(tu/deftest-kb arity-cycle-is-self-preserving-only-with-an-asserted-member
  ;; the two directions form a positive cycle: (arity R N) <-> (N-ary relation R).
  ;; A member asserted as a premise grounds the whole cycle; the derived twin cannot
  ;; ground itself, so retracting the sole premise collapses both (well-founded).
  (testing "asserting the arity keeps both the arity and the type believed"
    (tu/with-terms [binaryRelation]
      (let [h (v/assert kb (list 'arity binaryRelation 2) 'CxCore)]
        (is (seq (v/sentexes-matching kb (list 'arity binaryRelation 2) 'CxCore)))
        (is (seq (v/sentexes-matching kb (list 'binary binaryRelation) 'CxCore)))
        (testing "retracting the sole premise collapses the whole cycle"
          (v/retract! kb h)
          (is (empty? (v/sentexes-matching kb (list 'binary binaryRelation) 'CxCore)))
          (is (empty? (v/sentexes-matching kb (list 'arity binaryRelation 2) 'CxCore)))))))
  (testing "a specialized predicate witness keeps its type, arity, and predicate policy"
    (tu/with-terms [qPred]
      (let [h (v/assert kb (list 'unary_predicate qPred) 'CxCore)]
        (is (v/isa? kb qPred 'unary))
        (is (v/isa? kb qPred 'fixed_arity_predicate))
        (is (seq (v/sentexes-matching kb (list 'arity qPred 1) 'CxCore)))
        (testing "and retracting it collapses the derived arity"
          (v/retract! kb h)
          (is (empty? (v/sentexes-matching kb (list 'arity qPred 1) 'CxCore))))))))

(tu/deftest-kb algebraic-predicate-types-classify-a-predicate
  ;; (symmetric siblingOf) etc. are the marks the provers read AND, since each mark is a
  ;; type — (genl symmetric binary_predicate) in CxCore — the classification itself: the
  ;; property IS the membership, with no derived (…Predicate) twin between them.
  (testing "the mark is a membership in the property type"
    (is (v/isa? kb 'siblingOf 'symmetric))
    (is (v/isa? kb 'marriedTo 'symmetric))
    (is (v/isa? kb 'ancestorOf 'transitive))
    (is (v/isa? kb 'partOf 'transitive))
    (is (v/isa? kb 'birthYearOf 'functional)))
  (testing "and inherit binary_predicate / predicate through genl"
    (is (v/isa? kb 'siblingOf 'binary_predicate))
    (is (v/isa? kb 'ancestorOf 'predicate)))
  (testing "the mark is decontextualized, so it is visible wherever CxUniverse is — every
            data context — while staying out of CxCore's own sight above the universe"
    (is (seq (v/sentexes-matching kb '(symmetric siblingOf) 'CxLife)))
    (is (v/ask? kb '(symmetric siblingOf) 'CxSocialWorld))
    (is (empty? (v/sentexes-matching kb '(symmetric siblingOf) 'CxCore)))))

(tu/deftest-kb algebraic-predicate-types-answer-and-enumerate
  (testing "membership is answered directly from the stored mark"
    (is (v/ask? kb '(symmetric siblingOf)))
    (is (v/ask? kb '(transitive ancestorOf)))
    (is (v/ask? kb '(functional birthYearOf)))
    (is (not (v/ask? kb '(symmetric parentOf)))))
  (testing "and enumerated"
    ;; the domain relations and siblingDisjointException are the symmetric marks,
    ;; decontextualized like the other algebraic marks, so they answer the enumeration
    ;; wherever CxUniverse is seen.  seeAlso is NOT among them — it is a directional
    ;; cross-reference, not symmetric.
    (is (= '#{siblingOf marriedTo friendOf siblingDisjointException}
           (set (map #(get % '?p) (v/ask kb '(symmetric ?p) '?ctx)))))
    ;; `genl` and `genlCx` are in the enumeration because CxCore asserts (transitive genl)
    ;; / (transitive genlCx) outright.  They *are* transitive; answering them from cached
    ;; closures instead of the generic prover is an implementation choice, not a difference
    ;; in what they mean — and saying so is what lets them be named as the relation an
    ;; argument position is preserved along (docs/inherit.md).  The declaration is held out
    ;; of the :transitive prop machinery (the closure-relations skip-set), so it stays a
    ;; queryable classification without routing them to the generic prover — which is why
    ;; they do not appear in `(props kb :transitive)`.
    ;; `heavierThan` / `tallerThan` / `olderThan` are the instance-level strict orders,
    ;; transitive beside `largerThan`'s type-level claim: two stated comparisons compose
    ;; into the third off the closure, which is the route a KB that weighed nothing has.
    ;; `greaterInMagnitudeThan` is the fourth, over quantities rather than objects.
    ;; `instantBefore` / `instantAfter` are the point algebra's strict orders, transitive
    ;; so a forward join reads a narrative's consecutive links as one ordering.
    (is (= '#{ancestorOf partOf locatedIn largerThan instantBefore instantAfter
              causes beforeEvent genl genlCx
              heavierThan tallerThan olderThan greaterInMagnitudeThan}
           (set (map #(get % '?p) (v/ask kb '(transitive ?p) '?ctx)))))
    (is (not (v/has-prop? kb :transitive 'genl)))))

(tu/deftest-kb genlcx-is-a-forced-decontextualized-predicate
  (testing "a genlCx edge is forced to live in CxUniverse, wherever asserted"
    (is (seq   (v/sentexes-matching kb '(genlCx CxUniverse CxOrganism) 'CxUniverse)))
    (is (empty? (v/sentexes-matching kb '(genlCx CxUniverse CxOrganism) 'CxCore))))    ; forced away from CxCore
  (testing "the closure is intact — CxCore vocabulary is still visible from CxUniverse"
    (is (v/ask? kb '(binary_predicate genl) 'CxUniverse))))

;; ---- decontextualized_predicate: a fact that belongs to the KB, not to one theory --
;;
;; `(decontextualized_predicate P)` deduces every `(P ...)` into CxUniverse, which
;; every context sees.  CxUniverse and not a named target: the definitional
;; checks are context-scoped and run where the fact is stated, so a target the stating
;; context cannot see is a place those checks never look — two facts, each admissible
;; where it was stated, could meet there as a disjointness violation nothing reports.

(tu/deftest-kb the-lift-is-documented-as-an-inert-dotted-rule
  (testing "the dotted rule the code implements is stored (as documentation)"
    (is (seq (v/sentexes-matching kb '(implies (?pred . ?args) (ist CxUniverse (?pred . ?args))) 'CxCore)))))

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
  (testing "the roster is the algebraic marks, the inverse declaration, and genlCx"
    (is (= '#{functional inverse reflexive symmetric asymmetric transitive
              irreflexive anti_symmetric anti_transitive equivalence_relation
              injection surjection bijection}
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
    (v/assert-rule kb [(list bornInFrance '?x)] (list speaksFrench '?x) CxAlpha)
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
                               :rule (v/assert-rule kb [(list bornInFrance '?x)] (list speaksFrench '?x) CxAlpha)
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
                   (list connects '?x '?z) CxAlpha)
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
                             (list 'implies (list 'and (list bird '?x)) (list flies '?x))))
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
    (v/assert-rule kb [(list edgeTo '?x '?y)] (list reachesFrom '?y '?x) 'CxUniverse)
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

(tu/deftest-kb a-lift-out-of-sight-of-the-universe-is-checked-on-the-copy
  ;; The definitional checks run where a fact is stated, against what is visible from
  ;; there — so they cover the CxUniverse copy for free whenever the stating
  ;; context sees CxUniverse, which in a spindle-shaped KB is every context.  Two
  ;; contexts wired outside the spindle do not: neither sees the other's fact, nor the
  ;; copy, so each assert passes and the copies meet in CxUniverse as a violation
  ;; nobody looked for.  That case, and only that case, re-runs the check on the copy.
  (tu/with-terms [dog cat Rex CxOffA CxOffB]
    (v/assert kb (list 'genlCx CxOffA 'CxCore) 'CxUniverse)
    (v/assert kb (list 'genlCx CxOffB 'CxCore) 'CxUniverse)
    (is (not (v/sees? kb CxOffA 'CxUniverse)) "wired outside the spindle")
    (v/assert kb (list 'genl dog 'thing) 'CxCore)
    (v/assert kb (list 'genl cat 'thing) 'CxCore)
    (v/assert kb (list 'disjoint dog cat) 'CxCore)
    (v/assert kb (list 'decontextualized_predicate dog) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate cat) 'CxUniverse)
    (v/clear-violations! kb)

    (v/assert kb (list dog Rex) CxOffA)
    (testing "each fact is admissible where it is stated — neither context sees the other"
      (is (v/assert kb (list cat Rex) CxOffB)))
    (testing "but the second copy is refused rather than silently making Rex both"
      (is (not (and (seq (v/sentexes-matching kb (list dog Rex) 'CxUniverse))
                    (seq (v/sentexes-matching kb (list cat Rex) 'CxUniverse))))))
    (testing "and the refusal is reported, naming the context it was lifted from"
      (let [v (first (filter #(= :disjoint (:violation %)) (v/violations kb)))]
        (is (some? v))
        (is (= 'CxUniverse (:context v)))
        (is (= CxOffB (get-in v [:detail :lifted-from])))))))

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
