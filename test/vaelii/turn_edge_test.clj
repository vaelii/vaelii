;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.turn-edge-test
  "Edge cases for the features that landed this turn: the `evaluate` prover
  (extra operators, nesting, and use inside a rule antecedent), dot syntax
  driving a real forward rule, `genlCx` as a forced universal predicate
  (placement, closure, retraction, recovery), and the predicate-type provers
  (reflexive enumeration and a dual-property predicate).

  These cover scenarios not already exercised by dot_test / meta_test /
  common_sense_test / predicate_meta_test / recovery_test.  Each deftest builds
  its own KB on the scratch dbs and is net-neutral: `tu/with-neutral-kb` retracts
  what the test added; the persistence tests (a second KB over the same durable
  store) use `tu/with-cleared-kb`, whose honest teardown is a clear.  Invented
  domain terms are gensym'd; the real spindle contexts and starter/story terms a
  test verifies stay literal."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.starter :as starter]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(defn- core-context-kb [] (doto (tu/fresh) (core-context/load-into)))
(defn- starter-world-kb [] (doto (tu/fresh) (starter/load-into) (world/load-into)))

(defn- one [bindings k] (get (first bindings) k))

;; ---- evaluate: operators, nesting, ground checks ------------------------

(deftest evaluate-covers-more-operators-and-nesting
  ;; common_sense_test already covers (+), (*), a ground check, and an unbound
  ;; var; here: abs/min/max/mod/quot/rem/inc/dec, ratios, expt, and a mixed nest.
  (tu/with-neutral-kb [kb tu/fresh]                       ; the prover needs no ontology
    (testing "one-and-two-arg numeric ops"
      (is (= 5   (one (v/ask kb '(evaluate ?r (abs -5))   '?ctx) '?r)))
      (is (= 2   (one (v/ask kb '(evaluate ?r (min 3 7 2)) '?ctx) '?r)))
      (is (= 7   (one (v/ask kb '(evaluate ?r (max 3 7 2)) '?ctx) '?r)))
      (is (= 2   (one (v/ask kb '(evaluate ?r (mod 17 5)) '?ctx) '?r)))
      (is (= 3   (one (v/ask kb '(evaluate ?r (quot 17 5)) '?ctx) '?r)))
      (is (= 2   (one (v/ask kb '(evaluate ?r (rem 17 5)) '?ctx) '?r)))
      (is (= 6   (one (v/ask kb '(evaluate ?r (inc 5))    '?ctx) '?r)))
      (is (= 4   (one (v/ask kb '(evaluate ?r (dec 5))    '?ctx) '?r))))
    (testing "ratios stay exact; integer expt is integer-exact"
      (is (= 1/3 (one (v/ask kb '(evaluate ?r (/ 1 3))    '?ctx) '?r)))
      (is (= 8   (one (v/ask kb '(evaluate ?r (expt 2 3)) '?ctx) '?r))))
    (testing "a deeply mixed expression evaluates inside-out"
      (is (= 18  (one (v/ask kb '(evaluate ?r (- (* 4 5) (mod 17 5))) '?ctx) '?r)))
      (is (= 25  (one (v/ask kb '(evaluate ?r (max (abs -25) (+ 1 (* 2 3)))) '?ctx) '?r))))
    (testing "a ground result is checked, and an unevaluable subterm yields nothing"
      (is (v/ask? kb '(evaluate 5 (abs -5))))
      (is (not (v/ask? kb '(evaluate 6 (abs -5)))))
      (is (empty? (v/ask kb '(evaluate ?r (+ 1 (bogus 2))) '?ctx)))   ; unknown nested op
      (is (empty? (v/ask kb '(evaluate ?r (+ ?u 1))        '?ctx))))))  ; unbound var

;; ---- evaluate as a rule antecedent --------------------------------------

(deftest evaluate-drives-a-backward-rule-antecedent
  ;; A backward rule whose second antecedent is an (evaluate ...) goal: the node engine
  ;; substitutes the bindings from the first antecedent and dispatches the evaluate goal
  ;; to its leaf, where the EvaluateProver threads the computed value back.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [foo (tu/tmp-pred) bar (tu/tmp-pred)]
      (v/assert kb (list foo 3 4) 'CxUniverse)
      (v/assert-rule kb [(list foo '?x '?y) (list 'evaluate '?z (list '+ '?x '?y))]
                     (list bar '?x '?y '?z) 'CxUniverse {:direction :backward})
      (testing "the rule computes the third argument from the first two"
        (is (= '{?a 3 ?b 4 ?c 7}
               (first (v/query kb (list bar '?a '?b '?c) 'CxUniverse
                               {:max-depth 2})))))
      (testing "a ground query is checked against the computed value"
        (is (v/query? kb (list bar 3 4 7) 'CxUniverse {:max-depth 2}))
        (is (not (v/query? kb (list bar 3 4 8) 'CxUniverse {:max-depth 2})))))))

;; ---- dot syntax driving a concrete forward rule -------------------------

(deftest dot-syntax-drives-a-concrete-forward-rule
  ;; The dotted rest-pattern is not just documentation: a real forward rule with
  ;; a concrete head predicate copies parentOf pairs to kin pairs, and the ist
  ;; consequent directs the derived fact into CxUniverse.
  (tu/with-neutral-kb [kb core-context-kb]
    (let [parentOf (tu/tmp-pred) kin (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)]
      (v/assert kb (list 'implies (list parentOf '. '?args)
                         (list 'ist 'CxUniverse (list kin '. '?args))) 'CxUniverse)
      (v/assert kb (list parentOf tom bob) 'CxUniverse)   ; triggers the rule
      (testing "the spliced consequent lands as a believed fact in the named context"
        (is (= [(list kin tom bob)]
               (mapv :sentence (v/sentexes-matching kb (list kin tom bob) 'CxUniverse))))
        (is (v/ask? kb (list kin tom bob) 'CxUniverse)))
      (testing "an unrelated pair is not derived"
        (is (empty? (v/sentexes-matching kb (list kin bob tom) 'CxUniverse)))))))

(deftest dotted-rest-enumerates-and-joins-in-either-arrival-order
  ;; A dotted antecedent is sometimes the arriving trigger and sometimes a stored fact
  ;; the other antecedent has to retrieve.  Both paths must bind the same tail; otherwise
  ;; this rule's result depends on which premise happened to arrive last.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [agent_type agentCapable typeCapable
                    AgentA AgentB CapA CapB ToolA ToolB]
      (v/assert kb
                (list 'set/forwardRule
                      (list 'implies
                            (list 'and
                                  (list agent_type '?instance)
                                  (list agentCapable '?instance '. '?args))
                            (list typeCapable agent_type '. '?args)))
                'UniverseContext)

      ;; Dotted premise is the trigger.
      (v/assert kb (list agent_type AgentA) 'UniverseContext)
      (v/assert kb (list agentCapable AgentA CapA ToolA) 'UniverseContext)

      ;; Dotted premise must be found by the join after the type premise triggers.
      (v/assert kb (list agentCapable AgentB CapB ToolB) 'UniverseContext)
      (v/assert kb (list agent_type AgentB) 'UniverseContext)

      (testing "both premise arrival orders derive the same variadic bridge"
        (is (v/ask? kb (list typeCapable agent_type CapA ToolA) 'UniverseContext))
        (is (v/ask? kb (list typeCapable agent_type CapB ToolB) 'UniverseContext)))
      (testing "a dotted pattern directly enumerates and binds a stored tail"
        (is (= [(list agentCapable AgentB CapB ToolB)]
               (mapv :sentence
                     (v/sentexes-matching kb
                                          (list agentCapable AgentB '. '?args)
                                          'UniverseContext))))
        (is (= #{{'?args (list CapB ToolB)}}
               (set (v/ask kb (list agentCapable AgentB '. '?args)
                           'UniverseContext))))))))

;; ---- forced decontextualized predicate (genlCx) -------------------------

(deftest a-forced-genlcx-from-a-plain-context-lands-in-the-universe
  ;; genlCx is a forcedDecontextualizedPredicate: asserting one in an ordinary
  ;; context forces its storage to CxUniverse, yet the cached closure still
  ;; sees the edge (and its transitive consequences); retraction removes it.
  (tu/with-neutral-kb [kb core-context-kb]
    (let [alpha (tu/tmp-ctx) beta (tu/tmp-ctx) gamma (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx alpha beta)  'CxSocialWorld)  ; asserted in a plain context
      (v/assert kb (list 'genlCx beta  gamma) 'CxSocialWorld)
      (testing "the fact's extent is forced into CxUniverse, not the asserting context"
        (is (seq    (v/sentexes-matching kb (list 'genlCx alpha beta) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list 'genlCx alpha beta) 'CxSocialWorld))))
      (testing "the genlCx closure is intact — direct and transitive edges answer"
        (is (v/ask? kb (list 'genlCx alpha beta)))
        (is (v/ask? kb (list 'genlCx alpha gamma)))            ; alpha -> beta -> gamma
        (is (not (v/ask? kb (list 'genlCx gamma alpha)))))
      (testing "retracting a forced genlCx removes the sentex and the closure edge"
        (let [h (:id (first (v/sentexes-matching kb (list 'genlCx alpha beta) 'CxUniverse)))]
          (v/retract! kb h)
          (is (empty? (v/sentexes-matching kb (list 'genlCx alpha beta) 'CxUniverse)))
          (is (not (v/ask? kb (list 'genlCx alpha beta))))
          (is (not (v/ask? kb (list 'genlCx alpha gamma))))    ; chain broken
          (is (v/ask? kb (list 'genlCx beta gamma))))))))      ; the other edge survives

(deftest a-decontextualized-predicate-survives-recover
  ;; The lighter half of the same story: recover must re-mark `:decontextualized` from
  ;; the durable declaration, so the lift still applies to a fact asserted only after
  ;; recovery — and the copies made before it are already in the store, so they come
  ;; back with their justifications rather than being remade.
  (tu/with-cleared-kb [kb1 core-context-kb]
    (let [alpha (tu/tmp-ctx) pred (tu/tmp-pred) ann (tu/tmp-ind) bob (tu/tmp-ind)]
      (v/assert kb1 (list 'genlCx alpha 'CxUniverse) 'CxUniverse)
      (v/assert kb1 (list 'decontextualizedPredicate pred) 'CxUniverse)
      (v/assert kb1 (list pred ann) alpha)
      (is (seq (v/sentexes-matching kb1 (list pred ann) 'CxUniverse)) "lifted before the restart")

      (let [kb2 (tu/test-kb)]                        ; same stores, empty in-memory state
        (v/recover kb2)
        (testing "the declaration is believed again and the mark is back"
          (is (v/ask? kb2 (list 'decontextualizedPredicate pred)))
          (is (v/has-prop? kb2 :decontextualized pred)))
        (testing "the copy made before the restart is still there, still justified"
          (let [u (:id (first (v/sentexes-matching kb2 (list pred ann) 'CxUniverse)))]
            (is (some? u))
            (is (= 'decontextualizedPredicate
                   (:informant (first (v/supporting-justifications kb2 u)))))))
        (testing "and a fact asserted after recovery is lifted like any other"
          (v/assert kb2 (list pred bob) alpha)
          (is (seq (v/sentexes-matching kb2 (list pred bob) 'CxUniverse))))))))

(deftest forcing-a-decontextualized-predicate-survives-recover
  ;; recover must re-mark the :forced-decontextualized taxonomy property from the durable
  ;; (forcedDecontextualizedPredicate genlCx) sentex, so forcing still applies to a genlCx
  ;; asserted only after recovery.
  (tu/with-cleared-kb [_kb1 core-context-kb]                    ; kb1 writes the durable stores
    (let [kb2   (tu/test-kb)                         ; same dbs, empty in-memory state
          alpha (tu/tmp-ctx) beta (tu/tmp-ctx)]
      (v/recover kb2)
      (testing "the forcing declaration itself is believed again"
        (is (v/ask? kb2 '(forcedDecontextualizedPredicate genlCx))))
      (testing "a genlCx asserted post-recovery is still forced into CxUniverse"
        (v/assert kb2 (list 'genlCx alpha beta) 'CxSocialWorld)
        (is (seq    (v/sentexes-matching kb2 (list 'genlCx alpha beta) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb2 (list 'genlCx alpha beta) 'CxSocialWorld)))
        (is (v/ask? kb2 (list 'genlCx alpha beta)))))))

;; ---- predicate-type provers ---------------------------------------------

(deftest predicate-type-provers-reflexive-and-dual-property
  ;; meta_test covers symmetric/transitive/functional membership + enumeration;
  ;; here: reflexivePredicate (empty then populated), functionalPredicate
  ;; enumeration, and a single predicate carrying two algebraic properties.
  (tu/with-neutral-kb [kb core-context-kb]
    (let [sameSpotAs (tu/tmp-pred) heightOf (tu/tmp-pred) adjacentTo (tu/tmp-pred)]
      (testing "with no reflexive metadata the enumeration is empty"
        (is (empty? (v/ask kb '(reflexivePredicate ?p) '?ctx))))
      (v/assert kb (list 'reflexive sameSpotAs) 'CxUniverse)
      (v/assert kb (list 'functional heightOf)  'CxUniverse)
      (v/assert kb (list 'symmetric  adjacentTo) 'CxUniverse)
      (v/assert kb (list 'transitive adjacentTo) 'CxUniverse)     ; the same predicate, two properties
      (testing "reflexive/functional memberships answer and enumerate from metadata"
        (is (v/ask? kb (list 'reflexivePredicate sameSpotAs)))
        (is (= #{sameSpotAs}
               (set (map #(get % '?p) (v/ask kb '(reflexivePredicate ?p) '?ctx)))))
        ;; containment, not equality: CxCore declares (functional arity) itself,
        ;; so the shipped vocabulary is a member of this enumeration too
        (is (contains? (set (map #(get % '?p) (v/ask kb '(functionalPredicate ?p) '?ctx)))
                       heightOf)))
      (testing "a predicate declared both symmetric and transitive is classified as both"
        (is (v/ask? kb (list 'symmetricPredicate adjacentTo)))
        (is (v/ask? kb (list 'transitivePredicate adjacentTo)))
        (is (contains? (set (map #(get % '?p) (v/ask kb '(symmetricPredicate ?p) '?ctx)))
                       adjacentTo))
        (is (contains? (set (map #(get % '?p) (v/ask kb '(transitivePredicate ?p) '?ctx)))
                       adjacentTo)))
      (testing "a predicate without the property is not a member"
        (is (not (v/ask? kb (list 'reflexivePredicate adjacentTo))))
        (is (not (v/ask? kb (list 'functionalPredicate adjacentTo))))))))

;; ---- regressions for defects the review found (now fixed) ----------------

(deftest inert-dotted-rule-does-not-fire-on-a-global-chain
  ;; The (set/inertRule (implies (?pred . ?args) (ist CxUniverse (?pred . ?args))))
  ;; documentation rule must NOT copy facts into CxUniverse — forward chaining now
  ;; respects rule direction (a backward/inert rule never forward-fires).
  (tu/with-neutral-kb [kb core-context-kb]
    (let [dog (tu/tmp-type) muffet (tu/tmp-ind)]
      (v/assert kb (list dog muffet) 'CxCore)
      (v/forward-chain kb)
      (is (empty? (v/sentexes-matching kb (list dog muffet) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb '(forcedDecontextualizedPredicate genlCx) 'CxUniverse))))))

(deftest evaluate-is-error-safe
  (tu/with-neutral-kb [kb tu/fresh]
    (testing "a domain error (division / mod / quot by zero) yields no solution, not a throw"
      (is (empty? (v/ask kb '(evaluate ?r (/ 1 0))    '?ctx)))
      (is (empty? (v/ask kb '(evaluate ?r (mod 5 0))  '?ctx)))
      (is (empty? (v/ask kb '(evaluate ?r (quot 5 0)) '?ctx))))
    (testing "integer expt is integer-exact (not a double)"
      (is (= 8 (one (v/ask kb '(evaluate ?r (expt 2 3)) '?ctx) '?r)))
      (is (v/ask? kb '(evaluate 8 (expt 2 3)))))))

(deftest a-predicate-both-symmetric-and-transitive-answers-both-ways
  ;; TransitivePredicateProver does not run alone (completeness < 100), so a
  ;; symmetric+transitive predicate keeps its symmetric conclusions.
  (tu/with-neutral-kb [kb core-context-kb]
    (let [connectedTo (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind)]
      (v/assert kb (list 'symmetric connectedTo)  'CxUniverse)
      (v/assert kb (list 'transitive connectedTo) 'CxUniverse)
      (v/assert kb (list connectedTo a b) 'CxUniverse)
      (v/assert kb (list connectedTo b c) 'CxUniverse)
      (is (v/ask? kb (list connectedTo a c)))                     ; transitive
      (is (v/ask? kb (list connectedTo b a))))))                  ; symmetric

(deftest a-directly-asserted-predicate-type-fact-is-visible-to-ask
  ;; PredicateTypeProver (completeness 50) unions with FactProver, so a directly
  ;; asserted membership is not shadowed by the metadata-only answer.
  (tu/with-neutral-kb [kb core-context-kb]
    (let [fooRel (tu/tmp-pred)]
      (v/assert kb (list 'symmetricPredicate fooRel) 'CxCore)
      (is (v/ask? kb (list 'symmetricPredicate fooRel))))))

(deftest a-bare-dot-argument-is-rejected
  (tu/with-neutral-kb [kb core-context-kb]
    (let [dog (tu/tmp-type)]
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list dog '.) 'CxCore))))))

;; ---- the context spindle (CxCore <| upper <| CxUniverse <| middle <| CxWell) ----

(deftest a-core-context-kb-is-just-the-vocabulary-head
  ;; The spindle's bands (the upper definitional contexts, the middle theories) are
  ;; the starter's, not the vocabulary head's.  A CxCore-only KB has CxCore and its
  ;; vocabulary — including the forcedDecontextualizedPredicate declaration — but no
  ;; genlCx topology at all.
  (tu/with-neutral-kb [kb core-context-kb]
    (testing "CxCore vocabulary is present, including the forcing declaration"
      (is (seq (v/sentexes-matching kb '(binaryPredicate genl) 'CxCore)))
      (is (seq (v/sentexes-matching kb '(forcedDecontextualizedPredicate genlCx) 'CxCore))))
    (testing "but no spindle bands — those come with the starter"
      (is (empty? (v/sentexes-matching kb '(genlCx CxOrganism CxCore) '?ctx)))
      (is (not (tax/sees? (:taxonomy kb) 'CxWell 'CxCore))))))

(deftest a-user-defined-sibling-upper-context-supplies-universal-vocabulary
  ;; The spindle design lets a user add a sibling upper context — one that sees
  ;; CxCore and is seen by CxUniverse — to hold their own *universal* domain
  ;; terms.  Vocabulary put there (a type, an argIsa, an individual) is visible from
  ;; every data context below Well, and its argIsa constraints are enforced there.
  (tu/with-neutral-kb [kb starter-world-kb]
    (let [widgets (tu/tmp-ctx) widget (tu/tmp-type) priceOf (tu/tmp-pred)
          gadget (tu/tmp-ind) bad (tu/tmp-ind)]
      ;; a sibling upper context: sees CxCore, seen by CxUniverse (so every
      ;; descendant of CxUniverse — the middle theories, and CxNaturalWorld
      ;; below Well — sees it)
      (v/assert kb (list 'genlCx widgets 'CxCore)     'CxUniverse)
      (v/assert kb (list 'genlCx 'CxUniverse widgets) 'CxUniverse)
      ;; universal domain vocabulary defined once, in the sibling context
      (v/assert kb (list 'genl widget 'artifact)  widgets)
      (v/assert kb (list 'argIsa priceOf 1 widget) widgets)
      (v/assert kb (list widget gadget)            widgets)
      (testing "the sibling sits in the spindle's upper band"
        (is (tax/sees? (:taxonomy kb) widgets 'CxCore))
        (is (tax/sees? (:taxonomy kb) 'CxUniverse widgets))
        (is (tax/sees? (:taxonomy kb) 'CxNaturalWorld widgets)))   ; via Universe, through Well
      (testing "the sibling's vocabulary is visible from a data context"
        (is (v/isa? kb gadget widget     'CxNaturalWorld))
        (is (v/isa? kb gadget 'artifact  'CxNaturalWorld)))          ; genl widget artifact
      (testing "a fact using the sibling's term is allowed from the data context"
        (v/assert kb (list priceOf gadget 10) 'CxNaturalWorld)      ; gadget is a widget: OK
        (is (seq (v/sentexes-matching kb (list priceOf gadget 10) 'CxNaturalWorld))))
      (testing "and the sibling's argIsa constraint is enforced from the data context"
        (v/assert kb (list 'dog bad) 'CxNaturalWorld)               ; bad is-a (real) dog ⇒ is-a thing, but not a widget
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list priceOf bad 5) 'CxNaturalWorld)))))))

;; ---- recovery rebuilds the spindle and the derived stories ---------------

(deftest recover-rebuilds-the-spindle-and-the-stories
  ;; A restart (fresh in-memory taxonomy + JTMS over the same durable dbs) must
  ;; recover the spindle topology and the stories: their character types and their
  ;; derived morals come back IN with support.  This verifies the real starter +
  ;; test-world recover, so its terms stay literal.
  (tu/with-cleared-kb [kb1 starter-world-kb]
    (let [moral (:id (first (v/sentexes-matching kb1 '(repaidKindness MouseA LionA) 'CxLionMouse)))]
      (is (some? moral) "the moral was derived before the restart")
      (let [kb2 (tu/test-kb)]                     ; same dbs, empty memory
        (testing "before recover, the in-memory graph is empty"
          (is (not (tax/sees? (:taxonomy kb2) 'CxWell 'CxCore)))
          (is (not (v/in? kb2 moral))))
        (v/recover kb2)
        (testing "the spindle topology is rebuilt from the durable genlCx sentexes"
          (is (tax/sees? (:taxonomy kb2) 'CxUniverse 'CxOrganism))
          (is (tax/sees? (:taxonomy kb2) 'CxOrganism 'CxCore))
          (is (tax/sees? (:taxonomy kb2) 'CxWell     'CxCore))     ; transitive, whole spindle
          (is (tax/sees? (:taxonomy kb2) 'CxStories  'CxWell)))
        (testing "a story character keeps its ontology type after recovery"
          (is (v/isa? kb2 'LionA 'mammal))
          (is (v/isa? kb2 'MouseA 'animal)))
        (testing "the derived moral is believed again, with its support"
          (is (v/in? kb2 moral))
          (is (seq (v/supporting-justifications kb2 moral)))
          (is (seq (v/sentexes-matching kb2 '(repaidKindness MouseA LionA) 'CxLionMouse))))))))

;; ---- connected conjunctive antecedents, isolated from the stories --------

(deftest a-connected-conjunctive-rule-joins-on-a-shared-variable
  ;; The join feature the stories rely on, documented on a minimal world: a rule
  ;; (implies (and (p1 ?x A) (p2 ?y ?x)) (p3 ?y ?x)) with a CONSTANT (Anchor) in the
  ;; first antecedent and ?x the shared join variable.  Only the binding whose ?x is
  ;; anchored to the constant reaches the conclusion.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p1 (tu/tmp-pred) p2 (tu/tmp-pred) p3 (tu/tmp-pred)
          x1 (tu/tmp-ind) x2 (tu/tmp-ind) y1 (tu/tmp-ind) y2 (tu/tmp-ind)
          anchor (tu/tmp-ind) other (tu/tmp-ind)]
      ;; x1 is anchored to the constant and pairs with y1 -> should conclude (p3 y1 x1)
      (v/assert kb (list p1 x1 anchor) 'CxUniverse)
      (v/assert kb (list p2 y1 x1)     'CxUniverse)
      ;; x2 is anchored to a DIFFERENT constant, so (p1 ?x anchor) never binds ?x=x2
      (v/assert kb (list p1 x2 other)  'CxUniverse)
      (v/assert kb (list p2 y2 x2)     'CxUniverse)
      (v/assert-rule kb [(list p1 '?x anchor) (list p2 '?y '?x)] (list p3 '?y '?x) 'CxUniverse)
      (v/forward-chain kb)
      (testing "the anchored, joined binding is concluded"
        (is (seq (v/sentexes-matching kb (list p3 y1 x1) 'CxUniverse)))
        (is (v/ask? kb (list p3 y1 x1) 'CxUniverse)))
      (testing "a binding that fails the constant antecedent is not concluded"
        (is (empty? (v/sentexes-matching kb (list p3 y2 x2) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list p3 y1 x2) 'CxUniverse)))))))    ; nor any cross pairing
