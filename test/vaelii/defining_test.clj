;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.defining-test
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.defining :as defining]
            [vaelii.impl.except :as exc]
            [vaelii.impl.kb :as stored-kb]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/empty-kb) (tu/load-core!))))

(defn- contexts [kb homes]
  (doseq [home homes]
    (v/assert kb (list 'genlCx home 'CxUniverse) 'CxUniverse)))

(tu/deftest-kb a-bounded-defining-read-stops-before-realizing-the-term-posting
  (tu/with-terms [Subject tagged]
    (let [record (v/sentex kb (v/assert kb (list tagged Subject) 'CxUniverse))]
      (doseq [max-work [0 4]]
        (let [pulled (atom 0)]
          (with-redefs [stored-kb/find-sentexes
                        (fn [_ _]
                          (repeatedly 256 #(do (swap! pulled inc) record)))]
            (let [outcome (try
                            (budget/metered (budget/meter {:max-work max-work})
                                            #(v/defining-contexts kb Subject))
                            :unexpected-completion
                            (catch clojure.lang.ExceptionInfo e
                              (budget/exhausted e)))]
              (is (= :max-work outcome))
              (is (<= @pulled max-work)
                  "a small work bound cannot consume the whole lazy posting"))))))))

(tu/deftest-kb literal-quote-and-nested-sentences-do-not-define-their-contents
  (tu/with-terms [CxDefined CxMention Subject JimboMcFallible carriesSyntax]
    (contexts kb [CxDefined CxMention])
    (v/assert kb (list 'thing Subject) CxDefined)
    (let [quoted (list carriesSyntax (list 'Quote Subject))
          nested (list 'believes JimboMcFallible
                       (list 'comment Subject "every unit should have an swedish."))]
      (v/assert kb quoted CxMention)
      (is (seq (v/find-sentexes kb Subject)))
      (is (= #{CxDefined} (v/defining-contexts kb Subject)))
      (v/retract! kb (v/handle-of kb quoted CxMention))
      (v/assert kb nested CxMention)
      (is (= #{CxDefined} (v/defining-contexts kb Subject)))
      (let [h (v/assert kb (list 'comment Subject "The fictional subject has a direct comment.")
                        CxMention)]
        (is (= #{CxDefined CxMention} (v/defining-contexts kb Subject)))
        (v/retract! kb h)
        (is (= #{CxDefined} (v/defining-contexts kb Subject)))))))

(tu/deftest-kb ordinary-function-arguments-remain-defining-mentions
  (tu/with-terms [CxDefined Subject DisplayFn]
    (contexts kb [CxDefined])
    (let [sentence (list 'comment (list DisplayFn Subject) "A written function term.")
          h (v/assert kb sentence CxDefined)]
      (is (= sentence (:sentence (v/sentex kb h))))
      (is (= #{CxDefined} (v/defining-contexts kb Subject))))))

(tu/deftest-kb context-prefixed-function-arguments-remain-defining-mentions
  (tu/with-terms [CxDefined CxTemporalFn Subject Marker]
    (contexts kb [CxDefined])
    (v/assert kb (list 'binary_function CxTemporalFn) CxDefined)
    (let [term (list CxTemporalFn Subject Marker)
          sentence (list 'comment term "A written context constructor application.")
          h (v/assert kb sentence CxDefined)]
      (is (= sentence (:sentence (v/sentex kb h))))
      (is (v/ask? kb sentence CxDefined))
      (is (= #{CxDefined} (v/defining-contexts kb Subject))))))

(tu/deftest-kb an-asserted-negative-literal-defines-its-argument
  (tu/with-terms [CxDefined Subject tagged]
    (contexts kb [CxDefined])
    (let [sentence (list 'not (list tagged Subject))]
      (v/assert kb sentence CxDefined)
      (is (v/ask? kb sentence CxDefined))
      (is (= #{CxDefined} (v/defining-contexts kb Subject))))))

(tu/deftest-kb ordinary-home-filtering-precedes-context-maximization
  (tu/with-terms [CxParent CxChild CxSibling Subject describes]
    (contexts kb [CxParent CxSibling])
    (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse)
    (v/assert kb (list describes (list 'Quote Subject)) CxParent)
    (v/assert kb (list 'thing Subject) CxChild)
    (v/assert kb (list 'thing Subject) CxSibling)
    (is (= #{CxChild CxSibling} (v/defining-contexts kb Subject)))
    (let [h (v/assert kb (list 'thing Subject) CxParent)]
      (is (= #{CxParent CxSibling} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (is (= #{CxChild CxSibling} (v/defining-contexts kb Subject))))))

(tu/deftest-kb lifted-only-and-scaffolding-only-supports-do-not-create-a-global-home
  (tu/with-terms [CxHome Subject Marker liftedRel ordinaryRel conclusion]
    (contexts kb [CxHome])
    (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse)
    (v/assert kb (list liftedRel Subject Marker) CxHome)
    (is (= #{CxHome} (v/defining-contexts kb Subject)))
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list liftedRel '?x Marker) (list conclusion '?x)))
              'CxUniverse)
    (is (v/ask? kb (list conclusion Subject) 'CxUniverse))
    (is (= #{CxHome} (v/defining-contexts kb Subject)))
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list ordinaryRel '?x) (list conclusion '?x)))
              'CxUniverse)
    (let [h (v/assert kb (list ordinaryRel Subject) 'CxUniverse)]
      (is (= #{'CxUniverse} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (is (= #{CxHome} (v/defining-contexts kb Subject))))))

(tu/deftest-kb a-skeletal-content-antecedent-decides-before-the-other-support
  ;; The conclusion's only antecedent mentioning Subject is the lifted copy, skeletal, so
  ;; the ordinary prerequisite beside it does not make a global home.  The copy is
  ;; classified a round after the conclusion is first read, which must wait for it.
  (tu/with-terms [CxHome Subject Marker Other liftedRel prerequisite conclusion]
    (contexts kb [CxHome])
    (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse)
    (v/assert kb (list liftedRel Subject Marker) CxHome)
    (v/assert kb (list prerequisite Other) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list liftedRel '?x Marker) (list prerequisite Other))
                             (list conclusion '?x)))
              'CxUniverse)
    (is (v/ask? kb (list conclusion Subject) 'CxUniverse))
    (is (= #{CxHome} (v/defining-contexts kb Subject)))))

(tu/deftest-kb independent-premise-on-a-lifted-datum-remains-ordinary
  (tu/with-terms [CxHome Subject liftedType]
    (contexts kb [CxHome])
    (v/assert kb (list 'decontextualized_predicate liftedType) 'CxUniverse)
    (v/assert kb (list liftedType Subject) CxHome)
    (is (= #{CxHome} (v/defining-contexts kb Subject)))
    (let [h (v/assert kb (list liftedType Subject) 'CxUniverse)]
      (is (= #{'CxUniverse} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (is (= #{CxHome} (v/defining-contexts kb Subject))))))

(tu/deftest-kb an-arity-class-copy-does-not-create-a-global-defining-home
  (tu/with-terms [CxHome relation_kind nearbyRel]
    (contexts kb [CxHome])
    (v/assert kb (list 'genl relation_kind 'binary_predicate) CxHome {:strength :monotonic})
    (v/assert kb (list relation_kind nearbyRel) CxHome {:strength :monotonic})
    (is (v/ask? kb (list 'binary_predicate nearbyRel) 'CxUniverse))
    (is (= #{CxHome} (v/defining-contexts kb nearbyRel)))))

(tu/deftest-kb an-independent-premise-on-an-arity-class-copy-remains-ordinary
  (tu/with-terms [CxHome relation_kind nearbyRel]
    (contexts kb [CxHome])
    (v/assert kb (list 'genl relation_kind 'binary_predicate) CxHome {:strength :monotonic})
    (v/assert kb (list relation_kind nearbyRel) CxHome {:strength :monotonic})
    (v/assert kb (list 'binary_predicate nearbyRel) 'CxUniverse)
    (is (= #{'CxUniverse} (v/defining-contexts kb nearbyRel)))))

(tu/deftest-kb another-nats-bookkeeping-does-not-define-its-namespace-argument
  (tu/with-terms [CxHome Namespace namespace_kind LookupFn lookupOf access_kind usedBy Observer]
    (contexts kb [CxHome])
    (doseq [sentence [(list 'reifiable_function LookupFn)
                      (list 'result LookupFn access_kind)
                      (list 'functionCorrespondingPredicate LookupFn lookupOf 2)
                      (list 'arg lookupOf 1 namespace_kind)]]
      (v/assert kb sentence 'CxUniverse))
    (v/assert kb (list namespace_kind Namespace) CxHome)
    (v/assert kb (list usedBy (list LookupFn Namespace) Observer) CxHome)
    (is (v/ask? kb (list namespace_kind Namespace) 'CxUniverse))
    (is (= #{CxHome} (v/defining-contexts kb Namespace)))))

(tu/deftest-kb an-ordinary-derived-assertion-contributes-its-context
  (tu/with-terms [CxHome Subject sourceFact derivedFact]
    (contexts kb [CxHome])
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list sourceFact '?x) (list derivedFact '?x)))
              CxHome)
    (let [h (v/assert kb (list sourceFact Subject) CxHome)]
      (is (v/ask? kb (list derivedFact Subject) CxHome))
      (is (= #{CxHome} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (is (= #{} (v/defining-contexts kb Subject))))))

(tu/deftest-kb a-fact-an-equality-merge-respells-keeps-its-defining-context
  (tu/with-terms [CxHome Subject Kip Kipper ownerRel]
    (contexts kb [CxHome])
    (let [eq   (list 'equals Kip Kipper)
          rep  (do (v/assert kb eq CxHome {:strength :monotonic})
                   (v/representative kb Kip CxHome))
          fact (list ownerRel (if (= rep Kip) Kipper Kip) Subject)]
      ;; the merge first, then the fact, then the fact first, then the merge
      (v/assert kb fact CxHome {:strength :monotonic})
      (is (v/ask? kb (list ownerRel rep Subject) CxHome))
      (is (= #{CxHome} (v/defining-contexts kb Subject)))
      (v/retract! kb (v/handle-of kb eq CxHome))
      (v/assert kb eq CxHome {:strength :monotonic})
      (is (v/ask? kb (list ownerRel rep Subject) CxHome))
      (is (= #{CxHome} (v/defining-contexts kb Subject))))))

(tu/deftest-kb unsupported-cycles-and-inert-mentions-contribute-no-home
  (tu/with-terms [CxHome Subject pFact qFact]
    (contexts kb [CxHome])
    (v/assert kb (list 'set/forwardRule (list 'implies (list pFact '?x) (list qFact '?x))) CxHome)
    (v/assert kb (list 'set/forwardRule (list 'implies (list qFact '?x) (list pFact '?x))) CxHome)
    (let [h (v/assert kb (list pFact Subject) CxHome)]
      (is (= #{CxHome} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (v/assert-inert kb (list 'comment Subject "An inert comment.") CxHome)
      (is (not (v/ask? kb (list qFact Subject) CxHome)))
      (is (= #{} (v/defining-contexts kb Subject))))))

(tu/deftest-kb a-grounded-rule-that-names-a-constant-defines-it-in-the-rules-context
  ;; A rule naming Subject in its body is a mention of Subject, so its
  ;; context defines Subject whether or not the rule has fired.
  (tu/with-terms [CxHome Subject Marker trigger target]
    (contexts kb [CxHome])
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list trigger Marker) (list target Subject))) CxHome)
    (is (= #{CxHome} (v/defining-contexts kb Subject)))
    (let [h (v/assert kb (list trigger Marker) CxHome)]
      (is (v/ask? kb (list target Subject) CxHome))
      (is (= #{CxHome} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (is (= #{CxHome} (v/defining-contexts kb Subject))))))

(tu/deftest-kb a-rule-that-does-not-name-a-constant-leaves-it-to-the-leaf-that-does
  ;; The variant where the rule does not name Subject.  The derived
  ;; conclusion is stored in the rule's context, but its defining context comes from
  ;; the leaf that names Subject, and goes with that leaf.
  (tu/with-terms [CxHome CxTrig Subject trigger target]
    (contexts kb [CxTrig])
    (v/assert kb (list 'genlCx CxHome CxTrig) 'CxUniverse)
    (v/assert kb (tu/fwd [(list trigger '?x)] (list target '?x)) CxHome)
    (is (= #{} (v/defining-contexts kb Subject)) "before firing")
    (let [h (v/assert kb (list trigger Subject) CxTrig)
          derived (v/handle-of kb (list target Subject) CxHome)]
      (is (some? derived))
      (is (not (v/premise? kb derived)))
      (is (= #{CxTrig} (v/defining-contexts kb Subject)) "after firing")
      (v/retract! kb h)
      (is (not (v/ask? kb (list target Subject) CxHome)))
      (is (= #{} (v/defining-contexts kb Subject)) "after retracting the leaf"))))

(tu/deftest-kb a-skeletal-trigger-under-an-asserted-rule-creates-an-ordinary-global-home
  ;; The asserted rule is a leaf of the firing it informs, and it is ordinary.
  (tu/with-terms [CxOrigin Subject Marker liftedTrigger target subject_kind]
    (contexts kb [CxOrigin])
    (v/assert kb (list 'decontextualized_predicate liftedTrigger) 'CxUniverse)
    (v/assert kb (list 'arg target 1 subject_kind) 'CxUniverse)
    (v/assert kb (list liftedTrigger Marker) CxOrigin)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list liftedTrigger Marker) (list target Subject)))
              'CxUniverse)
    (is (v/ask? kb (list target Subject) 'CxUniverse))
    (is (v/ask? kb (list subject_kind Subject) 'CxUniverse))
    (is (= #{'CxUniverse} (v/defining-contexts kb Subject)))))

(tu/deftest-kb mixed-introduction-support-with-no-content-role-is-ordinary
  (tu/with-terms [CxOrigin Subject Marker Other liftedTrigger prerequisite target]
    (contexts kb [CxOrigin])
    (v/assert kb (list 'decontextualized_predicate liftedTrigger) 'CxUniverse)
    (v/assert kb (list liftedTrigger Marker) CxOrigin)
    (v/assert kb (list prerequisite Other) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list liftedTrigger Marker)
                                            (list prerequisite Other))
                             (list target Subject))) 'CxUniverse)
    (is (true? (v/ask? kb (list target Subject) 'CxUniverse)))
    (is (= #{'CxUniverse} (v/defining-contexts kb Subject)))))

;; ---- computed support: the engine's own knowledge, skeletal; its rule is a leaf ----

(tu/deftest-kb a-computed-only-firing-under-an-asserted-rule-is-ordinary
  (tu/with-terms [Subject target]
    (v/assert kb (tu/fwd [(list 'evaluate '?s (list '+ 1 2))] (list target Subject)) 'CxUniverse)
    (is (v/ask? kb (list target Subject) 'CxUniverse))
    (is (= {:contexts #{'CxUniverse} :skeletal-only? false}
           (defining/definition-evidence kb Subject)))))

(tu/deftest-kb an-unrepresented-term-is-defined-in-the-universe
  ;; `3` in `(theSum 3)` enters only through `evaluate`'s binding, and a number or string is
  ;; not posted in the term index.  An unrepresented term is defined in CxUniverse, as a
  ;; context is.
  (tu/with-terms [CxHome theSum]
    (contexts kb [CxHome])
    (v/assert kb (tu/fwd [(list 'evaluate '?s (list '+ 1 2))] (list theSum '?s)) CxHome)
    (is (v/ask? kb (list theSum 3) CxHome))
    (is (= [] (vec (v/find-sentexes kb 3))) "a number has no posting")
    (is (= {:contexts #{'CxUniverse} :skeletal-only? false} (defining/definition-evidence kb 3)))
    (is (= #{'CxUniverse} (v/defining-contexts kb "a string")))))

(tu/deftest-kb a-computed-literal-and-skeletal-trigger-under-an-asserted-rule-is-ordinary
  (tu/with-terms [CxOrigin Subject Marker liftedTrigger target]
    (contexts kb [CxOrigin])
    (v/assert kb (list 'decontextualized_predicate liftedTrigger) 'CxUniverse)
    (v/assert kb (list liftedTrigger Marker) CxOrigin)
    (v/assert kb (tu/fwd [(list liftedTrigger Marker) (list 'evaluate '?n (list '+ 1 2))]
                         (list target Subject)) 'CxUniverse)
    (is (v/ask? kb (list target Subject) 'CxUniverse))
    (is (= #{'CxUniverse} (v/defining-contexts kb Subject)))))

(tu/deftest-kb a-computed-literal-beside-an-ordinary-fact-is-ordinary
  (tu/with-terms [Subject Other prerequisite target]
    (v/assert kb (list prerequisite Other) 'CxUniverse)
    (v/assert kb (tu/fwd [(list prerequisite Other) (list 'evaluate '?n (list '+ 1 2))]
                         (list target Subject)) 'CxUniverse)
    (is (v/ask? kb (list target Subject) 'CxUniverse))
    (is (= #{'CxUniverse} (v/defining-contexts kb Subject)))))

;; ---- asserted leaves: the premises a datum's valid support bottoms out in -----------

(defn- leaves [kb h] (defining/asserted-leaves kb h))

(defn- held [kb sentence context] (v/handle-of kb sentence context))

(tu/deftest-kb a-premise-is-its-own-asserted-leaf
  (tu/with-terms [CxHome Subject tagged]
    (contexts kb [CxHome])
    (let [h (v/assert kb (list tagged Subject) CxHome)]
      (is (= {:leaves #{h} :computed? false} (leaves kb h))))))

(tu/deftest-kb a-chain-bottoms-out-in-its-premise-and-its-asserted-rules
  (tu/with-terms [CxHome Subject aFact bFact cFact]
    (contexts kb [CxHome])
    (let [r1 (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
          r2 (v/assert kb (tu/fwd [(list bFact '?x)] (list cFact '?x)) CxHome)
          a (v/assert kb (list aFact Subject) CxHome)
          c (held kb (list cFact Subject) CxHome)]
      (is (some? c))
      (is (= {:leaves #{a r1 r2} :computed? false} (leaves kb c))))))

(tu/deftest-kb a-diamond-reaches-its-shared-premise-once
  (tu/with-terms [CxHome Subject aFact bFact cFact dFact eFact]
    (contexts kb [CxHome])
    (let [rb (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
          rc (v/assert kb (tu/fwd [(list aFact '?x)] (list cFact '?x)) CxHome)
          rd (v/assert kb (tu/fwd [(list bFact '?x) (list cFact '?x) (list eFact '?x)]
                                  (list dFact '?x)) CxHome)
          a (v/assert kb (list aFact Subject) CxHome)
          e (v/assert kb (list eFact Subject) CxHome)
          d (held kb (list dFact Subject) CxHome)]
      (is (some? d))
      (is (= {:leaves #{a e rb rc rd} :computed? false} (leaves kb d))))))

(tu/deftest-kb a-support-cycle-bottoms-out-in-the-premise-that-grounds-it
  (tu/with-terms [CxHome Subject pFact qFact rFact]
    (contexts kb [CxHome])
    (let [rules (into #{} (map #(v/assert kb % CxHome))
                      [(tu/fwd [(list rFact '?x)] (list pFact '?x))
                       (tu/fwd [(list pFact '?x)] (list qFact '?x))
                       (tu/fwd [(list qFact '?x)] (list pFact '?x))])
          r (v/assert kb (list rFact Subject) CxHome)
          p (held kb (list pFact Subject) CxHome)
          q (held kb (list qFact Subject) CxHome)]
      (is (= 2 (count (v/supporting-justifications kb p))) "p rests on r and on q")
      (is (= {:leaves (conj rules r) :computed? false} (leaves kb p)))
      (is (= {:leaves (conj rules r) :computed? false} (leaves kb q))))))

(tu/deftest-kb a-guard-covered-alternative-contributes-no-leaf
  (tu/with-terms [bird penguin bat flies Opus CxFly]
    (contexts kb [CxFly])
    (let [rule #(list 'set/defaultRule (list 'set/forwardRule (list 'implies (list % '?x) (list flies '?x))))]
      (v/assert kb (rule bird) CxFly)
      (v/assert kb (list 'exceptWhen (list penguin '?x) (rule bird)) CxFly)
      (let [rt (v/assert kb (rule bat) CxFly)
            b (v/assert kb (list bird Opus) CxFly)
            t (v/assert kb (list bat Opus) CxFly)
            _ (v/assert kb (list penguin Opus) CxFly)
            h (held kb (list flies Opus) CxFly)]
        (is (= #{:guard :supports} (set (vals (v/justification-verdicts kb h CxFly)))))
        (is (= {:leaves #{t rt} :computed? false} (leaves kb h)))
        (is (not (contains? (:leaves (leaves kb h)) b)))))))

(tu/deftest-kb a-blocked-alternative-contributes-no-leaf
  (tu/with-terms [bird penguin bat flies Opus CxFly]
    (contexts kb [CxFly])
    (v/assert kb (list 'closed_extent_predicate penguin) CxFly)
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule
                             (list 'implies (list 'and (list bird '?x) (list 'not (list penguin '?x)))
                                   (list flies '?x)))) CxFly)
    (let [rt (v/assert kb (list 'set/defaultRule
                                (list 'set/forwardRule (list 'implies (list bat '?x) (list flies '?x))))
                       CxFly)
          b (v/assert kb (list bird Opus) CxFly)
          t (v/assert kb (list bat Opus) CxFly)
          _ (v/assert kb (list penguin Opus) CxFly)
          h (held kb (list flies Opus) CxFly)]
      (is (= #{:blocked :supports} (set (vals (v/justification-verdicts kb h CxFly)))))
      (is (= {:leaves #{t rt} :computed? false} (leaves kb h)))
      (is (not (contains? (:leaves (leaves kb h)) b))))))

(tu/deftest-kb an-all-computed-firing-leaves-only-its-rule-and-is-marked-computed
  (tu/with-terms [CxHome theSum]
    (contexts kb [CxHome])
    (let [rh (v/assert kb (tu/fwd [(list 'evaluate '?s (list '+ 1 2))] (list theSum '?s)) CxHome)
          h (held kb (list theSum 3) CxHome)]
      (is (= [[[] rh]] (mapv (juxt :antecedents :informant) (v/supporting-justifications kb h))))
      (is (= {:leaves #{rh} :computed? true} (leaves kb h))))))

(tu/deftest-kb a-computed-literal-beside-a-fact-leaves-only-the-fact
  (tu/with-terms [CxHome Ann Bob ageOf youngerThan]
    (contexts kb [CxHome])
    (let [a (v/assert kb (list ageOf Ann 10) CxHome)
          b (v/assert kb (list ageOf Bob 20) CxHome)
          rh (v/assert kb (tu/fwd [(list ageOf '?x '?a) (list ageOf '?y '?b) (list 'lessThan '?a '?b)]
                                  (list youngerThan '?x '?y)) CxHome)
          h (held kb (list youngerThan Ann Bob) CxHome)]
      (is (= {:leaves #{a b rh} :computed? false} (leaves kb h))))))

(tu/deftest-kb a-deduced-rule-is-walked-down-to-the-fact-it-rests-on
  ;; A defnNecessary fact mints its companion rule: the rule is derived, not asserted,
  ;; and it informs the firing, so the walk descends through it to the defn fact.
  (tu/with-terms [bachelor Tom unmarried]
    (let [dh (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
          bh (v/assert kb (list bachelor Tom) 'CxUniverse)
          rh (v/handle-of kb (list 'implies (list bachelor '?x) (list unmarried '?x)) 'CxUniverse)
          h (held kb (list unmarried Tom) 'CxUniverse)]
      (is (some? rh))
      (is (not (v/premise? kb rh)) "the companion rule is deduced")
      (is (= [rh] (map :informant (v/supporting-justifications kb h))) "and informs the firing")
      (is (= {:leaves #{bh dh} :computed? false} (leaves kb h))))))

(tu/deftest-kb the-leaf-that-names-the-subject-defines-it-not-the-rule-or-the-other-premise
  ;; A generic rule and a premise that doesn't name Subject help derive
  ;; (r Subject Object) but don't define Subject; the premise that names it does.
  (tu/with-terms [CxRule CxP CxQ CxJoin Subject Intermediate Object p q r]
    (contexts kb [CxRule CxP CxQ])
    (let [links (into #{} (map #(v/assert kb (list 'genlCx CxJoin %) 'CxUniverse))
                      [CxRule CxP CxQ])
          rh (v/assert kb (list 'set/forwardRule
                                (list 'implies (list 'and (list p '?x '?y) (list q '?y '?z))
                                      (list r '?x '?z)))
                       CxRule)
          ph (v/assert kb (list p Subject Intermediate) CxP)
          qh (v/assert kb (list q Intermediate Object) CxQ)
          h (held kb (list r Subject Object) CxJoin)]
      (is (true? (v/ask? kb (list r Subject Object) CxJoin)))
      (testing "the conclusion is a stored deduction resting on the rule and both premises"
        ;; the firing also rests on the genlCx links that let the join context see them
        (is (some? h))
        (is (not (v/premise? kb h)))
        (is (= {:leaves (into #{rh ph qh} links) :computed? false} (leaves kb h))))
      (is (= #{CxP} (v/defining-contexts kb Subject))))))

(tu/deftest-kb a-rule-that-names-the-subject-defines-it-beside-the-premise-that-does
  ;; When the rule names Subject too, its context defines Subject
  ;; alongside the premise's, reduced to the maximal ones via genlCx.
  (tu/with-terms [CxRule2 CxP2 CxQ2 CxJoin2 Subject Intermediate Object p q r]
    (contexts kb [CxRule2 CxP2 CxQ2])
    (let [links (into #{} (map #(v/assert kb (list 'genlCx CxJoin2 %) 'CxUniverse))
                      [CxRule2 CxP2 CxQ2])
          rh (v/assert kb (list 'set/forwardRule
                                (list 'implies (list 'and (list p Subject '?y) (list q '?y '?z))
                                      (list r Subject '?z)))
                       CxRule2)
          ph (v/assert kb (list p Subject Intermediate) CxP2)
          qh (v/assert kb (list q Intermediate Object) CxQ2)
          h (held kb (list r Subject Object) CxJoin2)]
      (is (true? (v/ask? kb (list r Subject Object) CxJoin2)))
      (testing "the conclusion is a stored deduction resting on the rule and both premises"
        ;; the firing also rests on the genlCx links that let the join context see them
        (is (some? h))
        (is (not (v/premise? kb h)))
        (is (= {:leaves (into #{rh ph qh} links) :computed? false} (leaves kb h))))
      (is (= #{CxRule2 CxP2} (v/defining-contexts kb Subject)))
      (testing "a genlCx between the two leaves' contexts reduces to the more general one"
        (v/assert kb (list 'genlCx CxP2 CxRule2) 'CxUniverse)
        (is (= #{CxRule2} (v/defining-contexts kb Subject)))))))

;; ---- equality: a mention is syntactic --------------------------------------------

(defn- equal-names-define-apart
  "`first-term` and `second-term` are equal (`pred`, one of `sameAs`, `equals` and
  `rewriteOf`, asserted with `first-term` as the first argument when `first-arg-first?`),
  and each is named by a fact in a context of its own.  The equation is stated in `CxEq`,
  a context of its own below `CxUniverse` alone, so context maximization cannot fold it
  into either fact context.  An equation is a mention, not a use, so
  it defines neither name: each term's defining contexts are its own fact's context alone."
  [kb pred first-term second-term first-arg-first? [tagFirst tagSecond] CxFirst CxSecond CxEq]
  (contexts kb [CxFirst CxSecond CxEq])
  (v/assert kb (list tagFirst first-term) CxFirst)
  (v/assert kb (list tagSecond second-term) CxSecond)
  (let [equation (if first-arg-first?
                   (list pred first-term second-term)
                   (list pred second-term first-term))]
    (v/assert kb equation CxEq)
    (is (v/ask? kb equation CxEq) "the equation holds where it is stated"))
  (is (not (v/ask? kb (list tagSecond first-term) CxFirst)) "and the merge only there")
  (is (= #{CxFirst} (v/defining-contexts kb first-term)))
  (is (= #{CxSecond} (v/defining-contexts kb second-term))))

(tu/deftest-kb an-equal-name-mentioned-elsewhere-does-not-define-the-other
  ;; A fact about MorningStar and one about EveningStar in different
  ;; contexts are mentions of each name alone, equality notwithstanding.  Both pairs and
  ;; both argument orders, so no choice of representative (first argument, least name)
  ;; passes by luck: MorningStar sorts after EveningStar, Alpha before Zeta.  Each
  ;; equality predicate, since each is skeletal for defining.
  (doseq [pred '[sameAs equals rewriteOf]
          first-arg-first? [true false]]
    (testing (str pred ", MorningStar and EveningStar, first argument first: " first-arg-first?)
      (tu/with-terms [MorningStar EveningStar tagM tagE CxM CxE CxEq]
        (equal-names-define-apart kb pred MorningStar EveningStar first-arg-first?
                                  [tagM tagE] CxM CxE CxEq)))
    (testing (str pred ", Alpha and Zeta, first argument first: " first-arg-first?)
      (tu/with-terms [Alpha Zeta tagA tagZ CxA CxZ CxEq]
        (equal-names-define-apart kb pred Alpha Zeta first-arg-first? [tagA tagZ] CxA CxZ CxEq)))))

(tu/deftest-kb a-term-named-only-in-an-equation-is-skeletal-only
  ;; SameAs, equals and rewriteOf are mention rather than use, so an
  ;; equation is skeletal for defining.  A term named in nothing else has believed
  ;; mentions but no ordinary leaf: no defining context, and skeletal-only.
  (doseq [pred '[sameAs equals rewriteOf]]
    (testing (str pred)
      (tu/with-terms [CxEq Lonely Other]
        (contexts kb [CxEq])
        (v/assert kb (list pred Lonely Other) CxEq)
        (is (v/ask? kb (list pred Lonely Other) CxEq))
        (is (= {:contexts #{} :skeletal-only? true} (defining/definition-evidence kb Lonely)))
        (is (= {:contexts #{} :skeletal-only? true} (defining/definition-evidence kb Other)))))))

(tu/deftest-kb a-negated-equation-is-skeletal-like-the-equation
  ;; Skeletality respects the literal's predicate, not the atom's
  ;; polarity, so (not P) is treated identically to P.  A negated equation defines
  ;; neither name, and a term named only in one is skeletal-only.
  (doseq [pred '[sameAs equals rewriteOf]]
    (testing (str "(not (" pred " ...)) between two names with facts of their own")
      (tu/with-terms [CxFirst CxSecond CxEq First Second tagFirst tagSecond]
        (contexts kb [CxFirst CxSecond CxEq])
        (v/assert kb (list tagFirst First) CxFirst)
        (v/assert kb (list tagSecond Second) CxSecond)
        (let [negated (list 'not (list pred First Second))]
          (v/assert kb negated CxEq)
          (is (some? (v/handle-of kb negated CxEq)) "the negated equation is stored"))
        (is (= #{CxFirst} (v/defining-contexts kb First)))
        (is (= #{CxSecond} (v/defining-contexts kb Second)))))
    (testing (str "a term named only in (not (" pred " ...))")
      (tu/with-terms [CxEq Lonely Other]
        (contexts kb [CxEq])
        (let [negated (list 'not (list pred Lonely Other))]
          (v/assert kb negated CxEq)
          (is (some? (v/handle-of kb negated CxEq))))
        (is (= {:contexts #{} :skeletal-only? true} (defining/definition-evidence kb Lonely)))
        (is (= {:contexts #{} :skeletal-only? true} (defining/definition-evidence kb Other)))))))

;; ---- contexts: genlCx is decontextualized, so a context is defined in CxUniverse ----

(tu/deftest-kb a-contexts-defining-context-is-the-universe
  ;; The genlCx links mention the context they relate, and genlCx is
  ;; decontextualized (forced_decontextualized_predicate), so every context is defined
  ;; in CxUniverse wherever its link was asserted, and a mention in a context below it
  ;; maximizes into CxUniverse too.
  (tu/with-terms [CxOther CxParent CxKid CxGrand]
    (contexts kb [CxOther CxParent])
    (testing "a context whose only genlCx was asserted in another context"
      (v/assert kb (list 'genlCx CxKid CxParent) CxOther)
      (is (= #{'CxUniverse} (v/defining-contexts kb CxKid))))
    (testing "and which is also commented in a child context of its own"
      (v/assert kb (list 'genlCx CxGrand CxKid) 'CxUniverse)
      (v/assert kb (list 'comment CxKid "A context commented below itself.") CxGrand)
      (is (= #{'CxUniverse} (v/defining-contexts kb CxKid))))
    (testing "CxUniverse itself"
      (is (= #{'CxUniverse} (v/defining-contexts kb 'CxUniverse))))))

;; ---- asserted-leaves-such-that: one walk, a unary filter, many starts ----------------

(defn- such-that [kb keep? hs] (defining/asserted-leaves-such-that kb keep? hs))

(tu/deftest-kb a-rejected-node-halts-the-walk-there
  ;; The filter rejects the middle of a chain: the walk neither descends past it nor
  ;; keeps it as a leaf, so only the rule that rests on it remains.
  (tu/with-terms [CxHome Subject aFact bFact cFact]
    (contexts kb [CxHome])
    (let [_r1 (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
          r2 (v/assert kb (tu/fwd [(list bFact '?x)] (list cFact '?x)) CxHome)
          _a (v/assert kb (list aFact Subject) CxHome)
          b (held kb (list bFact Subject) CxHome)
          c (held kb (list cFact Subject) CxHome)]
      (is (= (leaves kb c) (such-that kb (constantly true) c)) "the default filter is asserted-leaves")
      (is (= {:leaves #{r2} :computed? false} (such-that kb #(not= b %) c))))))

(tu/deftest-kb many-starts-share-one-walk
  ;; Two conclusions over a shared premise: one walk from both reads each handle's
  ;; support once and unions their leaves.
  (tu/with-terms [CxHome Subject aFact bFact cFact]
    (contexts kb [CxHome])
    (let [rb (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
          rc (v/assert kb (tu/fwd [(list aFact '?x)] (list cFact '?x)) CxHome)
          a (v/assert kb (list aFact Subject) CxHome)
          b (held kb (list bFact Subject) CxHome)
          c (held kb (list cFact Subject) CxHome)
          reads (atom {})
          verdicts exc/justification-verdicts]
      (with-redefs [exc/justification-verdicts (fn [kb h ctx]
                                                 (swap! reads update h (fnil inc 0))
                                                 (verdicts kb h ctx))]
        (is (= {:leaves #{a rb rc} :computed? false} (such-that kb (constantly true) [b c b]))))
      (is (every? #{1} (vals @reads)) "each handle's support is read once")
      (is (= #{b c} (set (keys @reads))) "and premises are not read at all"))))

(tu/deftest-kb a-filtered-walk-through-a-cycle-terminates
  (tu/with-terms [CxHome Subject pFact qFact rFact]
    (contexts kb [CxHome])
    (let [rules (into #{} (map #(v/assert kb % CxHome))
                      [(tu/fwd [(list rFact '?x)] (list pFact '?x))
                       (tu/fwd [(list pFact '?x)] (list qFact '?x))
                       (tu/fwd [(list qFact '?x)] (list pFact '?x))])
          r (v/assert kb (list rFact Subject) CxHome)
          p (held kb (list pFact Subject) CxHome)
          q (held kb (list qFact Subject) CxHome)]
      (is (= {:leaves (conj rules r) :computed? false} (such-that kb (constantly true) [p q])))
      (is (= {:leaves rules :computed? false} (such-that kb #(not= r %) [p q]))))))

;; ---- asserted-defining-leaves: the walk halts at skeletal things ---------------------

(defn- defining-leaves [kb hs] (defining/asserted-defining-leaves kb hs))

(tu/deftest-kb the-defining-walk-halts-at-a-lifted-copy
  (tu/with-terms [CxHome Subject Marker liftedRel conclusion]
    (contexts kb [CxHome])
    (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse)
    (let [source (v/assert kb (list liftedRel Subject Marker) CxHome)
          rh (v/assert kb (tu/fwd [(list liftedRel '?x Marker)] (list conclusion '?x)) 'CxUniverse)
          copy (held kb (list liftedRel Subject Marker) 'CxUniverse)
          h (held kb (list conclusion Subject) 'CxUniverse)]
      (is (some? copy))
      (is (contains? (:leaves (leaves kb h)) source) "the plain walk descends through the copy")
      (is (= {:leaves #{rh} :computed? false} (defining-leaves kb h)))
      (is (= {:leaves #{} :computed? false} (defining-leaves kb copy))))))

(tu/deftest-kb the-defining-walk-halts-at-a-computed-literal
  (tu/with-terms [CxHome theSum]
    (contexts kb [CxHome])
    (let [rh (v/assert kb (tu/fwd [(list 'evaluate '?s (list '+ 1 2))] (list theSum '?s)) CxHome)
          h (held kb (list theSum 3) CxHome)]
      (is (= {:leaves #{rh} :computed? true} (leaves kb h)))
      (is (= {:leaves #{rh} :computed? false} (defining-leaves kb h))))))

(tu/deftest-kb the-defining-walk-halts-at-nat-bookkeeping
  ;; Forced to the entailing reading, since the bookkeeping copy is the arg type's entailment.
  (tu/with-entailing
    (tu/with-terms [CxHome Namespace namespace_kind LookupFn lookupOf access_kind usedBy Observer]
      (contexts kb [CxHome])
      (doseq [sentence [(list 'reifiable_function LookupFn)
                        (list 'result LookupFn access_kind)
                        (list 'functionCorrespondingPredicate LookupFn lookupOf 2)
                        (list 'arg lookupOf 1 namespace_kind)]]
        (v/assert kb sentence 'CxUniverse))
      (v/assert kb (list usedBy (list LookupFn Namespace) Observer) CxHome)
      (let [bk (held kb (list namespace_kind Namespace) 'CxUniverse)
            nat-formula? #(= 'natFormula (first (:sentence (v/sentex kb %))))]
        (is (some? bk))
        (is (not (v/premise? kb bk)) "the global copy is deduced from the NAT's bookkeeping")
        (is (some nat-formula? (:leaves (leaves kb bk))) "which the plain walk keeps as a leaf")
        (is (seq (:leaves (defining-leaves kb bk))))
        (is (not-any? nat-formula? (:leaves (defining-leaves kb bk)))
            "and the defining walk halts at")))))

(tu/deftest-kb the-defining-walk-keeps-an-asserted-rule-and-walks-a-deduced-one
  (testing "an asserted rule is a leaf"
    (tu/with-terms [CxHome Subject aFact bFact cFact]
      (contexts kb [CxHome])
      (let [r1 (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
            r2 (v/assert kb (tu/fwd [(list bFact '?x)] (list cFact '?x)) CxHome)
            a (v/assert kb (list aFact Subject) CxHome)
            c (held kb (list cFact Subject) CxHome)]
        (is (= {:leaves #{a r1 r2} :computed? false} (defining-leaves kb c))))))
  (testing "a deduced rule is walked to the fact it rests on"
    (tu/with-terms [bachelor Tom unmarried]
      (let [dh (v/assert kb (list 'defnNecessary bachelor (list unmarried '?x)) 'CxUniverse)
            bh (v/assert kb (list bachelor Tom) 'CxUniverse)
            h (held kb (list unmarried Tom) 'CxUniverse)]
        (is (= {:leaves #{bh dh} :computed? false} (defining-leaves kb h)))))))
