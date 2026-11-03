;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.defining-test
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.defining :as defining]
            [vaelii.impl.kb :as stored-kb]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

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
                      (list 'functionCorrespondingPredicate LookupFn lookupOf)
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

(tu/deftest-kb a-grounded-ordinary-rule-can-introduce-a-defined-constant
  (tu/with-terms [CxHome Subject Marker trigger target]
    (contexts kb [CxHome])
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list trigger Marker) (list target Subject))) CxHome)
    (is (= #{} (v/defining-contexts kb Subject)))
    (let [h (v/assert kb (list trigger Marker) CxHome)]
      (is (v/ask? kb (list target Subject) CxHome))
      (is (= #{CxHome} (v/defining-contexts kb Subject)))
      (v/retract! kb h)
      (is (= #{} (v/defining-contexts kb Subject))))))

(tu/deftest-kb a-skeletal-trigger-and-ordinary-rule-do-not-create-a-global-ordinary-home
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
    (is (= #{CxOrigin} (v/defining-contexts kb Subject)))))

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

;; ---- asserted leaves: the premises a datum's valid support bottoms out in -----------

(defn- leaves [kb h] (defining/asserted-leaves kb h))

(defn- held [kb sentence context] (v/handle-of kb sentence context))

(tu/deftest-kb a-premise-is-its-own-asserted-leaf
  (tu/with-terms [CxHome Subject tagged]
    (contexts kb [CxHome])
    (let [h (v/assert kb (list tagged Subject) CxHome)]
      (is (= {:leaves #{h} :computed? false} (leaves kb h))))))

(tu/deftest-kb a-chain-bottoms-out-in-its-premise-and-not-its-rules
  (tu/with-terms [CxHome Subject aFact bFact cFact]
    (contexts kb [CxHome])
    (let [r1 (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
          r2 (v/assert kb (tu/fwd [(list bFact '?x)] (list cFact '?x)) CxHome)
          a (v/assert kb (list aFact Subject) CxHome)
          c (held kb (list cFact Subject) CxHome)]
      (is (some? c))
      (is (= {:leaves #{a} :computed? false} (leaves kb c)))
      (is (not-any? #{r1 r2} (:leaves (leaves kb c)))))))

(tu/deftest-kb a-diamond-reaches-its-shared-premise-once
  (tu/with-terms [CxHome Subject aFact bFact cFact dFact eFact]
    (contexts kb [CxHome])
    (v/assert kb (tu/fwd [(list aFact '?x)] (list bFact '?x)) CxHome)
    (v/assert kb (tu/fwd [(list aFact '?x)] (list cFact '?x)) CxHome)
    (v/assert kb (tu/fwd [(list bFact '?x) (list cFact '?x) (list eFact '?x)] (list dFact '?x))
              CxHome)
    (let [a (v/assert kb (list aFact Subject) CxHome)
          e (v/assert kb (list eFact Subject) CxHome)
          d (held kb (list dFact Subject) CxHome)]
      (is (some? d))
      (is (= {:leaves #{a e} :computed? false} (leaves kb d))))))

(tu/deftest-kb a-support-cycle-bottoms-out-in-the-premise-that-grounds-it
  (tu/with-terms [CxHome Subject pFact qFact rFact]
    (contexts kb [CxHome])
    (v/assert kb (tu/fwd [(list rFact '?x)] (list pFact '?x)) CxHome)
    (v/assert kb (tu/fwd [(list pFact '?x)] (list qFact '?x)) CxHome)
    (v/assert kb (tu/fwd [(list qFact '?x)] (list pFact '?x)) CxHome)
    (let [r (v/assert kb (list rFact Subject) CxHome)
          p (held kb (list pFact Subject) CxHome)
          q (held kb (list qFact Subject) CxHome)]
      (is (= 2 (count (v/supporting-justifications kb p))) "p rests on r and on q")
      (is (= {:leaves #{r} :computed? false} (leaves kb p)))
      (is (= {:leaves #{r} :computed? false} (leaves kb q))))))

(tu/deftest-kb a-guard-covered-alternative-contributes-no-leaf
  (tu/with-terms [bird penguin bat flies Opus CxFly]
    (contexts kb [CxFly])
    (let [rule #(list 'set/defaultRule (list 'set/forwardRule (list 'implies (list % '?x) (list flies '?x))))]
      (v/assert kb (rule bird) CxFly)
      (v/assert kb (rule bat) CxFly)
      (v/assert kb (list 'exceptWhen (list penguin '?x) (rule bird)) CxFly)
      (let [b (v/assert kb (list bird Opus) CxFly)
            t (v/assert kb (list bat Opus) CxFly)
            _ (v/assert kb (list penguin Opus) CxFly)
            h (held kb (list flies Opus) CxFly)]
        (is (= #{:guard :supports} (set (vals (v/justification-verdicts kb h CxFly)))))
        (is (= {:leaves #{t} :computed? false} (leaves kb h)))
        (is (not (contains? (:leaves (leaves kb h)) b)))))))

(tu/deftest-kb a-blocked-alternative-contributes-no-leaf
  (tu/with-terms [bird penguin bat flies Opus CxFly]
    (contexts kb [CxFly])
    (v/assert kb (list 'closed_extent_predicate penguin) CxFly)
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule
                             (list 'implies (list 'and (list bird '?x) (list 'not (list penguin '?x)))
                                   (list flies '?x)))) CxFly)
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule (list 'implies (list bat '?x) (list flies '?x)))) CxFly)
    (let [b (v/assert kb (list bird Opus) CxFly)
          t (v/assert kb (list bat Opus) CxFly)
          _ (v/assert kb (list penguin Opus) CxFly)
          h (held kb (list flies Opus) CxFly)]
      (is (= #{:blocked :supports} (set (vals (v/justification-verdicts kb h CxFly)))))
      (is (= {:leaves #{t} :computed? false} (leaves kb h)))
      (is (not (contains? (:leaves (leaves kb h)) b))))))

(tu/deftest-kb an-all-computed-firing-has-no-leaf-and-is-marked-computed
  (tu/with-terms [CxHome theSum]
    (contexts kb [CxHome])
    (let [rh (v/assert kb (tu/fwd [(list 'evaluate '?s (list '+ 1 2))] (list theSum '?s)) CxHome)
          h (held kb (list theSum 3) CxHome)]
      (is (= [[[] rh]] (mapv (juxt :antecedents :informant) (v/supporting-justifications kb h))))
      (is (= {:leaves #{} :computed? true} (leaves kb h))))))

(tu/deftest-kb a-computed-literal-beside-a-fact-leaves-only-the-fact
  (tu/with-terms [CxHome Ann Bob ageOf youngerThan]
    (contexts kb [CxHome])
    (let [a (v/assert kb (list ageOf Ann 10) CxHome)
          b (v/assert kb (list ageOf Bob 20) CxHome)
          _ (v/assert kb (tu/fwd [(list ageOf '?x '?a) (list ageOf '?y '?b) (list 'lessThan '?a '?b)]
                                 (list youngerThan '?x '?y)) CxHome)
          h (held kb (list youngerThan Ann Bob) CxHome)]
      (is (= {:leaves #{a b} :computed? false} (leaves kb h))))))
