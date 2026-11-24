;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.abduce-test
  "`abduce`: the abducibility check, the loop, the caps, the record a hypothesis leaves and the
  isolation of the scratch context (docs/abduction.md)."
  (:require [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.abduce :as abduce]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- a-context
  "Hang `ctx` under CxUniverse; a `fresh` KB has no context wiring."
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse))

(defn- grant [kb pred ctx]
  (v/assert kb (list 'abducible_predicate pred) ctx))

(defn- a-rule [kb antecedents consequent ctx]
  (v/assert kb (list 'implies (cons 'and antecedents) consequent) ctx {:direction :forward}))

(defn- wabd!
  "`ctx` under CxUniverse, `premise` granted, and `(premise ?x)` → `(goal ?x)`."
  [kb goal premise ctx]
  (a-context kb ctx)
  (grant kb premise ctx)
  (a-rule kb [(list premise '?x)] (list goal '?x) ctx))

(defn- sentences [result] (set (map :sentence (:hypotheses result))))

;; ---- the headline --------------------------------------------------------

(tu/deftest-kb the-wabd-shape
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (is (not (v/provable? kb (list wabGoal N) CxTheory)))
    (let [r (v/abduce kb (list wabGoal N) CxTheory)]
      (testing "the one hypothesis that makes the goal follow, in the result's context"
        (is (= #{(list wabPremise N)} (sentences r)))
        (is (= (:context r) (:context (first (:hypotheses r))))))
      (testing "two solutions: the fact chaining stored, and the rule over the hypothesis"
        (is (= [{} {}] (:solutions r))))
      (testing "the scratch context is torn down, so the handle is nil"
        (is (nil? (:handle (first (:hypotheses r)))))
        (is (nil? (v/handle-of kb (list wabPremise N) (:context r))))
        (is (not (v/provable? kb (list wabGoal N) CxTheory)))))))

;; ---- the abducibility check ----------------------------------------------

(tu/deftest-kb the-abducibility-check-refuses-and-reports-what-it-will-not-assume
  ;; The constraint-only reading, where the cat in a dog-only slot is a refusal; under
  ;; the entailing reading the slot derives `(dog_ N)`, a clash and not a refusal, so the
  ;; abducibility check admits the hypothesis as `assert` admits the sentence.
  (tu/without-entailing
   (doseq [[why setup]
           [["ungranted" (fn [_ _ _ _ _] nil)]
            ["a believed negation denies it"
             (fn [kb p n cx _]
               (grant kb p cx)
               (v/assert kb (list 'not (list p n)) cx {:strength :monotonic}))]
            ["a clash the hypothesis would form: a cat in a dog-only slot"
             (fn [kb p n cx [dog_ cat_]]
               (grant kb p cx)
               (v/assert kb (list 'genl dog_ 'thing) cx)
               (v/assert kb (list 'genl cat_ 'thing) cx)
               (v/assert kb (list 'disjoint dog_ cat_) cx)
               (v/assert kb (list cat_ n) cx)
               (v/assert kb (list 'arg p 1 dog_) cx))]]]
     (tu/with-terms [wabGoal wabPremise N dog_ cat_ CxTheory]
       (a-context kb CxTheory)
       (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) CxTheory)
       (setup kb wabPremise N CxTheory [dog_ cat_])
       (let [r (v/abduce kb (list wabGoal N) CxTheory)]
         (is (empty? (:hypotheses r)) why)
         (is (empty? (:solutions r)) why)
         (is (= [(list wabPremise N)] (:refused r)) why)))))
  (testing "assert would refuse it: an argument no naming convention reads"
    (tu/with-terms [wabGoal wabPremise CxTheory]
      (wabd! kb wabGoal wabPremise CxTheory)
      (let [misnamed 'Baby_Penguin
            r        (v/abduce kb (list wabGoal misnamed) CxTheory)]
        (is (= :naming (try (v/assert kb (list wabPremise misnamed) CxTheory) nil
                            (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (is (empty? (:hypotheses r)))
        (is (= [(list wabPremise misnamed)] (:refused r)))))))

(tu/deftest-kb an-open-goal-hypothesizes-nothing
  (tu/with-terms [wabGoal wabPremise CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (let [r (v/abduce kb (list wabGoal '?who) CxTheory)]
      (is (empty? (:hypotheses r)))
      (is (empty? (:solutions r)))
      (testing "the refusal names the open literal the search ran out on — the rule's own
                variable, since the goal's is bound to it"
        (is (= 1 (count (:refused r))))
        (let [[pred arg] (first (:refused r))]
          (is (= wabPremise pred))
          (is (str/starts-with? (name arg) "?")))))))

(tu/deftest-kb the-abducibility-check-reads-grants-and-denials-visible-from-the-asking-context
  (doseq [[what in-sibling before after]
          [["a grant" (fn [kb p _ cx _] (grant kb p cx)) empty? seq]
           ["a denial" (fn [kb p n cx asker]
                         (grant kb p asker)
                         (v/assert kb (list 'not (list p n)) cx {:strength :monotonic}))
            seq empty?]]]
    (tu/with-terms [wabGoal wabPremise N CxTheory CxSibling]
      (a-context kb CxTheory)
      (a-context kb CxSibling)
      (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) CxTheory)
      (in-sibling kb wabPremise N CxSibling CxTheory)
      (is (before (:hypotheses (v/abduce kb (list wabGoal N) CxTheory)))
          (str what " in a context the asker cannot see"))
      (v/assert kb (list 'genlCx CxTheory CxSibling) 'CxUniverse)
      (is (after (:hypotheses (v/abduce kb (list wabGoal N) CxTheory)))
          (str what " once the asker sees its context")))))

(tu/deftest-kb retracting-the-grant-withdraws-the-permission
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (is (seq (:hypotheses (v/abduce kb (list wabGoal N) CxTheory))))
    (v/retract! kb (v/handle-of kb (list 'abducible_predicate wabPremise) CxTheory))
    (is (empty? (:hypotheses (v/abduce kb (list wabGoal N) CxTheory))))))

(tu/deftest-kb the-decision-is-a-predicate-over-a-sentence
  (tu/with-terms [wabPremise N CxTheory]
    (a-context kb CxTheory)
    (is (not (abduce/abducible? kb (list wabPremise N) CxTheory)) "ungranted")
    (grant kb wabPremise CxTheory)
    (is (abduce/abducible? kb (list wabPremise N) CxTheory))
    (is (not (abduce/abducible? kb (list wabPremise '?x) CxTheory)) "open")
    (is (not (abduce/abducible? kb (list 'not (list wabPremise N)) CxTheory))
        "a negation's functor is `not`, which nothing grants")
    (is (not (abduce/abducible? kb N CxTheory)) "not a literal")
    (is (not (abduce/abducible? kb (list (list wabPremise N) N) CxTheory))
        "a compound in functor position names no predicate")))

;; ---- what a hypothesis is ------------------------------------------------

(tu/deftest-kb a-kept-hypothesis-is-an-ordinary-premise-in-the-scratch-context
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (let [r    (v/abduce kb (list wabGoal N) CxTheory {:keep? true})
          actx (:context r)
          h    (:handle (first (:hypotheses r)))
          c    (v/handle-of kb (list wabGoal N) actx)
          e    (v/handle-of kb (list 'genlCx actx CxTheory) 'CxUniverse)]
      (try
        (testing "a believed :default premise, justified by nothing"
          (is (integer? h))
          (is (v/believed? kb h))
          (is (v/premise? kb h))
          (is (= :default (v/defeat-class kb h)))
          (is (true? (:premise? (tu/why-root kb h))))
          (is (empty? (:support (tu/why-root kb h)))))
        (testing "its provenance says it was assumed, and for what"
          (let [pv (v/provenance kb h)]
            (is (true? (:abduced pv)))
            (is (= (list wabGoal N) (:abduced-for pv)))
            (is (= :vaelii.impl.abduce/hypothesis (:creator pv)))))
        (testing "the rule fired over it, placement put the conclusion in the scratch
                  context, and `why` names the hypothesis as its support"
          (is (v/believed? kb c))
          (is (false? (:premise? (tu/why-root kb c))))
          (is (some (fn [s] (some #(= (list wabPremise N) (:sentence %)) (:because s)))
                    (:support (tu/why-root kb c)))))
        (testing "nothing that existed before can see any of it"
          (is (nil? (v/handle-of kb (list wabPremise N) CxTheory)))
          (is (empty? (v/sentexes-matching kb (list wabGoal N) CxTheory))))
        (testing "the edge that makes the scratch context is :monotonic"
          (is (= :monotonic (v/defeat-class kb e))))
        (finally (v/abduce-discard! kb r))))))

(tu/deftest-kb a-monotonic-fact-defeats-a-hypothesis-through-the-ordinary-path
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (let [r (v/abduce kb (list wabGoal N) CxTheory {:keep? true})
          h (:handle (first (:hypotheses r)))
          c (v/handle-of kb (list wabGoal N) (:context r))]
      (try
        (is (v/believed? kb c))
        (let [no (v/assert kb (list 'not (list wabPremise N)) CxTheory
                           {:strength :monotonic})]
          (testing "the hypothesis is defeated, and what it licensed goes out with it"
            (is (= :defeated (:reason (v/why-not kb h))))
            (is (not (v/believed? kb c))))
          (testing "retract the fact and the assumption comes back"
            (v/retract! kb no)
            (is (v/believed? kb h))))
        (finally (v/abduce-discard! kb r))))))

;; ---- isolation and cleanup -----------------------------------------------

(tu/deftest-kb an-ignored-abduction-leaves-the-kb-as-it-found-it
  (doseq [base-default? [false true]]
    (tu/with-terms [wabGoal wabPremise wabQ N CxTheory]
      (wabd! kb wabGoal wabPremise CxTheory)
      (when base-default?
        ;; the hypothesis's consequence contradicts a base default: arbitration relabels
        ;; and deletes no record
        (v/assert kb (list wabQ N) CxTheory)
        (a-rule kb [(list wabPremise '?x)] (list 'not (list wabQ '?x)) CxTheory))
      (let [sx-before (tu/sentex-ids kb)
            jd-before (tu/justification-ids kb)
            in-before (v/believed kb sx-before)
            r         (v/abduce kb (list wabGoal N) CxTheory)]
        (is (seq (:hypotheses r)))
        (is (= sx-before (tu/sentex-ids kb)) (str base-default?))
        (is (= jd-before (tu/justification-ids kb)) (str base-default?))
        (is (= in-before (v/believed kb sx-before)) (str base-default?))))))

(tu/deftest-kb discarding-takes-the-consequences-and-every-edge-with-it
  (tu/with-terms [wabGoal wabPremise N CxTheory CxOther]
    (wabd! kb wabGoal wabPremise CxTheory)
    (a-context kb CxOther)
    (let [sx-before (tu/sentex-ids kb)
          r         (v/abduce kb (list wabGoal N) CxTheory {:keep? true})]
      (is (integer? (v/handle-of kb (list wabGoal N) (:context r))))
      (v/assert kb (list 'genlCx (:context r) CxOther) 'CxUniverse)
      (let [gone (v/abduce-discard! kb r)]
        (is (<= 3 (:removed-sentexes gone)) "hypothesis, conclusion, two edges")
        (is (= sx-before (tu/sentex-ids kb))))
      (testing "discarding twice is a no-op, not an error"
        (is (= {:removed-sentexes 0 :removed-justifications 0}
               (v/abduce-discard! kb r)))))))

(tu/deftest-kb a-keep-past-the-cap-is-refused-and-names-the-kept-contexts
  (tu/with-terms [wabGoal wabPremise A B C CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (with-redefs [abduce/max-kept 2]
      (let [a (v/abduce kb (list wabGoal A) CxTheory {:keep? true})
            b (v/abduce kb (list wabGoal B) CxTheory {:keep? true})]
        (try
          (let [sx-before (tu/sentex-ids kb)
                refusal   (try (v/abduce kb (list wabGoal C) CxTheory {:keep? true})
                               nil
                               (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= :too-many-kept (:type refusal)))
            (is (= 2 (:max refusal)))
            (is (= (sort [(:context a) (:context b)]) (:contexts refusal)))
            (is (= sx-before (tu/sentex-ids kb)) "the refused call stored nothing"))
          (testing "a call that keeps nothing still runs at the cap"
            (is (seq (:hypotheses (v/abduce kb (list wabGoal C) CxTheory)))))
          (testing "discarding a kept context makes room for another"
            (v/abduce-discard! kb a)
            (v/abduce-discard! kb (v/abduce kb (list wabGoal C) CxTheory {:keep? true})))
          (finally (v/abduce-discard! kb a) (v/abduce-discard! kb b)))))))

(tu/deftest-kb a-throw-mid-search-still-tears-the-scratch-context-down
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (let [sx-before (tu/sentex-ids kb)
          ctxs      (set (v/contexts kb))]
      (is (thrown? RuntimeException
                   (with-redefs [res/prove (fn [& _] (throw (RuntimeException. "boom")))]
                     (v/abduce kb (list wabGoal N) CxTheory))))
      (is (= sx-before (tu/sentex-ids kb)))
      (is (= ctxs (set (v/contexts kb)))))))

(tu/deftest-kb a-hypothesis-cannot-block-a-base-rule-firing
  (tu/with-terms [wabTrigger wabConc wabBlock wabGoal N CxTheory]
    (a-context kb CxTheory)
    (v/assert kb (list 'exceptWhen (list wabBlock '?x)
                       (list 'set/forwardRule (list 'implies (list 'and (list wabTrigger '?x))
                                                    (list wabConc '?x))))
              CxTheory)
    (v/assert kb (list wabTrigger N) CxTheory)
    (let [c (v/handle-of kb (list wabConc N) CxTheory)]
      (is (integer? c))
      ;; the hypothesis is the literal the base rule's exception asks about
      (grant kb wabBlock CxTheory)
      (a-rule kb [(list wabBlock '?x)] (list wabGoal '?x) CxTheory)
      (let [r (v/abduce kb (list wabGoal N) CxTheory {:keep? true})]
        (try
          (is (= #{(list wabBlock N)} (sentences r)))
          (testing "the exception is evaluated in the base conclusion's placement context,
                    which cannot see into the scratch one: same handle, still believed"
            (is (= c (v/handle-of kb (list wabConc N) CxTheory)))
            (is (v/believed? kb c)))
          (finally (v/abduce-discard! kb r)))))))

;; ---- the search ----------------------------------------------------------

(tu/deftest-kb a-conjunction-is-assumed-round-by-round-up-to-the-cap
  (tu/with-terms [wabGoal wabP wabQ wabR N CxTheory]
    (a-context kb CxTheory)
    (run! #(grant kb % CxTheory) [wabP wabQ wabR])
    (a-rule kb [(list wabP '?x) (list wabQ '?x) (list wabR '?x)] (list wabGoal '?x) CxTheory)
    (testing "each round reaches one conjunct further than the last"
      (let [r (v/abduce kb (list wabGoal N) CxTheory)]
        (is (= #{(list wabP N) (list wabQ N) (list wabR N)} (sentences r)))
        (is (seq (:solutions r)))
        (is (= :complete (:status r)))))
    (testing "the cap stops it, says so, and does not report the unminted as refused"
      (let [r (v/abduce kb (list wabGoal N) CxTheory {:max-hypotheses 2})]
        (is (= 2 (count (:hypotheses r))))
        (is (empty? (:solutions r)))
        (is (= :capped (:status r)))
        (is (empty? (:refused r)))))
    (testing "a nil cap is no bound"
      (let [r (v/abduce kb (list wabGoal N) CxTheory {:max-hypotheses nil})]
        (is (= 3 (count (:hypotheses r))))
        (is (= :complete (:status r)))))))

(tu/deftest-kb the-hypothesis-set-is-irredundant
  (tu/with-terms [wabGoal wabP wabQ wabR N CxTheory]
    (a-context kb CxTheory)
    (grant kb wabP CxTheory)
    (grant kb wabQ CxTheory)
    (doseq [p [wabP wabQ wabR]]
      (a-rule kb [(list p '?x)] (list wabGoal '?x) CxTheory))
    (testing "both granted routes are assumed, then the first in content order is dropped;
              the solutions are the survivor's, and nothing is refused once one is proved"
      (let [r (v/abduce kb (list wabGoal N) CxTheory)]
        (is (= #{(list wabQ N)} (sentences r)))
        (is (= 2 (count (:solutions r))))
        (is (= [] (:refused r)))
        (is (= :complete (:status r)))))
    (testing "a cap that left a candidate unminted reports :capped though the goal follows"
      (let [r (v/abduce kb (list wabGoal N) CxTheory {:max-hypotheses 1})]
        (is (= #{(list wabP N)} (sentences r)))
        (is (seq (:solutions r)))
        (is (= :capped (:status r)))))))

(tu/deftest-kb a-goal-that-already-follows-assumes-nothing
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (v/assert kb (list wabPremise N) CxTheory)
    (let [r (v/abduce kb (list wabGoal N) CxTheory)]
      (is (empty? (:hypotheses r)))
      (is (seq (:solutions r)))
      (is (= :complete (:status r))))))

(tu/deftest-kb abducing-the-same-goal-twice-uses-two-scratch-contexts
  (tu/with-terms [wabGoal wabPremise N CxTheory]
    (wabd! kb wabGoal wabPremise CxTheory)
    (let [r1 (v/abduce kb (list wabGoal N) CxTheory)
          r2 (v/abduce kb (list wabGoal N) CxTheory)]
      (is (= #{(list wabPremise N)} (sentences r1) (sentences r2)))
      (is (not= (:context r1) (:context r2)))
      (is (zero? (v/count-in-context kb (:context r1))))
      (is (zero? (v/count-in-context kb (:context r2)))))))

(tu/deftest-kb the-depth-cap-bounds-where-a-dead-end-may-be-assumed
  (tu/with-terms [wabGoal wabMid wabPremise N CxTheory]
    (wabd! kb wabMid wabPremise CxTheory)
    (a-rule kb [(list wabMid '?x)] (list wabGoal '?x) CxTheory)
    ;; the dead end is two rule expansions deep; nil is no bound
    (doseq [[opts found?] [[{:max-depth 1} false] [{:max-depth 2} true]
                           [{:max-depth nil} true] [{} true]]]
      (let [r (v/abduce kb (list wabGoal N) CxTheory opts)]
        (if found?
          (is (= #{(list wabPremise N)} (sentences r)) (pr-str opts))
          (is (= [(list wabPremise N)] (:refused r)) (pr-str opts)))))))

(tu/deftest-kb a-branch-the-loop-guard-cuts-is-not-a-dead-end
  (tu/with-terms [wabP wabQ N CxTheory]
    (wabd! kb wabP wabQ CxTheory)
    (wabd! kb wabQ wabP CxTheory)
    ;; (wabP N) → (wabQ N) → (wabP N) is cut, and every goal on the path had a rule
    (let [r (v/abduce kb (list wabP N) CxTheory)]
      (is (empty? (:hypotheses r)))
      (is (empty? (:refused r)))
      (is (= :complete (:status r))))))

;; ---- the call ------------------------------------------------------------

(tu/deftest-kb a-variable-context-is-refused
  (tu/with-terms [wabGoal N]
    (is (= :not-ground (try (v/abduce kb (list wabGoal N) '?ctx) nil
                            (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(tu/deftest-kb a-conjunctive-goal-abduces-across-its-conjuncts
  (tu/with-terms [wabP wabQ N CxTheory]
    (a-context kb CxTheory)
    (grant kb wabP CxTheory)
    (grant kb wabQ CxTheory)
    (let [r (v/abduce kb [(list wabP N) (list wabQ N)] CxTheory)]
      (is (= #{(list wabP N) (list wabQ N)} (sentences r)))
      (is (seq (:solutions r))))))

(tu/deftest-kb the-context-defaults-to-universe
  (tu/with-terms [wabGoal wabPremise N]
    (grant kb wabPremise 'CxUniverse)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) 'CxUniverse)
    (let [r (v/abduce kb (list wabGoal N))]
      (is (= #{(list wabPremise N)} (sentences r)))
      (is (seq (:solutions r))))))

(tu/deftest-kb an-abduce-option-nothing-reads-is-refused
  ;; a misspelt :keep? would tear down the scratch context the caller meant to keep
  (tu/with-terms [pp Aa CxAb]
    (doseq [opts [{:max-hypothesis 2} {:keep true} {:max-dpeth 3}]]
      (let [e (try (v/abduce kb (list pp Aa) CxAb opts) nil
                   (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :unknown-option (:type e)) (pr-str opts))))))
