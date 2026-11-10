;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rewrite-query-test
  "The positive rewriteOf public relation is read through reader representatives.
  Raw storage remains directed."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite-query :as rewrite-query]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb caller-data-is-not-an-internal-rule-head-instruction
  (let [forged '(:vaelii.impl.resolution/rule-head (unestablished A) (unestablished ?x))]
    (doseq [engine [:dfs :inference]]
      (binding [v/*query-engine* engine]
        (is (empty? (v/prove kb forged 'CxUniverse {:max-depth 1})))))
    (is (empty? (v/query kb forged 'CxUniverse {:max-depth 1})))
    (tu/with-terms [instructionName hasPattern]
      (v/assert kb (list instructionName :vaelii.impl.resolution/rule-head) 'CxUniverse)
      (let [dynamic [(list instructionName '?instruction)
                     '(?instruction (unestablished A) (unestablished ?x))]]
        (is (empty? (v/query kb dynamic 'CxUniverse {:max-depth 1}))))
      (let [quoted (list hasPattern
                         (list 'Quote '(:vaelii.impl.resolution/rule-head
                                        (unestablished A) (unestablished B))))]
        (v/assert kb quoted 'CxUniverse)
        (doseq [engine [:dfs :inference]]
          (binding [v/*query-engine* engine]
            (is (= #{{}} (set (v/prove kb quoted 'CxUniverse {:max-depth 1}))))))))))

(tu/deftest-kb real-head-steps-keep-their-owner-through-search-transformations
  (tu/with-terms [Target Value]
    (let [reader (rewrite-query/head-reader kb 'CxUniverse)
          other (rewrite-query/head-reader kb 'CxUniverse)
          [_ step] (res/rule-head-match kb (list 'rewriteOf Target '?answer)
                                        (list 'rewriteOf Target '?raw) {} 'CxUniverse reader)
          ready (res/substitute step {'?raw Value})
          [canonical _] (sx/canonical-conjunction [ready])]
      (is (res/rule-head-step? ready reader))
      (is (res/rule-head-step? (first canonical) reader))
      (is (not (res/rule-head-step? ready other)))
      (is (nil? (res/solve-rule-head other ready {})))
      (is (= {'?answer Value} (res/solve-rule-head reader ready {})))
      (doseq [read [#(v/prove kb ready 'CxUniverse {:max-depth 1})
                    #(v/query kb ready 'CxUniverse {:max-depth 1})]]
        (is (= :shape (tu/refusal-type read)))))))

(tu/deftest-kb a-bounded-dfs-resume-keeps-the-head-owner-of-its-pending-stack
  (tu/with-terms [QualifierFn namedRoot FirstRoot SecondRoot binaryRelation]
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn 2)) 'CxUniverse)
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (doseq [root [FirstRoot SecondRoot]]
      (v/assert-rule kb [(list 'arity binaryRelation 2)]
                     (list 'rewriteOf root (list QualifierFn 2))
                     'CxUniverse {:direction :backward}))
    (binding [v/*query-engine* :dfs]
      (let [budget {:max-results 1 :max-depth 3}
            result (loop [partial (v/prove-within kb (list 'rewriteOf '?left namedRoot) 'CxUniverse budget)
                          answers [] rounds 0]
                     (let [answers (into answers (:results partial))]
                       (if (and (:resume partial) (< rounds 8))
                         (recur (v/resume partial budget) answers (inc rounds))
                         {:answers answers :complete? (= :complete (:status partial))})))]
        (is (:complete? result))
        (is (every? (set (map #(get % '?left) (:answers result))) [FirstRoot SecondRoot]))))))

(tu/deftest-kb tail-commutation-rejoins-rewrite-consumers-without-moving-a-value-tuple
  (doseq [mark-first? [true false]]
    (tu/with-terms [PairFn qualifierOf preferred old Alpha Beta seen]
      (v/assert kb (list 'reifiable_function PairFn) 'CxUniverse)
      (v/assert kb (list 'functionCorrespondingPredicate PairFn qualifierOf 1) 'CxUniverse)
      (let [tuple (list qualifierOf preferred Alpha Beta)
            tuple-h (v/assert kb tuple 'CxUniverse {:strength :monotonic})
            expression (list PairFn Beta Alpha)
            goal (list 'rewriteOf preferred expression)
            mark (list 'commutativeInArgAndRest qualifierOf 2)
            mark-h (when mark-first? (v/assert kb mark 'CxUniverse))]
        (is (neg? (compare (str Alpha) (str Beta))))
        (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
        (v/assert-rule kb [goal] (list seen preferred) 'CxUniverse {:direction :forward})
        (when-not mark-first?
          (is (false? (v/ask? kb goal 'CxUniverse)))
          (is (false? (v/ask? kb (list seen preferred) 'CxUniverse))))
        (let [mark-h (or mark-h (v/assert kb mark 'CxUniverse))]
          (is (true? (v/ask? kb goal 'CxUniverse)))
          (is (true? (v/ask? kb (list seen preferred) 'CxUniverse)))
          (is (= tuple (:sentence (v/sentex kb tuple-h))))
          (is (false? (v/ask? kb (list 'reifiable_function qualifierOf) 'CxUniverse)))
          (is (empty? (filter #(= PairFn (first (nth (:sentence %) 2 nil)))
                              (v/find-sentexes kb 'natFormula))))
          (v/retract! kb mark-h)
          (is (false? (v/ask? kb goal 'CxUniverse)))
          (is (false? (v/ask? kb (list seen preferred) 'CxUniverse)))
          (v/assert kb mark 'CxUniverse)
          (is (true? (v/ask? kb goal 'CxUniverse)))
          (is (true? (v/ask? kb (list seen preferred) 'CxUniverse)))
          (is (= tuple (:sentence (v/sentex kb tuple-h)))))))))

(deftest an-independent-strict-use-wins-on-each-source-axis
  (let [relaxed {:nonplacing #{1} :label-only #{1} :readers #{'CxPrivate}}]
    (is (nil? (prover-types/merge-source-roles [1] nil [2] nil)))
    (is (= {:readers #{'CxPrivate}}
           (prover-types/merge-source-roles [1] relaxed [1] nil)
           (prover-types/merge-source-roles [1] nil [1] relaxed)))
    ;; Neither proof-local strict use may be relaxed by the other axis. Reader
    ;; constraints accumulate; they are not logical bindings or synthetic premises.
    (is (= {:readers #{'CxPrivate 'CxOther}}
           (prover-types/merge-source-roles
            [1] {:nonplacing #{1} :readers #{'CxPrivate}}
            [1] {:label-only #{1} :readers #{'CxOther}})))))

(deftest rewrite-read-associations-are-unioned-without-changing-logical-values
  (let [a {:goal '(rewriteOf 17 ?x) :handle 1 :outputs '{?x 23}}
        b {:goal '(rewriteOf ?y 23) :handle 2 :outputs '{?y 17}}]
    (is (= #{a b}
           (:rewrite-reads
            (prover-types/merge-source-roles
             #{1} {:rewrite-reads #{a}} #{2} {:rewrite-reads #{b}}))))))

(deftest application-evidence-observes-the-existing-branch-without-another-resolution
  ;; This is a branch-observer control, not a substitute for the forward proof tests.
  ;; The same resolver functions and short-circuit precedence must run in both modes.
  (doseq [[namespace alias value mapped expected source expected-calls]
          [["nat" 'namedRoot 'otherValue 'oldMap 'namedRoot :rewrite [:rewrite]]
           ["nat" nil 'namedRoot 'oldMap 'namedRoot :correspondence [:rewrite :correspondence]]
           ["nat" nil nil 'oldMap 'oldMap :map [:rewrite :correspondence :map]]
           ["nat" nil nil nil nil :unresolved [:rewrite :correspondence :map]]
           ["cx" nil 'notAContext 'cx/old 'cx/old :map [:rewrite :map]]]]
    (let [calls (atom [])
          events (atom [])
          lookup (fn [observe?]
                   (binding [nat-read/*application-read* (when observe? #(swap! events conj %))]
                     (nat-read/existing-term nil '(QualifierFn base) namespace 'CxPrivate)))]
      (with-redefs [nat-read/rewrite-target (fn [& _] (swap! calls conj :rewrite) alias)
                    nat-read/correspondence-value (fn [& _] (swap! calls conj :correspondence) value)
                    nat-read/dedup-constant (fn [& _] (swap! calls conj :map) mapped)]
        (is (= expected (lookup false)))
        (is (= expected-calls @calls))
        (reset! calls [])
        (is (= expected (lookup true)))
        (is (= expected-calls @calls))
        (is (= [{:expression '(QualifierFn base) :namespace namespace :context 'CxPrivate
                 :source source :value expected :readings []}]
               (map #(dissoc % :attempt-readings) @events)))))))

(deftest map-fallback-does-not-claim-the-failed-correspondence-attempt
  (let [events (atom [])]
    (with-redefs [nat-read/rewrite-target (constantly nil)
                  nat-read/correspondence-value
                  (fn [& _]
                    (res/*correspondence-read* {:operation :tuple :handle 123 :value 'ambiguous})
                    nil)
                  nat-read/dedup-constant
                  (fn [& _]
                    (res/*normalization-read* {:operation :normalization :supports [#{456}]})
                    'nat/existing)]
      (is (= 'nat/existing
             (binding [nat-read/*application-read* #(swap! events conj %)]
               (nat-read/existing-term nil '(QualifierFn base) "nat" 'CxPrivate))))
      (is (= :map (:source (last @events))))
      (is (= [{:operation :normalization :supports [#{456}]}]
             (:readings (last @events)))))))

(tu/deftest-kb a-correspondence-trace-retains-the-actual-declaration-and-tuple
  (tu/with-terms [QualifierFn qualifierOf base namedRoot old]
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (let [declaration (v/assert kb (list 'functionCorrespondingPredicate QualifierFn qualifierOf 2)
                                'CxUniverse)
          tuple (v/assert kb (list qualifierOf base namedRoot) 'CxUniverse)
          events (atom [])
          expression (list QualifierFn base)]
      (is (= namedRoot
             (binding [nat-read/*application-read* #(swap! events conj %)
                       res/*correspondence-read* #(swap! events conj %)]
               (nat-read/existing-term kb expression "nat" 'CxUniverse))))
      (is (some #(= {:expression expression :namespace "nat" :context 'CxUniverse
                     :source :correspondence :value namedRoot}
                    (dissoc % :readings :attempt-readings))
                @events))
      (is (some #(and (= :declarations (:operation %))
                      (some #{[QualifierFn qualifierOf 2 declaration]} (:declarations %)))
                @events))
      (is (some #(and (= :tuple (:operation %)) (= tuple (:handle %))
                      (= namedRoot (:value %))
                      (sequential? (get-in % [:lineage :pattern]))
                      (= (list qualifierOf base '?v) (:goal %)))
                @events))
      (let [[actual readings] (rewrite-query/endpoint-reading kb 'CxUniverse expression)]
        (is (= namedRoot actual (rewrite-query/endpoint kb 'CxUniverse expression)))
        (is (some #(and (= :tuple (:operation %)) (= tuple (:handle %))) readings))
        (is (some #(and (= :correspondence (:source %)) (= namedRoot (:value %))) readings))
        (is (some #(and (= :retrieval-candidate (:operation %)) (= tuple (:handle %))
                        (= (list qualifierOf base '?v) (:goal %)))
                  readings)))
      (v/assert kb (list 'rewriteOf namedRoot old) 'CxUniverse)
      (let [goal (list 'rewriteOf '?left expression)
            plain (set (rewrite-query/matches kb goal 'CxUniverse))
            traced (vec (rewrite-query/matches-with-readings kb goal 'CxUniverse))
            certificates (vec (rewrite-query/match-certificates kb goal 'CxUniverse))]
        (is (seq traced))
        (is (= plain (set (map #(subvec % 0 3) traced))))
        (is (= (set (map second plain)) (set (map first certificates))))
        (is (every? #(and (contains? (second %) declaration)
                          (contains? (second %) tuple)
                          (= #{'CxUniverse} (:readers (nth % 2)))) certificates))
        (is (every? #(contains? (:label-only (nth % 2)) declaration) certificates))
        (is (every? #(not (contains? (:label-only (nth % 2)) tuple)) certificates))
        (is (every? #(= namedRoot (get (second %) '?left)) traced))
        (is (some #(some (fn [event] (= :correspondence (:source event)))
                         (:events (nth % 3)))
                  traced))))))

(tu/deftest-kb admitted-correspondence-lineage-survives-both-retrieval-paths
  (tu/with-terms [QualifierFn qualifierOf narrowQualifierOf base namedRoot]
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'genl narrowQualifierOf qualifierOf) 'CxUniverse)
    (v/assert kb (list 'symmetric narrowQualifierOf) 'CxUniverse)
    (let [declaration (v/assert kb (list 'functionCorrespondingPredicate QualifierFn qualifierOf 2)
                                'CxUniverse)
          h (v/assert kb (list narrowQualifierOf base namedRoot) 'CxUniverse)
          expression (list QualifierFn base)]
      (doseq [hierarchical? [false true]]
        (binding [res/*hierarchical-retrieval* hierarchical?]
          (let [events (atom [])
                plain (nat-read/existing-term kb expression "nat" 'CxUniverse)
                traced (binding [nat-read/*application-read* #(swap! events conj %)]
                         (nat-read/existing-term kb expression "nat" 'CxUniverse))
                selected (:readings (last @events))
                admitted (filter #(= :tuple (:operation %)) selected)]
            (is (= namedRoot plain traced))
            (is (= :correspondence (:source (last @events))))
            (is (some #(some #{[QualifierFn qualifierOf 2 declaration]} (:declarations %)) selected))
            (is (some #(and (= h (:handle %)) (= namedRoot (:value %))
                            (= (list qualifierOf base '?v) (:goal %))
                            (sequential? (get-in % [:lineage :probe]))
                            (= narrowQualifierOf (first (get-in % [:lineage :pattern]))))
                      admitted))))))))

(tu/deftest-kb a-rewrite-binding-roundtrips-and-composes-before-projection
  (tu/with-terms [preferred old marked unrelated]
    (v/assert kb (list marked preferred) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
    (let [answers (set (v/query kb (list 'rewriteOf preferred '?x) 'CxUniverse))]
      (is (= #{{'?x preferred}} answers))
      (doseq [answer answers]
        (is (true? (v/ask? kb (list 'rewriteOf preferred (get answer '?x)) 'CxUniverse))))
      (is (= #{{'?x preferred}}
             (set (v/query kb (list 'and (list 'rewriteOf preferred '?x)
                                    (list marked '?x)) 'CxUniverse)))))
    (testing "a variable predicate does not expose the retired spelling"
      (let [bindings (filter #(= 'rewriteOf (get % '?p))
                             (v/query kb (list '?p preferred '?x) 'CxUniverse))]
        (is (seq bindings))
        (is (= #{preferred} (set (map #(get % '?x) bindings))))))
    (testing "normalization is applied before repeated-variable unification"
      (is (contains? (set (v/query kb '(rewriteOf ?x ?x) 'CxUniverse))
                     {'?x preferred}))
      (is (= #{{'?x preferred}}
             (set (v/query kb (list 'rewriteOf '?x old) 'CxUniverse))))
      (is (contains? (set (v/query kb '(rewriteOf ?x ?y) 'CxUniverse))
                     {'?x preferred '?y preferred})))
    (testing "a visible witness permits either spelling, not universal reflexivity"
      (is (true? (v/ask? kb (list 'rewriteOf old preferred) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'rewriteOf preferred preferred) 'CxUniverse)))
      (is (false? (v/ask? kb (list 'rewriteOf unrelated unrelated) 'CxUniverse))))
    (testing "the actual stored edge is still directed and as authored"
      (is (some? (v/handle-of kb (list 'rewriteOf preferred old) 'CxUniverse)))
      (is (nil? (v/handle-of kb (list 'rewriteOf preferred preferred) 'CxUniverse))))))

(tu/deftest-kb a-private-rewrite-is-not-a-public-normalization-witness
  (tu/with-terms [preferred old CxPrivate CxChild CxSibling]
    (v/assert kb (list 'genlCx CxChild CxPrivate) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) CxPrivate)
    (doseq [reader [CxPrivate CxChild]]
      (is (= #{{'?x preferred}}
             (set (v/query kb (list 'rewriteOf old '?x) reader))))
      (doseq [pred ['sameAs 'equals]]
        (is (= #{{'?x preferred}} (set (v/query kb (list pred old '?x) reader))))))
    (doseq [reader ['CxUniverse CxSibling]]
      (is (empty? (v/query kb (list 'rewriteOf old '?x) reader)))
      (is (false? (v/ask? kb (list 'rewriteOf preferred preferred) reader)))
      (doseq [pred ['sameAs 'equals]]
        (is (= #{{'?x old}} (set (v/query kb (list pred old '?x) reader))))))))

(tu/deftest-kb identity-class-answers-keep-live-aliases-but-not-retired-spellings
  (tu/with-terms [preferred old identityAlias]
    (v/assert kb (list 'sameAs preferred identityAlias) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
    (doseq [pred ['sameAs 'equals]]
      (is (= #{preferred identityAlias}
             (set (map #(get % '?x)
                       (v/query kb (list pred preferred '?x) 'CxUniverse)))))
      (is (true? (v/ask? kb (list pred preferred identityAlias) 'CxUniverse))))))

(tu/deftest-kb a-forward-rewrite-consumer-constructs-the-public-endpoint-not-the-raw-payload
  ;; Ordinary unquoted conclusions could hide a raw binding by reifying it on write.
  ;; Constructing a mention makes that difference observable instead.
  (tu/with-terms [QualifierFn base namedRoot mentioned CxPrivate CxSibling]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert-rule kb [(list 'rewriteOf namedRoot '?endpoint)]
                   (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                   'CxUniverse {:direction :forward})
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn base)) CxPrivate)
    (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
    (is (false? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn base))) CxPrivate)))
    (doseq [reader ['CxUniverse CxSibling]]
      (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) reader))))))

(tu/deftest-kb a-backward-rewrite-head-does-not-reintroduce-a-resolved-application
  (tu/with-terms [QualifierFn base namedRoot binaryRelation]
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn base)) 'CxUniverse)
    ;; Arity is itself forced-monotonic: the fixture does not rely on an unforced
    ;; ordinary antecedent licensing an equation conclusion.
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (let [head (list 'rewriteOf namedRoot (list QualifierFn base))
          rh (v/assert-rule kb [(list 'arity binaryRelation 2)] head
                            'CxUniverse {:direction :backward})]
      (is (some? rh))
      (is (= head (:consequent (v/sentex kb rh))))
      (is (= #{{'?endpoint namedRoot}}
             (set (v/query kb (list 'rewriteOf namedRoot '?endpoint) 'CxUniverse
                           {:max-depth 3})))))))

(tu/deftest-kb backward-heads-read-body-bound-endpoints-before-public-joins
  (tu/with-terms [QualifierFn namedRoot ruleRoot binaryRelation marked absent]
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn 2)) 'CxUniverse)
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (v/assert kb (list marked namedRoot) 'CxUniverse)
    (let [head (list 'rewriteOf ruleRoot (list QualifierFn '?number))
          rh (v/assert-rule kb [(list 'arity binaryRelation '?number)] head
                            'CxUniverse {:direction :backward})
          goal (list 'rewriteOf ruleRoot '?endpoint)
          joined [goal (list marked '?endpoint)
                  (list 'unknown (list absent '?endpoint))]]
      (is (some? rh))
      (is (= head (last (v/readable-sentence (v/sentex kb rh)))))
      ;; No equation with this left endpoint is stored: a closed success must use
      ;; the backward head rather than the alias fact that normalizes its rhs.
      (is (empty? (v/sentexes-matching kb (list 'rewriteOf ruleRoot '?raw))))
      (doseq [engine [:dfs :inference]]
        (binding [v/*query-engine* engine]
          (is (v/provable? kb (list 'rewriteOf ruleRoot namedRoot) 'CxUniverse
                           {:max-depth 3}))
          (is (= #{{'?endpoint namedRoot}}
                 (set (v/prove kb goal 'CxUniverse {:max-depth 3}))))
          (is (= #{{'?rest (list namedRoot)}}
                 (set (v/prove kb (list 'rewriteOf ruleRoot '. '?rest) 'CxUniverse
                               {:max-depth 3}))))
          (is (= #{{'?endpoint namedRoot}}
                 (set (v/prove kb joined 'CxUniverse {:max-depth 3}))))))
      (is (= #{{'?endpoint namedRoot}}
             (set (v/query kb goal 'CxUniverse {:max-depth 3}))))
      (let [proofs (v/query kb goal 'CxUniverse {:max-depth 3 :proof? true})]
        (is (seq proofs))
        (doseq [answer proofs]
          (is (= {'?endpoint namedRoot} (:bindings answer)))
          (is (= 1 (count (:because (first (:proof answer)))))))))))

(tu/deftest-kb a-variable-predicate-consequent-uses-the-same-public-head-view
  (tu/with-terms [QualifierFn namedRoot ruleRoot binaryRelation]
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn 2)) 'CxUniverse)
    (v/assert kb (list 'arity 'rewriteOf 2) 'CxUniverse)
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (let [rh (v/assert-rule kb [(list 'arity '?relation '?number)
                                (list 'arity binaryRelation '?number)]
                            (list '?relation ruleRoot (list QualifierFn '?number))
                            'CxUniverse {:direction :backward})]
      (is (some? rh))
      (doseq [engine [:dfs :inference]]
        (binding [v/*query-engine* engine]
          (is (= #{{'?endpoint namedRoot}}
                 (set (v/prove kb (list 'rewriteOf ruleRoot '?endpoint) 'CxUniverse
                               {:max-depth 3}))))
          (is (= #{{'?endpoint (list QualifierFn 2)}}
                 (set (v/prove kb (list binaryRelation ruleRoot '?endpoint) 'CxUniverse
                               {:max-depth 3})))))))))

(tu/deftest-kb backward-head-normalization-remains-reader-local
  (tu/with-terms [QualifierFn namedRoot ruleRoot binaryRelation CxPrivate CxSibling]
    (doseq [reader [CxPrivate CxSibling]]
      (v/assert kb (list 'genlCx reader 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (let [expression (list QualifierFn 2)
          goal (list 'rewriteOf ruleRoot '?endpoint)]
      (v/assert kb (list 'rewriteOf namedRoot expression) CxPrivate)
      (is (some? (v/assert-rule kb [(list 'arity binaryRelation '?number)]
                                (list 'rewriteOf ruleRoot (list QualifierFn '?number))
                                'CxUniverse {:direction :backward})))
      (doseq [engine [:dfs :inference]]
        (binding [v/*query-engine* engine]
          (is (= #{{'?endpoint namedRoot}}
                 (set (v/prove kb goal CxPrivate {:max-depth 3}))))
          (doseq [reader ['CxUniverse CxSibling]]
            (is (= #{{'?endpoint expression}}
                   (set (v/prove kb goal reader {:max-depth 3}))))))))))

(defn- assert-lazy-rewrite-head!
  ([kb binary-relation rule-root qualifier-fn]
   (assert-lazy-rewrite-head! kb binary-relation rule-root qualifier-fn 'CxUniverse))
  ([kb binary-relation rule-root qualifier-fn context]
   (v/assert kb
             (list 'set/lazyForwardRule
                   (rules/rule-sentence [(list 'arity binary-relation '?number)]
                                        (list 'rewriteOf rule-root (list qualifier-fn '?number))))
             context)))

(tu/deftest-kb dotted-public-rewrite-goals-preserve-canonical-rest-bindings
  (tu/with-terms [preferred old]
    (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
    (is (= #{{'?rest (list preferred)}}
           (set (v/query kb (list 'rewriteOf preferred '. '?rest) 'CxUniverse))))
    (is (= #{{'?predicate 'rewriteOf '?rest (list preferred)}}
           (set (filter #(= 'rewriteOf (get % '?predicate))
                        (v/query kb (list '?predicate preferred '. '?rest) 'CxUniverse)))))
    (is (= #{{'?predicate 'rewriteOf '?args (list preferred preferred)}}
           (set (filter #(= 'rewriteOf (get % '?predicate))
                        (v/query kb (list '?predicate '. '?args) 'CxUniverse)))))))

(tu/deftest-kb lazy-heads-bind-canonical-endpoints-without-storing-an-equation
  (tu/with-terms [QualifierFn namedRoot ruleRoot binaryRelation mentioned restMentioned closed]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (let [alias-h (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn 2)) 'CxUniverse)
          body-h (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
          lazy-h (assert-lazy-rewrite-head! kb binaryRelation ruleRoot QualifierFn)]
      (is (some? lazy-h))
      (v/assert-rule kb [(list 'rewriteOf ruleRoot '?endpoint)]
                     (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                     'CxUniverse {:direction :forward})
      (v/assert-rule kb [(list 'rewriteOf ruleRoot namedRoot)] (list closed ruleRoot)
                     'CxUniverse {:direction :forward})
      (v/assert-rule kb [(list 'rewriteOf ruleRoot '. '?tail)]
                     (list restMentioned (list 'Quasiquote (list 'Unquote '?tail)))
                     'CxUniverse {:direction :forward})
      (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) 'CxUniverse)))
      (is (false? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn 2))) 'CxUniverse)))
      (is (true? (v/ask? kb (list closed ruleRoot) 'CxUniverse)))
      (is (true? (v/ask? kb (list restMentioned (list 'Quote (list namedRoot))) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'rewriteOf ruleRoot '?raw))))
      (v/retract! kb alias-h)
      (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) 'CxUniverse)))
      (is (true? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn 2))) 'CxUniverse)))
      (is (false? (v/ask? kb (list closed ruleRoot) 'CxUniverse)))
      (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn 2)) 'CxUniverse)
      (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) 'CxUniverse)))
      (v/retract! kb body-h)
      (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) 'CxUniverse)))
      (is (false? (v/ask? kb (list restMentioned (list 'Quote (list namedRoot))) 'CxUniverse)))
      (is (false? (v/ask? kb (list closed ruleRoot) 'CxUniverse))))))

(tu/deftest-kb lazy-head-counter-readings-are-proof-local-to-private-rivals
  (tu/with-terms [QualifierFn namedRoot rival ruleRoot binaryRelation mentioned CxPrivate CxSibling]
    (quasiquote/ensure-quasiquote-functions kb)
    (doseq [reader [CxPrivate CxSibling]]
      (v/assert kb (list 'genlCx reader 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (let [expression (list QualifierFn 2)]
      (v/assert kb (list 'rewriteOf namedRoot expression) 'CxUniverse)
      (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
      (is (some? (assert-lazy-rewrite-head! kb binaryRelation ruleRoot QualifierFn)))
      (v/assert-rule kb [(list 'rewriteOf ruleRoot '?endpoint)]
                     (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                     'CxUniverse {:direction :forward})
      (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
      (let [rival-h (v/assert kb (list 'rewriteOf rival expression) CxPrivate)]
        (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
        (is (true? (v/ask? kb (list mentioned (list 'Quote expression)) CxPrivate)))
        (doseq [reader ['CxUniverse CxSibling]]
          (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) reader)))
          (is (false? (v/ask? kb (list mentioned (list 'Quote expression)) reader))))
        (v/retract! kb rival-h)
        (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
        (is (false? (v/ask? kb (list mentioned (list 'Quote expression)) CxPrivate)))))))

(tu/deftest-kb a-private-lazy-head-is-not-authorized-by-public-discovery-contexts
  (tu/with-terms [QualifierFn namedRoot ruleRoot binaryRelation mentioned CxPrivate CxSibling]
    (quasiquote/ensure-quasiquote-functions kb)
    (doseq [reader [CxPrivate CxSibling]]
      (v/assert kb (list 'genlCx reader 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn 2)) 'CxUniverse)
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (is (some? (assert-lazy-rewrite-head! kb binaryRelation ruleRoot QualifierFn CxPrivate)))
    (v/assert-rule kb [(list 'rewriteOf ruleRoot '?endpoint)]
                   (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                   'CxUniverse {:direction :forward})
    (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
    (doseq [reader ['CxUniverse CxSibling]]
      (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) reader))))))

(tu/deftest-kb lazy-heads-follow-a-new-correspondence-without-a-map
  (tu/with-terms [QualifierFn qualifierOf preferred ruleRoot binaryRelation mentioned]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'arity binaryRelation 2) 'CxUniverse)
    (is (some? (assert-lazy-rewrite-head! kb binaryRelation ruleRoot QualifierFn)))
    (v/assert-rule kb [(list 'rewriteOf ruleRoot '?endpoint)]
                   (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                   'CxUniverse {:direction :forward})
    (let [expression (list QualifierFn 2)
          written (list mentioned (list 'Quote expression))
          resolved (list mentioned (list 'Quote preferred))
          tuple-h (v/assert kb (list qualifierOf 2 preferred) 'CxUniverse)]
      (is (true? (v/ask? kb written 'CxUniverse)))
      (is (false? (v/ask? kb resolved 'CxUniverse)))
      (let [declaration-h (v/assert kb (list 'functionCorrespondingPredicate QualifierFn qualifierOf 2)
                                    'CxUniverse)]
        (is (false? (v/ask? kb written 'CxUniverse)))
        (is (true? (v/ask? kb resolved 'CxUniverse)))
        (v/retract! kb tuple-h)
        (is (true? (v/ask? kb written 'CxUniverse)))
        (is (false? (v/ask? kb resolved 'CxUniverse)))
        (v/assert kb (list qualifierOf 2 preferred) 'CxUniverse)
        (is (true? (v/ask? kb resolved 'CxUniverse)))
        (v/retract! kb declaration-h)
        (is (true? (v/ask? kb written 'CxUniverse)))
        (is (false? (v/ask? kb resolved 'CxUniverse))))
      (is (empty? (filter #(= expression (nth (:sentence %) 2 nil))
                          (v/find-sentexes kb 'natFormula)))))))

(tu/deftest-kb a-counter-reading-does-not-canonicalize-an-old-output-again
  (tu/with-terms [preferred old]
    (let [h (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
          rows (rewrite-query/row-readings kb h 'CxUniverse)]
      (is (= #{(list 'rewriteOf preferred preferred)} (set (map first rows))))
      ;; Asking this closed goal would normalize `old` again and answer true. A
      ;; firing that bound `old` must compare the returned canonical fact instead.
      (is (true? (v/ask? kb (list 'rewriteOf preferred old) 'CxUniverse)))
      (is (not-any? #(= (list 'rewriteOf preferred old) (first %)) rows))
      (is (= (list 'rewriteOf preferred old) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb an-unresolved-alias-certificate-retains-both-ambiguity-witnesses
  (tu/with-terms [QualifierFn base namedRoot rival CxPrivate]
    (v/assert kb (list 'genlCx CxPrivate 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (let [expression (list QualifierFn base)
          first-h (v/assert kb (list 'rewriteOf namedRoot expression) 'CxUniverse)
          goal (list 'rewriteOf namedRoot '?endpoint)
          original (first (rewrite-query/match-certificates kb goal CxPrivate))
          association (first (:rewrite-reads (nth original 2)))
          rival-h (v/assert kb (list 'rewriteOf rival expression) CxPrivate)
          certificates (vec (rewrite-query/match-certificates kb goal CxPrivate))]
      (is (= #{{'?endpoint expression}} (set (map first certificates))))
      ;; With only first-h the same resolver returns namedRoot, not expression.
      ;; A raw candidate event could not warrant this negative-branch decision.
      (is (every? #(and (contains? (second %) first-h)
                        (contains? (second %) rival-h)) certificates))
      (let [counter (vec (rewrite-query/counter-certificates kb association CxPrivate))]
        (is (seq counter))
        (is (every? #(contains? (first %) rival-h) counter)))
      (is (empty? (rewrite-query/counter-certificates kb association 'CxUniverse)))
      (v/retract! kb rival-h)
      (let [restored (vec (rewrite-query/match-certificates kb goal CxPrivate))]
        (is (= #{{'?endpoint namedRoot}} (set (map first restored))))
        (is (every? #(not (contains? (second %) rival-h)) restored))
        (is (empty? (rewrite-query/counter-certificates kb association CxPrivate)))))))

(defn- check-map-source-role
  "The primitive reads stated maps globally and derived maps only in their context."
  [kb stated?]
  (doseq [sentence '[(genlCx CxPrivate CxUniverse) (reifiable_function QualifierFn)
                     (rewriteOf namedRoot old)]]
    (v/assert kb sentence 'CxUniverse))
  (if stated?
    (v/assert kb '(natFormula namedRoot (QualifierFn base)) 'CxPrivate)
    (do (v/assert-rule kb '[(marker base)] '(natFormula namedRoot (QualifierFn base))
                       'CxPrivate {:direction :forward})
        (v/assert kb '(marker base) 'CxPrivate)))
  (let [h (v/handle-of kb '(natFormula namedRoot (QualifierFn base)) 'CxPrivate)
        goal '(rewriteOf namedRoot (QualifierFn base))
        private (vec (rewrite-query/match-certificates kb goal 'CxPrivate))
        public (vec (rewrite-query/match-certificates kb goal 'CxUniverse))]
    (is (some? h))
    (is (= stated? (v/premise? kb h)))
    (is (seq private))
    (is (= stated? (boolean (seq public))))
    (doseq [[_ supports reading] (concat private public)]
      (is (contains? supports h))
      (is (contains? (:label-only reading) h))
      (is (= stated? (contains? (:nonplacing reading) h))))))

(tu/deftest-kb a-stated-map-retains-global-structural-source-roles
  (check-map-source-role kb true))

(tu/deftest-kb a-derived-map-retains-contextual-source-placement
  (check-map-source-role kb false))

(tu/deftest-kb a-private-rival-rechecks-an-inherited-forward-rewrite-answer
  (tu/with-terms [QualifierFn base namedRoot rival mentioned CxPrivate CxSibling]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert kb (list 'genlCx CxPrivate 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf namedRoot (list QualifierFn base)) 'CxUniverse)
    (v/assert-rule kb [(list 'rewriteOf namedRoot '?endpoint)]
                   (list mentioned (list 'Quasiquote (list 'Unquote '?endpoint)))
                   'CxUniverse {:direction :forward})
    (doseq [reader ['CxUniverse CxPrivate CxSibling]]
      (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) reader))))
    (let [rival-h (v/assert kb (list 'rewriteOf rival (list QualifierFn base)) CxPrivate)]
      ;; The old alias still exists and is IN. The new ambiguity changes the read,
      ;; so withdrawing only positive support cannot repair this inherited proof.
      (is (false? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
      (is (true? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn base))) CxPrivate)))
      (doseq [reader ['CxUniverse CxSibling]]
        (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) reader)))
        (is (false? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn base))) reader))))
      (v/retract! kb rival-h)
      (is (true? (v/ask? kb (list mentioned (list 'Quote namedRoot)) CxPrivate)))
      (is (false? (v/ask? kb (list mentioned (list 'Quote (list QualifierFn base))) CxPrivate))))))

(tu/deftest-kb a-new-correspondence-rejoins-a-quoted-ground-application-without-a-map
  (tu/with-terms [QualifierFn qualifierOf base preferred old mentioned CxPrivate CxSibling]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert kb (list 'genlCx CxPrivate 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf preferred old) 'CxUniverse)
    (v/assert-rule kb [(list 'rewriteOf '?left (list QualifierFn base))]
                   (list mentioned (list 'Quasiquote (list 'Unquote '?left)))
                   'CxUniverse {:direction :forward})
    (is (false? (v/ask? kb (list mentioned (list 'Quote preferred)) CxPrivate)))
    (let [declaration (v/assert kb (list 'functionCorrespondingPredicate QualifierFn qualifierOf 2)
                                'CxUniverse)
          tuple (v/assert kb (list qualifierOf base preferred) CxPrivate)]
      (is (true? (v/ask? kb (list mentioned (list 'Quote preferred)) CxPrivate)))
      (doseq [reader ['CxUniverse CxSibling]]
        (is (false? (v/ask? kb (list mentioned (list 'Quote preferred)) reader))))
      ;; The written application is an equation mention, not an independently used
      ;; application. Neither a named alias nor an opaque placeholder licenses it.
      (is (empty? (filter #(= (list QualifierFn base) (nth (:sentence %) 2 nil))
                          (v/find-sentexes kb 'natFormula))))
      (v/retract! kb declaration)
      (is (false? (v/ask? kb (list mentioned (list 'Quote preferred)) CxPrivate)))
      (v/retract! kb tuple))))
