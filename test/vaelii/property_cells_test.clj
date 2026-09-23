;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.property-cells-test
  "One witness per property a subsystem claims and its own tests leave unasserted: context
  scoping, belief filtering and order independence, across the anytime readers, the lookup
  levels, exceptions, schematic rewriting, modal belief, generators and abduction — and
  locality through a whole KB on each index and network representation, where
  `jtms_locality_test` reads the window off a bare network.

  Each test states one subsystem against one property: a sibling context that must not see, a
  stored-but-defeated sentex that must not be read as believed, or two arrival orders that
  must agree.  Each opens with the control that makes its absence mean something — the
  owning context answers, the undefeated fact is read — so an empty read cannot pass by
  reading nothing."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private C 'CxUniverse)

(defn- siblings!
  "Wire each context directly under CxUniverse, so any two of them are siblings."
  [kb & cxs]
  (doseq [c cxs]
    (v/assert kb (list 'genlCx c C) C {:strength :monotonic})))

(defn- probe-kb
  "A second KB on its own space, cleared and with CxCore loaded."
  [tag]
  (doto (v/open-kb (update tu/plain-memory-space :space conj ::probe tag))
    (tu/clear-kb!)
    (tu/load-core!)))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(defn- xs [results] (set (keep #(get % '?x) results)))

;; ---- anytime / scoping -------------------------------------------------

(tu/deftest-kb anytime-reads-no-sibling-fact
  (tu/with-terms [p A CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list p A) CxA)
    (let [g (list p '?x)]
      (testing "control: the owning context answers A"
        (is (= #{A} (xs (:results (v/ask-within kb g CxA {:max-ms 60000})))))
        (is (= #{A} (xs (:results (v/prove-within kb g CxA {:max-ms 60000}))))))
      (testing "the sibling answers nothing"
        (is (= #{} (xs (:results (v/ask-within kb g CxB {:max-ms 60000})))))
        (is (= #{} (xs (:results (v/prove-within kb g CxB {:max-ms 60000})))))
        (is (empty? (:results (v/ask-within kb (list p A) CxB {:max-ms 60000}))))
        (is (empty? (:results (v/prove-within kb (list p A) CxB {:max-ms 60000}))))))))

;; ---- anytime / belief --------------------------------------------------

(tu/deftest-kb anytime-reads-no-defeated-fact
  (tu/with-terms [p A CxA]
    (siblings! kb CxA)
    (let [g   (list p '?x)
          aw  #(xs (:results (v/ask-within kb g CxA {:max-ms 60000})))
          pw  #(xs (:results (v/prove-within kb g CxA {:max-ms 60000})))
          agw #(seq (:results (v/ask-within kb (list p A) CxA {:max-ms 60000})))
          pgw #(seq (:results (v/prove-within kb (list p A) CxA {:max-ms 60000})))]
      (v/assert kb (list p A) CxA)
      (testing "control: the default is answered before the negation"
        (is (= #{A} (aw)))
        (is (= #{A} (pw))))
      (let [neg (v/assert kb (list 'not (list p A)) CxA {:strength :monotonic})]
        (testing "defeated: stored, OUT, and not answered"
          (is (some? (v/handle-of kb (list p A) CxA)))
          (is (false? (v/in? kb (v/handle-of kb (list p A) CxA))))
          (is (= #{} (aw)) "ask-within answered a defeated fact")
          (is (= #{} (pw)) "prove-within answered a defeated fact")
          (is (nil? (agw)) "ground ask-within answered a defeated fact")
          (is (nil? (pgw)) "ground prove-within answered a defeated fact"))
        (v/retract! kb neg)
        (testing "the negation retracted, A is back"
          (is (= #{A} (aw)))
          (is (= #{A} (pw))))))))

;; ---- levels / belief ---------------------------------------------------

(defn- flying-world
  "defeated_goals_test's world: birds fly by default, penguins do not, Tweety is a
  penguin, Robin a plain bird.  Returns the penguin rule's handle — the defeater."
  [kb {:keys [bird penguin flies Tweety Robin]}]
  (v/assert kb (list 'genl penguin bird) C)
  (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) C)
  (let [pr (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) C
                          {:direction :forward})]
    (v/assert kb (list penguin Tweety) C {:strength :monotonic})
    (v/assert kb (list bird Robin) C {:strength :monotonic})
    pr))

(defn- level-counts [kb goal]
  (into (sorted-map) (for [l (range 8)] [l (count (v/lookup kb l goal C))])))

(tu/deftest-kb levels-read-no-defeated-fact
  (tu/with-terms [bird penguin flies Tweety Robin]
    (let [pr   (flying-world kb {:bird bird :penguin penguin :flies flies
                                 :Tweety Tweety :Robin Robin})
          goal (list flies Tweety)]
      (testing "premise: stored and defeated"
        (is (some? (v/handle-of kb goal C)))
        (is (false? (v/in? kb (v/handle-of kb goal C)))))
      (let [defeated (level-counts kb goal)]
        (is (zero? (defeated 7)) "level 7 answered the defeated fact")
        (testing "levels 2-6 (belief-filtered per docs/levels.md) are empty too"
          (is (= {2 0 3 0 4 0 5 0 6 0} (select-keys defeated [2 3 4 5 6])))))
      (v/retract! kb pr)
      (testing "the defeater retracted, the fact revives"
        (is (true? (v/in? kb (v/handle-of kb goal C))))
        (let [revived (level-counts kb goal)]
          (is (pos? (revived 7)) "level 7 does not answer the revived fact"))))))

;; ---- exceptions / belief (defeat half) ---------------------------------

(defn- except-world!
  "The except_test rule shape, plus (bird Opus), with the penguin default and its
  monotonic negation asserted in `order`."
  [kb {:keys [bird penguin flies Opus Cx]} order]
  (siblings! kb Cx)
  (v/assert kb (list 'exceptWhen (list penguin '?b)
                     (default-rule [(list bird '?b)] (list flies '?b)))
            Cx)
  (v/assert kb (list bird Opus) Cx)
  (let [steps {:penguin  #(v/assert kb (list penguin Opus) Cx)
               :negation #(v/assert kb (list 'not (list penguin Opus)) Cx
                                    {:strength :monotonic})}]
    (doseq [s order] ((steps s)))))

(defn- except-reading [kb {:keys [penguin flies Opus Cx]}]
  {:penguin-believed? (boolean (seq (v/sentexes-matching kb (list penguin Opus) Cx)))
   :flies-believed?   (boolean (seq (v/sentexes-matching kb (list flies Opus) Cx)))
   :flies-ask?        (v/ask? kb (list flies Opus) Cx)})

(tu/deftest-kb a-defeated-exception-lifts-the-block
  (tu/with-terms [bird penguin flies Opus CxBird]
    (let [terms {:bird bird :penguin penguin :flies flies :Opus Opus :Cx CxBird}
          k1    (probe-kb :p4-penguin-first)
          k2    (probe-kb :p4-negation-first)]
      (try
        (except-world! k1 terms [:penguin :negation])
        (except-world! k2 terms [:negation :penguin])
        (let [r1 (except-reading k1 terms)
              r2 (except-reading k2 terms)]
          (testing "penguin default, then its monotonic negation"
            (is (false? (:penguin-believed? r1)) "premise: the penguin default is OUT")
            (is (true? (:flies-believed? r1)) "the defeated exception still blocks"))
          (testing "negation first, then the penguin default"
            (is (false? (:penguin-believed? r2)) "premise: the penguin default is OUT")
            (is (true? (:flies-believed? r2)) "the defeated exception still blocks"))
          (testing "order independence"
            (is (= r1 r2))))
        (finally (tu/clear-kb! k1) (tu/clear-kb! k2))))))

;; ---- equational / scoping ----------------------------------------------

(tu/deftest-kb an-equation-does-not-rewrite-a-sibling-fact
  (tu/with-terms [fatherOf grandfather_of parent_chain Tom Ann CxA CxB]
    (siblings! kb CxA CxB)
    (let [orig #(list parent_chain (list fatherOf (list fatherOf %)))
          norm #(list parent_chain (list grandfather_of %))]
      (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
                CxA)
      (v/assert kb (orig Ann) CxA)
      (v/assert kb (orig Tom) CxB)
      (testing "control: the equation rewrites a fact in its own context"
        (is (seq (v/sentexes-matching kb (norm Ann) CxA))))
      (testing "the sibling's fact is not rewritten"
        (is (seq (v/sentexes-matching kb (orig Tom) CxB))
            "the original no longer matches in the sibling")
        (is (empty? (v/sentexes-matching kb (norm Tom) CxB))
            "the rewritten form matches in the sibling")
        (is (nil? (v/handle-of kb (norm Tom) CxB))
            "a rewritten twin was stored in the sibling")
        (is (= [{'?y Tom}] (v/ask kb (list parent_chain (list fatherOf (list fatherOf '?y))) CxB)))
        (is (empty? (v/ask kb (list parent_chain (list grandfather_of '?y)) CxB)))))))

;; ---- belief (modal) / belief -------------------------------------------

(tu/deftest-kb a-defeated-agent-belief-is-not-projected
  (tu/with-terms [flies Tweety Agent]
    (let [cx  (modal/context-of-agent Agent)
          pos (list 'believes Agent (list flies Tweety))
          neg (list 'believes Agent (list 'not (list flies Tweety)))]
      (v/assert kb (list flies Tweety) cx)
      (testing "control: the default is projected"
        (is (v/ask? kb pos C)))
      (v/assert kb (list 'not (list flies Tweety)) cx {:strength :monotonic})
      (testing "defeated in the agent's context, the belief is not projected"
        (is (false? (v/in? kb (v/handle-of kb (list flies Tweety) cx))) "premise: OUT")
        (is (not (v/ask? kb pos C)) "ask projected a defeated belief")
        (is (not (v/provable? kb pos C)) "provable? projected a defeated belief")
        (is (v/ask? kb neg C) "control: the negation is projected")))))

;; ---- generators / scoping ----------------------------------------------

(tu/deftest-kb a-stamped-rule-does-not-fire-in-a-sibling
  (tu/with-terms [plan_verb outcomeEmotion planOf feels succeededAt Joy Tom Plan CxA CxB]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'implies
                       (list 'and (list plan_verb '?outcome)
                             (list outcomeEmotion '?outcome '?emotion))
                       (list 'implies
                             (list 'and (list planOf '?a '?p) (list '?outcome '?a '?p))
                             (list feels '?a '?emotion)))
              CxA)
    (v/assert kb (list plan_verb succeededAt) CxA)
    (v/assert kb (list outcomeEmotion succeededAt Joy) CxA)
    (doseq [cx [CxA CxB]]
      (v/assert kb (list planOf Tom Plan) cx)
      (v/assert kb (list succeededAt Tom Plan) cx))
    (let [feels-in #(into #{} (map '?e) (v/ask kb (list feels Tom '?e) %))]
      (testing "control: the stamped rule concludes in its own context"
        (is (= #{Joy} (feels-in CxA))))
      (testing "the sibling, holding the same member facts, gets no conclusion"
        (is (= #{} (feels-in CxB)))
        (is (nil? (v/handle-of kb (list feels Tom Joy) CxB)))
        (is (empty? (filter :antecedent (v/sentexes-in-context kb CxB)))
            "a rule was stamped into the sibling")))))

;; ---- abduction / order -------------------------------------------------

(defn- abduce-in [tag order {:keys [goalp prems N CxTheory]}]
  (let [k (probe-kb tag)]
    (try
      (v/assert k (list 'genlCx CxTheory C) C)
      (doseq [i order]
        (v/assert k (list 'abducible_predicate (prems i)) CxTheory))
      (doseq [i order]
        (v/assert k (list 'implies (cons 'and [(list (prems i) '?x)]) (list goalp '?x))
                  CxTheory {:direction :forward}))
      (set (map :sentence (:hypotheses (v/abduce k (list goalp N) CxTheory
                                                 {:max-hypotheses 1}))))
      (finally (tu/clear-kb! k)))))

(tu/deftest-kb the-hypothesis-cap-keys-on-content-not-order
  (tu/with-terms [goalp prema premb premc N CxTheory]
    (let [terms {:goalp goalp :prems [prema premb premc] :N N :CxTheory CxTheory}
          orders [[0 1 2] [0 2 1] [1 0 2] [1 2 0] [2 0 1] [2 1 0]]
          rs (into {} (for [o orders] [o (abduce-in [:p9 o] o terms)]))]
      (is (every? #(= 1 (count %)) (vals rs)) "premise: one hypothesis each")
      (is (= 1 (count (distinct (vals rs))))
          "the capped hypothesis depends on assertion order"))))

;; ---- locality, per representation --------------------------------------

(defn- chains!
  "`n` two-link forward chains, one root fact each."
  [kb n]
  (v/assert-rule kb ['(lp_root ?x)] '(lp_mid ?x) C {:direction :forward})
  (v/assert-rule kb ['(lp_mid ?x)] '(lp_leaf ?x) C {:direction :forward})
  (v/with-deferred-settle kb
    (dotimes [i n] (v/assert kb (list 'lp_root (symbol (str "Lp" i))) C)))
  kb)

(defn- window
  "The datums every settle `f` ran relabelled, taken as each window is cleared."
  [f]
  (let [orig jtms/reset-touched! w (atom #{})]
    (with-redefs [jtms/reset-touched! (fn [tms] (swap! w into (jtms/touched tms)) (orig tms))]
      (f))
    @w))

(deftest a-settle-window-does-not-grow-with-the-kb-on-any-representation
  ;; One chain's root arriving and one leaving relabel that chain — root, middle, leaf —
  ;; at 20 chains and at 400, on either network, over the KV index, the columnar trie,
  ;; and a fork whose chains all sit in its base.
  (doseq [tms [:reference :dense]
          [label open] [["memory" #(v/open-kb {:backend :memory :space [::loc :m tms %]
                                               :recover? false :tms tms})]
                        ["memory-columnar" #(v/open-kb {:backend :memory-columnar
                                                        :space [::loc :c tms %]
                                                        :recover? false :tms tms})]
                        ["fork" #(v/fork (doto (v/open-kb {:backend :memory
                                                           :space [::loc :base tms %]
                                                           :recover? false :tms tms})
                                           (tu/clear-kb!) (chains! %))
                                         ;; the default space, an ephemeral one nothing
                                         ;; else uses: a named one would hold a previous
                                         ;; run's writes on a second run in one JVM
                                         {:tms tms})]]]
    (testing (str label " on the " (name tms) " network")
      (is (= [3 3 3 3]
             (into [] (mapcat (fn [n]
                                (let [kb (open n)]
                                  (when-not (= "fork" label) (tu/clear-kb! kb) (chains! kb n))
                                  [(count (window #(v/assert kb '(lp_root LpNew) C)))
                                   (count (window #(v/retract! kb (v/handle-of kb '(lp_root Lp3) C))))])))
                   [20 400]))))))
