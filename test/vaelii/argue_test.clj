;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argue-test
  "Tests for vaelii.core/argue — four-valued epistemic status queries."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb argue-true-for-asserted-fact
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (is (= :true (:verdict (v/argue kb (list dog Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-unknown-for-unasserted-fact
  (tu/with-terms [hungry Muffet]
    (is (= :unknown (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-false-for-explicitly-negated-fact
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :false (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-contradiction-for-both-sides-at-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list hungry Muffet) 'CxUniverse)
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :contradiction (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-true-via-genl
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (is (= :true (:verdict (v/argue kb (list animal Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-rule-expansion-with-max-depth
  (tu/with-terms [dog has_fur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list has_fur '?x) 'CxUniverse {:direction :backward})
    (testing "without opts: ask does not fire backward rules"
      (is (= :unknown (:verdict (v/argue kb (list has_fur Muffet) 'CxUniverse)))))
    (testing "with max-depth: rules fire"
      (is (= :true (:verdict (v/argue kb (list has_fur Muffet) 'CxUniverse {:max-depth 3})))))
    (testing "and the rule-derived side carries the search's derivation, not a JTMS why"
      ;; the conclusion of a backward rule is never stored, so the JTMS has nothing to
      ;; explain it with and `:for-why` is the wrong key to look under
      (let [r (v/argue kb (list has_fur Muffet) 'CxUniverse {:max-depth 3})]
        (is (nil? (:for-why r)))
        (is (seq (:for-derivation r)))
        (is (= (list has_fur Muffet) (:goal (first (:for-derivation r)))))
        (is (= :rule (:via (first (:for-derivation r)))))))))

(tu/deftest-kb argue-stops-a-ground-goal-search-at-its-first-answer
  ;; The stored fact answers (fed Muffet) at the root.  Ten rules also conclude it, and
  ;; a search run past the first answer expands each of their children.
  (tu/with-terms [fed Muffet]
    (v/assert kb (list fed Muffet) 'CxUniverse)
    (dotimes [_ 10]
      (tu/with-terms [source]
        (v/assert-rule kb [(list source '?x)] (list fed '?x) 'CxUniverse
                       {:direction :backward})))
    (let [steps (atom 0)
          step! inf/step!]
      ;; the 1-arity calls the 2-arity through the var, so only the 2-arity counts
      (with-redefs [inf/step! (fn ([sess] (step! sess))
                                ([sess dl] (swap! steps inc) (step! sess dl)))]
        (is (= :true (:verdict (v/argue kb (list fed Muffet) 'CxUniverse {:max-depth 2})))))
      (is (= 3 @steps)
          "one step for the side that holds, and two for the other: its root and the empty frontier"))))

(tu/deftest-kb argue-derives-through-a-rewrite-whose-residual-repeats-a-conjunct
  ;; (a K) rewrites to (b K) ∧ (e K), and (e K) to (b K) ∧ (f K): the second (b K) folds
  ;; onto the first, left of the rewritten literal.
  (tu/with-terms [qqa qqb qqe qqf FoldK]
    (v/assert-rule kb [(list qqb '?x) (list qqe '?x)] (list qqa '?x) 'CxUniverse
                   {:direction :backward})
    (v/assert-rule kb [(list qqb '?x) (list qqf '?x)] (list qqe '?x) 'CxUniverse
                   {:direction :backward})
    (v/assert kb (list qqb FoldK) 'CxUniverse)
    (v/assert kb (list qqf FoldK) 'CxUniverse)
    (let [r (v/argue kb (list qqa FoldK) 'CxUniverse {:max-depth 2})]
      (is (= :true (:verdict r)))
      (is (= :rule (:via (first (:for-derivation r))))))))

(tu/deftest-kb argue-a-stored-side-carries-the-jtms-why-and-no-derivation
  ;; the two explanations are a fallback, not a pair: where the JTMS answers, the search
  ;; is not run at all — a tree nobody reads costs a whole query
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [r (v/argue kb (list dog Muffet) 'CxUniverse {:max-depth 3})]
      (is (= :true (:verdict r)))
      (is (true? (:believed? (:for-why r))))
      (is (nil? (:for-derivation r))))))

(tu/deftest-kb argue-derives-no-tree-for-a-pattern-or-at-depth-zero
  (tu/with-terms [dog has_fur Muffet Rex]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list has_fur '?x) 'CxUniverse {:direction :backward})
    (testing "a pattern answers once per binding, so one tree off the front names none of them"
      (let [r (v/argue kb (list has_fur '?who) 'CxUniverse {:max-depth 3})]
        (is (= :true (:verdict r)))
        (is (= 2 (count (:for r))) "both answers are reported")
        (is (nil? (:for-derivation r)) "and no tree claims to explain them")))
    (testing "depth 0 expands no rule, so a side it still answers has no derivation"
      ;; the goal has to be provable at depth 0 for this to say anything: an unprovable
      ;; one carries no derivation because it carries no `:for` either
      (let [r (v/argue kb (list dog Muffet) 'CxUniverse {:max-depth 0})]
        (is (= :true (:verdict r)))
        (is (nil? (:for-derivation r)))))))

(tu/deftest-kb argue-a-prover-answered-side-carries-the-one-node-the-search-took
  ;; `genl` transitivity is the registry's answer, not a rule's — nothing is stored, so
  ;; the JTMS has no why, and the search's tree is the single `:leaf` node it walked.
  ;; True, and as much as the search knows: asserted because it is the shape every
  ;; taxonomy-, evaluatable- and calculus-answered side reports
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (let [r (v/argue kb (list animal Muffet) 'CxUniverse {:max-depth 3})]
      (is (= :true (:verdict r)))
      (is (nil? (:for-why r)) "the transitive conclusion is not stored")
      (is (= [{:goal (list animal Muffet) :via :leaf}] (:for-derivation r))))))

(tu/deftest-kb argue-explains-both-sides-of-a-contradiction
  ;; the asymmetry this pair of keys exists to close: before, a side a rule derived was
  ;; reported as provable and left unexplained, so an adjudicating caller saw evidence
  ;; for the stored side and silence for the other
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(list dog '?x)] (list barks '?x) 'CxUniverse
                   {:direction :backward :strength :default})
    (v/assert kb (list 'not (list barks Muffet)) 'CxUniverse {:strength :monotonic})
    (let [r (v/argue kb (list barks Muffet) 'CxUniverse {:max-depth 3})]
      (is (= :contradiction (:verdict r)))
      (testing "the stored side reads from the JTMS"
        (is (= :monotonic (:defeat-class (:against-why r))))
        (is (nil? (:against-derivation r))))
      (testing "the derived side reads from the search"
        (is (nil? (:for-why r)))
        (is (= :rule (:via (first (:for-derivation r)))))))))

(tu/deftest-kb argue-monotonic-wins-over-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse {:strength :default})
    (v/assert kb (list hungry Muffet) 'CxUniverse {:strength :monotonic})
    (is (= :true (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-reads-both-sides-inside-a-deferred-batch-and-the-winner-after-it
  ;; the closing settle places the pair, so inside the batch both sides stand and the
  ;; known-true one outranks the default; after it the default side is withdrawn
  (tu/with-terms [hungry Muffet]
    (let [r (v/with-deferred-settle kb
              (v/assert kb (list hungry Muffet) 'CxUniverse {:strength :monotonic})
              (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse {:strength :default})
              (v/argue kb (list hungry Muffet) 'CxUniverse))
          after (v/argue kb (list hungry Muffet) 'CxUniverse)]
      (is (= [:monotonic :default] [(:defeat-class (:for-why r)) (:defeat-class (:against-why r))])
          "inside the batch each side answers with its class")
      (is (= :true (:verdict r)))
      (is (= [:monotonic nil] [(:defeat-class (:for-why after)) (:defeat-class (:against-why after))])
          "after the settle the default side is withdrawn")
      (is (= :true (:verdict after))))))

(tu/deftest-kb argue-with-proofs-asked-reads-the-derivation-off-its-own-answers
  (tu/with-terms [dog has_fur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list has_fur '?x) 'CxUniverse {:direction :backward})
    (let [r (v/argue kb (list has_fur Muffet) 'CxUniverse {:max-depth 3 :proof? true})]
      (is (= :true (:verdict r)))
      (is (= (:proof (first (:for r))) (:for-derivation r)))
      (is (= :rule (:via (first (:for-derivation r))))))))

(tu/deftest-kb argue-refuses-an-option-it-does-not-read-at-its-own-entry-point
  ;; `argue` reaches `query` only when `:max-depth` is there and takes the
  ;; no-rule-expansion `ask` arm otherwise, so a key set checked downstream is not checked
  ;; at all for exactly the misspelling that matters: `{:max-deph 3}` would answer
  ;; `:unknown` for a sentence a rule derives, which is the failure the docstring says
  ;; must not happen.  The check is `argue`'s own, and the key set is `query`'s.
  (tu/with-terms [dog has_fur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list has_fur '?x) 'CxUniverse {:direction :backward})
    (let [goal    (list has_fur Muffet)
          refusal (fn [opts]
                    (try (v/argue kb goal 'CxUniverse opts) nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (testing "a misspelt depth is refused rather than taking the facts-only arm"
        (doseq [opts [{:max-deph 3} {:max-depth 3 :max-deph 4} {:nonsense 1}]]
          (let [d (refusal opts)]
            (is (= :unknown-option (:type d)) (pr-str opts))
            (is (= (vec (sort v/query-opt-keys)) (:options d)) "and the refusal names the key set")
            (is (seq (:unknown d))))))
      (testing "a non-map opts too"
        (is (= :unknown-option (:type (refusal :oops))))
        (is (= :unknown-option (:type (refusal [:max-depth 3])))))
      (testing "and every accepted key still answers"
        (is (= :true (:verdict (v/argue kb goal 'CxUniverse {:max-depth 3}))))
        (is (= :true (:verdict (v/argue kb goal 'CxUniverse
                                        {:max-depth 3 :strategy :depth-first}))))
        (is (= :unknown (:verdict (v/argue kb goal 'CxUniverse nil))))))))

;; ---- a retrieval-time transitiveInArg answer --------------------------------

(defn- transitive-skill-kb!
  "A wren that glides, `(genl gliding moving)` and `(transitiveInArg hasSkill 2 genl)`:
  `(hasSkill Pip moving)` is answered at retrieval and nothing stores it.  Returns the
  goal and the three sentences an explanation of it has to name."
  [kb wren hasSkill gliding moving Pip]
  (let [fact (list hasSkill Pip gliding)
        edge (list 'genl gliding moving)
        decl (list 'transitiveInArg hasSkill 2 'genl)]
    (v/assert kb (list wren Pip) 'CxUniverse)
    (v/assert kb fact 'CxUniverse)
    (v/assert kb edge 'CxUniverse)
    (v/assert kb decl 'CxUniverse)
    {:goal (list hasSkill Pip moving) :supports #{fact edge decl}}))

(defn- named-in
  "Every sentence `argue`'s explanation of the positive side names, at any depth: the
  JTMS map's `:sentence` and `:rule`, and the derivation's `:goal` and `:sentence`."
  [r]
  (->> (tree-seq coll? seq [(:for-why r) (:for-derivation r)])
       (filter map?)
       (mapcat (juxt :sentence :goal :rule))
       (remove nil?)
       set))

(tu/deftest-kb argue-answers-a-retrieval-time-transitive-in-arg-conclusion
  (tu/with-terms [wren hasSkill gliding moving Pip]
    (let [{:keys [goal]} (transitive-skill-kb! kb wren hasSkill gliding moving Pip)]
      (is (true? (v/ask? kb goal)))
      (is (= :true (:verdict (v/argue kb goal 'CxUniverse {:max-depth 3})))))))

(tu/deftest-kb ^:red argue-names-the-supports-of-a-retrieval-time-transitive-in-arg-conclusion
  ;; Red on vaelii#239.  The answer holds (the test above), but no record is stored for
  ;; it and the search reports it as one `:leaf`, so its explanation names none of the
  ;; fact it was reached from, the `genl` edge or the declaration that licenses the step.
  (tu/with-terms [wren hasSkill gliding moving Pip]
    (let [{:keys [goal supports]} (transitive-skill-kb! kb wren hasSkill gliding moving Pip)
          r (v/argue kb goal 'CxUniverse {:max-depth 3})]
      (is (= :true (:verdict r)))
      (is (= supports (into #{} (filter supports) (named-in r)))))))
