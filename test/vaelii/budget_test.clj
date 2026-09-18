;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.budget-test
  "Resource-bounded / anytime inference: `budget/collect` as the partial-result
  contract over a lazy stream, and its wiring into `ask-within` / `prove-within` /
  `resume`.  The invariants under test:

    * a generous budget runs dry (`:complete`) and equals the unbounded answer;
    * a tight budget returns a *prefix* and a `:resume` continuation, so
      concatenating results across `resume` reconstructs the whole answer;
    * bounding never over-realizes (it terminates on an infinite source);
    * `:max-cost` is qualitative — it drops whole prover tiers before the search;
    * `:max-depth` prunes the DFS's rule expansion, and `:max-term-growth` raises its
      other termination guard."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the pure collector (no KB) -----------------------------------------

(deftest collect-unbounded-runs-dry
  (let [r (budget/collect (range 5) nil)]
    (is (= [0 1 2 3 4] (:results r)))
    (is (= :complete (:status r)))
    (is (= 5 (:count r)))
    (is (nil? (:resume r)))
    ;; a wall-clock delta is never negative, so `(<= 0 …)` would be a reading of the
    ;; clock rather than of the collector; what the report promises is the key, carrying
    ;; `ms-since`'s fractional millisecond rather than a rounded one
    (is (double? (:elapsed-ms r)))))

(deftest collect-empty-source-is-complete
  (let [r (budget/collect () {:max-results 3})]
    (is (= [] (:results r)))
    (is (= :complete (:status r)))
    (is (nil? (:resume r)))))

(deftest collect-caps-at-max-results-and-resumes
  (let [r1 (budget/collect (range 10) {:max-results 3})]
    (is (= [0 1 2] (:results r1)))
    (is (= :capped (:status r1)))
    (is (= 3 (:count r1)))
    (is (fn? (:resume r1)))
    (testing "resume continues from exactly where it stopped"
      (let [r2 (budget/resume r1 {:max-results 4})]
        (is (= [3 4 5 6] (:results r2)))
        (is (= :capped (:status r2)))
        (testing "and the final resume runs dry"
          (let [r3 (budget/resume r2 nil)]
            (is (= [7 8 9] (:results r3)))
            (is (= :complete (:status r3)))
            (is (nil? (:resume r3)))))))
    (testing "concatenating every step reconstructs the whole source"
      (loop [r r1, acc []]
        (let [acc (into acc (:results r))]
          (if (:resume r)
            (recur (budget/resume r nil) acc)
            (is (= (vec (range 10)) acc))))))))

(deftest collect-does-not-over-realize-an-infinite-source
  ;; (range) with no bound is infinite; a cap must not hang, and must realize only
  ;; the prefix (the map side effect proves nothing past index 3 was pulled).
  (let [pulled (atom [])
        src    (map (fn [n] (swap! pulled conj n) n) (range))
        r      (budget/collect src {:max-results 3})]
    (is (= [0 1 2] (:results r)))
    (is (= :capped (:status r)))
    (is (= [0 1 2] @pulled) "exactly the prefix was realized, nothing past it")))

(deftest collect-timeout-then-resume
  (let [r1 (budget/collect (range 4) {:max-ms 0})]     ; a zero deadline trips immediately
    (is (= [] (:results r1)))
    (is (= :timeout (:status r1)))
    (is (fn? (:resume r1)))
    (testing "resuming with time to spare finishes the source"
      (let [r2 (budget/resume r1 nil)]
        (is (= [0 1 2 3] (:results r2)))
        (is (= :complete (:status r2)))))))

(deftest resume-of-a-complete-result-is-idempotent
  (let [r (budget/collect (range 3) nil)]
    (is (= :complete (:status r)))
    (is (identical? r (budget/resume r {:max-results 1}))
        "a complete result has no continuation, so resume returns it unchanged")))

;; ---- ask-within ---------------------------------------------------------

(tu/deftest-kb ask-within-unbounded-matches-ask
  (tu/with-terms [parentOf Tom Bob Ann Zed CxFam]
    (v/assert kb (list parentOf Tom Bob) CxFam)
    (v/assert kb (list parentOf Tom Ann) CxFam)
    (v/assert kb (list parentOf Tom Zed) CxFam)
    (let [goal (list parentOf Tom '?y)
          full (set (map #(get % '?y) (v/ask kb goal CxFam)))
          r    (v/ask-within kb goal CxFam {:max-ms 60000})]
      (is (= :complete (:status r)))
      (is (= #{Bob Ann Zed} full))
      (is (= full (set (map #(get % '?y) (:results r))))))))

(tu/deftest-kb ask-within-caps-and-resumes-to-the-whole-answer
  (tu/with-terms [parentOf Tom Bob Ann Zed CxFam]
    (v/assert kb (list parentOf Tom Bob) CxFam)
    (v/assert kb (list parentOf Tom Ann) CxFam)
    (v/assert kb (list parentOf Tom Zed) CxFam)
    (let [goal (list parentOf Tom '?y)
          full (set (map #(get % '?y) (v/ask kb goal CxFam)))
          r1   (v/ask-within kb goal CxFam {:max-results 1})]
      (is (= :capped (:status r1)))
      (is (= 1 (:count r1)))
      (testing "resuming until complete covers the whole answer, with no duplicates"
        (loop [r r1, acc []]
          (let [acc (into acc (map #(get % '?y) (:results r)))]
            (if (:resume r)
              (recur (v/resume r {:max-results 1}) acc)
              (do (is (= full (set acc)))
                  (is (= (count acc) (count (distinct acc))) "distinct survives resume")))))))))

(tu/deftest-kb ask-within-max-cost-drops-the-search-tier
  ;; No *registry* member is `:search` — nothing in it expands a rule — so the top tier
  ;; is exercised the way an application would reach it: a registered prover that
  ;; declares itself expensive, and a goal only it answers.
  (tu/with-terms [reachable Tom Ann CxFam]
    (let [costly (reify prover-types/Prover
                   (applicable?  [_ _ goal _] (= reachable (first goal)))
                   (est-bindings [_ _ _ _] 1)
                   (cost         [_ _ _ _] :search)
                   (completeness [_ _ _ _] 50)
                   (solve        [_ _ _ _] [{'?who Ann}]))]
      (v/add-prover kb costly)
      (let [goal (list reachable Tom '?who)]
        (testing "at :lookup the search tier is excluded, so no answer"
          (let [r (v/ask-within kb goal CxFam {:max-cost :lookup})]
            (is (= :complete (:status r)))
            (is (empty? (:results r)))))
        (testing "raising the ceiling to :search lets it run"
          (let [r (v/ask-within kb goal CxFam {:max-cost :search})]
            (is (= #{Ann} (set (map #(get % '?who) (:results r)))))))))))

(tu/deftest-kb a-ceiling-that-is-not-a-tier-is-refused
  ;; The mistake is invisible in the result — a ceiling that admits everything returns
  ;; exactly the answers a correct one would, only having done the work the bound
  ;; existed to avoid.  So a `:max-cost` outside the three tiers has to say so, and
  ;; carry a `:type` a caller can discriminate on rather than an NPE from inside a
  ;; comparison.
  (tu/with-terms [partOf A B D CxFam]
    (v/assert kb (list 'transitive partOf) CxFam)
    (v/assert kb (list partOf A B) CxFam)
    (v/assert kb (list partOf B D) CxFam)
    (let [goal (list partOf A '?y)]
      (testing "a real tier answers"
        (is (= :complete (:status (v/ask-within kb goal CxFam {:max-cost :compute})))))
      (doseq [bogus [:Lookup :cheap :lookups "lookup"]]
        (testing (str "a ceiling of " (pr-str bogus) " is refused, with the tiers named")
          (let [e (try (v/ask-within kb goal CxFam {:max-cost bogus})
                       nil
                       (catch clojure.lang.ExceptionInfo e e))]
            (is (some? e) (str (pr-str bogus) " was accepted as a cost tier"))
            (is (= :unknown-option (:type (ex-data e))))
            (is (= provers/cost-tiers (:known (ex-data e))))))))))

(tu/deftest-kb ask-within-max-cost-compute-tier
  ;; A declared-transitive predicate: FactProver (:lookup) sees only the *direct*
  ;; links, while TransitivePredicateProver (:compute) walks the closure.  So the
  ;; :lookup ceiling gives the direct answer and the :compute ceiling the full reach —
  ;; the middle tier made visible.
  (tu/with-terms [precedes A B C CxFam]
    (v/assert kb (list 'transitive precedes) CxFam)
    (v/assert kb (list precedes A B) CxFam)
    (v/assert kb (list precedes B C) CxFam)
    (let [goal (list precedes A '?y)]
      (testing ":lookup sees the direct link only"
        (is (= #{B} (set (map #(get % '?y)
                              (:results (v/ask-within kb goal CxFam {:max-cost :lookup})))))))
      (testing ":compute walks the transitive closure"
        (is (= #{B C} (set (map #(get % '?y)
                                (:results (v/ask-within kb goal CxFam {:max-cost :compute}))))))))))

(tu/deftest-kb the-lookup-ceiling-keeps-the-closed-world-prover
  ;; `UnknownProver` costs `:compute`, and every other `:compute` member falls out under a
  ;; `:lookup` ceiling.  This one does not, and the asymmetry is what an honest empty rests
  ;; on: dropping a `:compute` prover makes a run *under-report*, which is the trade a
  ;; ceiling asks for, while dropping the closed-world one **inverts** it — an empty result
  ;; for `(unknown S)` reads as "S is derivable" and the run reports `:complete` while
  ;; saying it.  So both directions are pinned here: with the prover dropped, the second
  ;; assertion would read the same and the first would go quietly false.
  (tu/with-terms [flies Tweety CxFam]
    (let [goal (list 'unknown (list flies Tweety))]
      (testing "an underivable argument is unknown, even at the lowest ceiling"
        (let [r (v/ask-within kb goal CxFam {:max-cost :lookup})]
          (is (= :complete (:status r)))
          (is (= [{}] (:results r))
              "an empty answer here would read as (flies Tweety) being derivable")))
      (v/assert kb (list flies Tweety) CxFam)
      (testing "and a derivable one is not, at the same ceiling"
        (is (empty? (:results (v/ask-within kb goal CxFam {:max-cost :lookup}))))))))

;; ---- prove-within -------------------------------------------------------
;; A single-expansion grandparentOf rule (backward-only, so nothing is forward-
;; materialized) gives a clean handle on both the result cap and :max-depth without
;; depending on deep backward recursion.

(defn- grandparent-kb [kb parentOf grandparentOf Tom Bob Ann Zed ctx]
  (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                 (list grandparentOf '?x '?z) ctx {:direction :backward})
  (v/assert kb (list parentOf Tom Bob) ctx)
  (v/assert kb (list parentOf Bob Ann) ctx)
  (v/assert kb (list parentOf Bob Zed) ctx))

(tu/deftest-kb prove-within-generous-budget-matches-prove
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed CxFam]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed CxFam)
    (let [goal (list grandparentOf Tom '?who)
          full (set (map #(get % '?who) (v/prove kb goal CxFam)))
          r    (v/prove-within kb goal CxFam {:max-ms 60000})]
      (is (= #{Ann Zed} full))
      (is (= :complete (:status r)))
      (is (= full (set (map #(get % '?who) (:results r))))))))

(tu/deftest-kb prove-within-caps-and-resumes-to-the-whole-answer
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed CxFam]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed CxFam)
    (let [goal (list grandparentOf Tom '?who)
          full (set (map #(get % '?who) (v/prove kb goal CxFam)))
          r1   (v/prove-within kb goal CxFam {:max-results 1})]
      (is (= #{Ann Zed} full))
      (is (= :capped (:status r1)))
      (is (= 1 (:count r1)))
      (testing "resuming from the saved goal stack covers the whole answer"
        (loop [r r1, acc []]
          (let [acc (into acc (map #(get % '?who) (:results r)))]
            (if (:resume r)
              (recur (v/resume r {:max-results 1}) acc)
              (is (= full (set acc))))))))))

(tu/deftest-kb prove-within-max-depth-bounds-rule-expansion
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed CxFam]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed CxFam)
    (let [goal (list grandparentOf Tom '?who)]
      (testing "depth 0 permits no rule expansion, so a rule-derived goal is empty"
        (let [r (v/prove-within kb goal CxFam {:max-depth 0})]
          (is (= :complete (:status r)))
          (is (empty? (:results r)))))
      (testing "one expansion is enough for grandparentOf"
        (is (= #{Ann Zed}
               (set (map #(get % '?who)
                         (:results (v/prove-within kb goal CxFam {:max-depth 1}))))))))))

(tu/deftest-kb prove-bounds-carries-the-term-growth-ceiling
  (tu/with-terms [p SuccFn A CxRaise]
    ;; (implies (p (SuccFn ?x)) (p ?x)): every expansion wraps one more SuccFn, so the
    ;; stored answer sits twelve levels of *rule-invented* nesting past the query — past
    ;; the shipped allowance, and reachable only by raising it
    ;; backward only: fired forwards the rule would peel the stored term down to
    ;; `(p A)` and store the answer, which is a different question from this one
    (v/assert-rule kb [(list p (list SuccFn '?x))] (list p '?x) CxRaise {:direction :backward})
    (v/assert kb (list p (nth (iterate #(list SuccFn %) A) 12)) CxRaise)
    (let [run (fn [budget]
                (:solutions (res/prove-from kb #(provers/candidate-rules kb % CxRaise)
                                            CxRaise (budget/prove-bounds budget)
                                            (res/initial-prove-stack kb [(list p A)] CxRaise)
                                            [])))]
      (testing "the shipped allowance cuts the branch four levels short of the fact"
        (is (empty? (run nil))))
      (testing "a raised ceiling reaches it"
        (is (= [{}] (run {:max-term-growth 20}))))
      (testing "the other bounds still translate"
        (let [b (budget/prove-bounds {:max-ms 5000 :max-results 3 :max-depth 2})]
          (is (some? (:deadline b)))
          (is (= 3 (:max-results b)))
          (is (= 2 (:max-depth b)))
          (is (nil? (:max-term-growth b)) "unnamed is the default ceiling, not no ceiling")))
      ;; ...and the public entry point reaches `prove-from` through that same translation rather
      ;; than through a bounds map of its own.  The bound is rostered, so `check-budget!`
      ;; admits it — an entry point that then dropped it would answer under the shipped ceiling
      ;; with nothing to say the raise had not been read.
      ;; Under the shipped executor whatever the sweep installed: the claim is about the
      ;; DFS arm's translation, and the node engine takes neither this map nor this bound.
      (testing "prove-within carries it, and builds no bounds map of its own"
        (tu/with-shipped-config
          (is (empty? (:results (v/prove-within kb (list p A) CxRaise nil)))
              "the shipped ceiling, through the public entry point")
          (is (= [{}] (:results (v/prove-within kb (list p A) CxRaise {:max-term-growth 20})))
              "and a raised one reaches the fact the bounds map already reaches"))))))

;; ---- the plain entry points under a bound ----------------------------------------
;; `ask` / `ask?` / `prove` / `provable?` each take a trailing bound of their own, and the
;; two kinds of bound answer differently on purpose: a depth PRUNES, so the answer is the
;; whole of what that depth admits, while a clock SUSPENDS, so what the search holds is a
;; prefix — and a solution vector and a boolean have no room to say so.  These pin both
;; halves, and the second is what stops a deadline from reading as a KB that knows less.

(tu/deftest-kb a-bound-it-runs-dry-inside-answers-what-the-unbounded-entry-point-does
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed CxFam]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed CxFam)
    (let [goal (list grandparentOf Tom '?who)
          who  (fn [ms] (set (map #(get % '?who) ms)))]
      (is (= #{Ann Zed} (who (v/prove kb goal CxFam {:max-ms 60000}))))
      (is (= (who (v/prove kb goal CxFam)) (who (v/prove kb goal CxFam {:max-ms 60000})))
          "a generous bound changes no answer")
      (is (true? (v/provable? kb goal CxFam {:max-ms 60000})))
      (is (= (set (v/ask kb (list parentOf Tom '?y) CxFam))
             (set (v/ask kb (list parentOf Tom '?y) CxFam {:max-ms 60000})))
          "and the registry's answers are the registry's answers")
      (is (true? (v/ask? kb (list parentOf Tom '?y) CxFam {:max-ms 60000}))))))

(tu/deftest-kb a-depth-prunes-so-it-answers-rather-than-refusing
  ;; The space under a depth is genuinely exhausted, so `false` there is a statement about
  ;; derivations within that depth — a question a caller may ask — where `false` under an
  ;; exhausted clock would be a statement about the clock wearing the KB's face.
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed CxFam]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed CxFam)
    (let [goal (list grandparentOf Tom '?who)]
      (is (empty? (v/prove kb goal CxFam {:max-depth 0}))
          "no rule expansion, so a rule-derived goal has nothing")
      (is (false? (v/provable? kb goal CxFam {:max-depth 0}))
          "and the boolean says so rather than refusing")
      (is (= #{Ann Zed} (set (map #(get % '?who) (v/prove kb goal CxFam {:max-depth 1}))))
          "one expansion is enough, and the answer is complete for that depth"))))

(tu/deftest-kb an-exhausted-clock-is-a-refusal-and-never-a-short-answer
  ;; `{:max-ms 0}` is a deadline already past, so the search stops at its first bound check
  ;; whatever the box is doing — the honest reading of "no time at all", and the only
  ;; spelling of this that reads the same on an idle box and under a dozen JVMs.
  (tu/with-terms [p SuccFn A CxLoop]
    ;; a rule whose every expansion wraps one more term around its subgoal, so it asks a
    ;; fresh goal each time: a search that runs until a guard stops it rather than until
    ;; the data does, which is what a bound on these entry points is for
    (v/assert-rule kb [(list p (list SuccFn '?x))] (list p '?x) CxLoop {:direction :backward})
    (v/assert kb (list p A) CxLoop)
    (let [goal (list p A)]
      (doseq [[entry-point run] [["prove"     #(v/prove kb goal CxLoop {:max-ms 0})]
                                 ["provable?" #(v/provable? kb goal CxLoop {:max-ms 0})]
                                 ["ask"       #(v/ask kb goal CxLoop {:max-ms 0})]
                                 ["ask?"      #(v/ask? kb goal CxLoop {:max-ms 0})]]]
        (let [d (ex-data (is (thrown? clojure.lang.ExceptionInfo (run))))]
          (is (= :budget-exhausted (:type d))
              (str entry-point " refused rather than answering off a prefix"))
          (is (= [entry-point :timeout] [(:entry-point d) (:status d)])
              "naming the entry point that ran out and what stopped it"))))))

(tu/deftest-kb each-bounded-entry-point-reads-its-own-roster
  (tu/with-terms [dog Muffet CxRoster]
    (v/assert kb (list dog Muffet) CxRoster)
    (let [goal    (list dog '?x)
          refusal (fn [f] (:type (ex-data (is (thrown? clojure.lang.ExceptionInfo (f))))))]
      (testing "a misspelt bound is refused rather than run unbounded"
        (is (= [:unknown-option :unknown-option :unknown-option :unknown-option]
               [(refusal #(v/prove kb goal CxRoster {:max-mss 10}))
                (refusal #(v/provable? kb goal CxRoster {:max-mss 10}))
                (refusal #(v/ask kb goal CxRoster {:max-mss 10}))
                (refusal #(v/ask? kb goal CxRoster {:max-mss 10}))])))
      (testing "a depth is prove's and not ask's — nothing in the registry expands a
                rule, so a depth there would be a bound accepted and never consulted"
        (is (= :unknown-option (refusal #(v/ask kb goal CxRoster {:max-depth 1}))))
        (is (= :unknown-option (refusal #(v/ask? kb goal CxRoster {:max-depth 1}))))
        (is (= #{Muffet} (set (map #(get % '?x)
                                   (v/prove kb goal CxRoster {:max-depth 1}))))))
      (testing "and a bound that is not the kind of number it names, since one that is
                not reads as no bound at all"
        (is (= :unknown-option (refusal #(v/prove kb goal CxRoster {:max-depth -1}))))
        (is (= :unknown-option (refusal #(v/ask kb goal CxRoster {:max-ms :soon}))))))))

;; ---- the budget roster ----------------------------------------------------

(deftest a-budget-bound-nothing-reads-is-refused
  ;; Every bound is optional, so a misspelt one is not missing — the run is simply
  ;; unbounded: `{:max-mss 100}` realizes the whole stream, which on an infinite
  ;; source never returns.  (`:max-cost` outside the tiers is the *value* check and
  ;; stays `:unknown-option` at the prover entry point; this is the key check one level up.)
  (testing "collect refuses the typo before realizing anything"
    (let [pulled (atom 0)
          src    (map (fn [i] (swap! pulled inc) i) (range))
          e      (is (thrown? clojure.lang.ExceptionInfo
                              (budget/collect src {:max-mss 100})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= [:max-mss] (:unknown (ex-data e))))
      (is (re-find #":max-ms" (ex-message e)) "the right spelling is in the message")
      (is (zero? @pulled) "nothing was realized on the way to the refusal")))
  (testing "a non-map budget is refused rather than read as unbounded"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map"
                          (budget/collect (range 5) :max-results))))
  (testing "each anytime entry point's own rostered bounds pass — ask's three and prove's four"
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog Muffet CxBudget]
        (v/assert kb (list dog Muffet) CxBudget)
        (is (= :complete (:status (v/ask-within kb (list dog '?x) CxBudget
                                                {:max-ms 5000 :max-results 10
                                                 :max-cost :search}))))
        (is (= :complete (:status (v/prove-within kb (list dog '?x) CxBudget
                                                  {:max-results 10 :max-depth 3
                                                   :max-term-growth 40})))))))
  (testing "and both anytime entry points hold their budget to the roster"
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog]
        (doseq [entry-point [#(v/ask-within kb (list dog '?x) {:max-result 1})
                             #(v/prove-within kb (list dog '?x) {:max-result 1})]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (entry-point)))]
            (is (= :unknown-option (:type (ex-data e))))
            (is (= [:max-result] (:unknown (ex-data e))))))))))
