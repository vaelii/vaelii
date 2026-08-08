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
    * `:max-depth` prunes the DFS's rule expansion."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the pure collector (no KB) -----------------------------------------

(deftest collect-unbounded-runs-dry
  (let [r (budget/collect (range 5) nil)]
    (is (= [0 1 2 3 4] (:results r)))
    (is (= :complete (:status r)))
    (is (= 5 (:count r)))
    (is (nil? (:resume r)))
    (is (<= 0 (:elapsed-ms r)))))

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
  (tu/with-terms [parentOf Tom Bob Ann Zed FamContext]
    (v/assert kb (list parentOf Tom Bob) FamContext)
    (v/assert kb (list parentOf Tom Ann) FamContext)
    (v/assert kb (list parentOf Tom Zed) FamContext)
    (let [goal (list parentOf Tom '?y)
          full (set (map #(get % '?y) (v/ask kb goal FamContext)))
          r    (v/ask-within kb goal FamContext {:max-ms 60000})]
      (is (= :complete (:status r)))
      (is (= #{Bob Ann Zed} full))
      (is (= full (set (map #(get % '?y) (:results r))))))))

(tu/deftest-kb ask-within-caps-and-resumes-to-the-whole-answer
  (tu/with-terms [parentOf Tom Bob Ann Zed FamContext]
    (v/assert kb (list parentOf Tom Bob) FamContext)
    (v/assert kb (list parentOf Tom Ann) FamContext)
    (v/assert kb (list parentOf Tom Zed) FamContext)
    (let [goal (list parentOf Tom '?y)
          full (set (map #(get % '?y) (v/ask kb goal FamContext)))
          r1   (v/ask-within kb goal FamContext {:max-results 1})]
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
  (tu/with-terms [reachable Tom Ann FamContext]
    (let [costly (reify provers/Prover
                   (applicable?  [_ _ goal _] (= reachable (first goal)))
                   (est-bindings [_ _ _ _] 1)
                   (cost         [_ _ _ _] :search)
                   (completeness [_ _ _ _] 50)
                   (solve        [_ _ _ _] [{'?who Ann}]))]
      (v/add-prover kb costly)
      (let [goal (list reachable Tom '?who)]
        (testing "at :lookup the search tier is excluded, so no answer"
          (let [r (v/ask-within kb goal FamContext {:max-cost :lookup})]
            (is (= :complete (:status r)))
            (is (empty? (:results r)))))
        (testing "raising the ceiling to :search lets it run"
          (let [r (v/ask-within kb goal FamContext {:max-cost :search})]
            (is (= #{Ann} (set (map #(get % '?who) (:results r)))))))))))

(tu/deftest-kb a-ceiling-that-is-not-a-tier-is-refused
  ;; The mistake is invisible in the result — a ceiling that admits everything returns
  ;; exactly the answers a correct one would, only having done the work the bound
  ;; existed to avoid.  So a `:max-cost` outside the three tiers has to say so, and
  ;; carry a `:type` a caller can discriminate on rather than an NPE from inside a
  ;; comparison.
  (tu/with-terms [partOf A B D FamContext]
    (v/assert kb (list 'transitive partOf) FamContext)
    (v/assert kb (list partOf A B) FamContext)
    (v/assert kb (list partOf B D) FamContext)
    (let [goal (list partOf A '?y)]
      (testing "a real tier answers"
        (is (= :complete (:status (v/ask-within kb goal FamContext {:max-cost :compute})))))
      (doseq [bogus [:Lookup :cheap :lookups "lookup"]]
        (testing (str "a ceiling of " (pr-str bogus) " is refused, with the tiers named")
          (let [e (try (v/ask-within kb goal FamContext {:max-cost bogus})
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
  (tu/with-terms [precedes A B C FamContext]
    (v/assert kb (list 'transitive precedes) FamContext)
    (v/assert kb (list precedes A B) FamContext)
    (v/assert kb (list precedes B C) FamContext)
    (let [goal (list precedes A '?y)]
      (testing ":lookup sees the direct link only"
        (is (= #{B} (set (map #(get % '?y)
                              (:results (v/ask-within kb goal FamContext {:max-cost :lookup})))))))
      (testing ":compute walks the transitive closure"
        (is (= #{B C} (set (map #(get % '?y)
                                (:results (v/ask-within kb goal FamContext {:max-cost :compute}))))))))))

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
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed FamContext]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed FamContext)
    (let [goal (list grandparentOf Tom '?who)
          full (set (map #(get % '?who) (v/prove kb goal FamContext)))
          r    (v/prove-within kb goal FamContext {:max-ms 60000})]
      (is (= #{Ann Zed} full))
      (is (= :complete (:status r)))
      (is (= full (set (map #(get % '?who) (:results r))))))))

(tu/deftest-kb prove-within-caps-and-resumes-to-the-whole-answer
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed FamContext]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed FamContext)
    (let [goal (list grandparentOf Tom '?who)
          full (set (map #(get % '?who) (v/prove kb goal FamContext)))
          r1   (v/prove-within kb goal FamContext {:max-results 1})]
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
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann Zed FamContext]
    (grandparent-kb kb parentOf grandparentOf Tom Bob Ann Zed FamContext)
    (let [goal (list grandparentOf Tom '?who)]
      (testing "depth 0 permits no rule expansion, so a rule-derived goal is empty"
        (let [r (v/prove-within kb goal FamContext {:max-depth 0})]
          (is (= :complete (:status r)))
          (is (empty? (:results r)))))
      (testing "one expansion is enough for grandparentOf"
        (is (= #{Ann Zed}
               (set (map #(get % '?who)
                         (:results (v/prove-within kb goal FamContext {:max-depth 1}))))))))))

;; ---- the budget roster ----------------------------------------------------

(deftest a-budget-bound-nothing-reads-is-refused
  ;; Every bound is optional, so a misspelt one is not missing — the run is simply
  ;; unbounded: `{:max-mss 100}` realizes the whole stream, which on an infinite
  ;; source never returns.  (`:max-cost` outside the tiers is the *value* check and
  ;; stays `:unknown-option` at the prover door; this is the key check one level up.)
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
    ;; The keyword is the point — the refusal is what this asserts — so the
    ;; type mismatch clj-kondo sees is the test's subject, not a defect.
    #_{:clj-kondo/ignore [:type-mismatch]}
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map"
                          (budget/collect (range 5) :max-results))))
  (testing "the four rostered bounds all pass at every door"
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog Muffet BudgetContext]
        (v/assert kb (list dog Muffet) BudgetContext)
        (is (= :complete (:status (v/ask-within kb (list dog '?x) BudgetContext
                                                {:max-ms 5000 :max-results 10
                                                 :max-cost :search}))))
        (is (= :complete (:status (v/prove-within kb (list dog '?x) BudgetContext
                                                  {:max-results 10 :max-depth 3})))))))
  (testing "and both anytime doors hold their budget to the roster"
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog]
        (doseq [door [#(v/ask-within kb (list dog '?x) {:max-result 1})
                      #(v/prove-within kb (list dog '?x) {:max-result 1})]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (door)))]
            (is (= :unknown-option (:type (ex-data e))))
            (is (= [:max-result] (:unknown (ex-data e))))))))))
