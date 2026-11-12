;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.query-status-test
  "`query-status` — `query`'s answers plus a report of the run.

  The report exists for one silent failure `:max-depth` otherwise has: a query truncated
  at the depth bound returns the same empty (or short) seq as a query whose goal is
  genuinely unprovable, so a bound one too low reads as \"no\" rather than \"not deep
  enough.\"  The tests below hold the distinction — a too-shallow bound is `:truncated?`
  where an unprovable goal at a sufficient bound is not — and check the timings and the
  context refusal that come with it.

  `:truncated?` is conservative: it fires when the bound stopped any rewrite, which for a
  cyclic rule set is every bound (the search always has one deeper level to refuse), and
  which for a fixed-depth rule chain clears exactly when the bound is deep enough.  Both
  are asserted; the fixed-depth case is the empire-eligibility shape the prompt names."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; A fixed-depth rule chain, the empire-eligibility shape: `eligible` wraps `canAct`,
;; which is concluded from a base fact.  So `(eligible U)` needs two rewrites, and a
;; :max-depth 1 tuned for the direct `canAct` rule is one too low for the wrapped one.
(defn- eligibility-kb [kb canAct eligible baseCan U1 CxE]
  (v/assert kb (list baseCan U1) CxE)
  (v/assert-rule kb [(list baseCan '?u)] (list canAct '?u) CxE {:direction :backward})
  (v/assert-rule kb [(list canAct '?u)] (list eligible '?u) CxE {:direction :backward}))

(tu/deftest-kb a-too-shallow-bound-is-distinguishable-from-an-unprovable-goal
  (tu/with-terms [canAct eligible baseCan U1 U2 CxE]
    (eligibility-kb kb canAct eligible baseCan U1 CxE)
    (let [goal (list eligible '?u)]
      (testing "one level too shallow: no answer, and the report says the bound cut it"
        (let [r (v/query-status kb goal CxE {:max-depth 1})]
          (is (= [] (:answers r)))
          (is (= 0 (:count r)))
          (is (:truncated? r) "the wrapped rule's `canAct` antecedent hit depth 0 unrewritten")
          (is (= :truncated (:status r)))
          (is (= 1 (:depth r)))))
      (testing "deep enough: the answer appears and the bound no longer cuts"
        (let [r (v/query-status kb goal CxE {:max-depth 2})]
          (is (= #{U1} (into #{} (map #(get % '?u)) (:answers r))))
          (is (= 1 (:count r)))
          (is (not (:truncated? r)) "the leaves are base facts no rule concludes")
          (is (= :complete (:status r)))))
      (testing "genuinely unprovable at a sufficient bound: empty AND not truncated —"
        ;; the reading the bare seq cannot give.  U2 has no base fact, so no depth reaches
        ;; it; at depth 2 its `canAct`/`baseCan` leaves are answered (as nothing) rather
        ;; than cut, which is what separates \"no\" from \"not deep enough.\"
        (let [r (v/query-status kb (list eligible U2) CxE {:max-depth 2})]
          (is (= [] (:answers r)))
          (is (not (:truncated? r)))
          (is (= :complete (:status r)))))
      (testing "and the too-shallow read of the unprovable goal is truncated, like any"
        (let [r (v/query-status kb (list eligible U2) CxE {:max-depth 1})]
          (is (= [] (:answers r)))
          (is (:truncated? r)))))))

(tu/deftest-kb a-cyclic-rule-set-terminates-and-reports-its-truncation
  ;; The bound is a real safety limit over a cyclic rule graph, and the report is the
  ;; other half of the prompt's requirement: the cut is reported rather than silently
  ;; swallowed.  A cyclic set always has one deeper level the bound refuses, so it is
  ;; truncated at every depth — which is the correct answer for a search a bound, not the
  ;; data, terminated.
  (tu/with-terms [edge reach A B CxC]
    (v/assert kb (list edge A B) CxC)
    (v/assert kb (list edge B A) CxC)
    (v/assert-rule kb [(list edge '?x '?y)] (list reach '?x '?y) CxC {:direction :backward})
    (v/assert-rule kb [(list edge '?x '?y) (list reach '?y '?z)] (list reach '?x '?z)
                   CxC {:direction :backward})
    (let [r (v/query-status kb (list reach A '?z) CxC {:max-depth 5})]
      (testing "it terminates under the bound and hands back finite answers"
        (is (= #{A B} (into #{} (map #(get % '?z)) (:answers r)))
            "A reaches B directly and A through the cycle"))
      (testing "and reports the cut"
        (is (:truncated? r))
        (is (= :truncated (:status r)))))))

(tu/deftest-kb a-facts-only-read-is-complete-and-never-truncated
  ;; No depth, or `:max-depth 0`, is a complete answer to its own question — the registry
  ;; alone, expanding no rule — so a depth never cut it and the report says so.  The
  ;; `stats` map is the node engine's, so a facts-only read carries none.
  (tu/with-terms [canAct eligible baseCan U1 CxE]
    (eligibility-kb kb canAct eligible baseCan U1 CxE)
    (let [r (v/query-status kb (list baseCan '?u) CxE {:max-depth 0})]
      (is (= #{U1} (into #{} (map #(get % '?u)) (:answers r))))
      (is (not (:truncated? r)))
      (is (= :complete (:status r)))
      (is (= 0 (:depth r)))
      (is (not (contains? r :stats)) "no node engine ran, so no node-engine counters"))))

(tu/deftest-kb the-report-times-the-run-and-counts-the-search
  (tu/with-terms [canAct eligible baseCan U1 CxE]
    (eligibility-kb kb canAct eligible baseCan U1 CxE)
    (testing "an answered read: a first-answer time and a total, and the node counters"
      (let [r (v/query-status kb (list eligible '?u) CxE {:max-depth 2})]
        (is (number? (:total-time-ms r)))
        (is (<= 0.0 (double (:total-time-ms r))))
        (is (number? (:time-to-first-answer-ms r)) "there is an answer, so there is a first")
        (is (map? (:stats r)))
        (is (pos? (:expanded (:stats r))) "the node engine expanded at least the root")
        (is (contains? (:stats r) :nodes))
        (is (contains? (:stats r) :frontier))))
    (testing "an empty read still times, and the first-answer time is nil"
      (let [r (v/query-status kb (list eligible '?u) CxE {:max-depth 1})]
        (is (number? (:total-time-ms r)))
        (is (nil? (:time-to-first-answer-ms r)) "no answer, so no first-answer time")))))

(tu/deftest-kb a-report-answers-exactly-what-query-answers
  ;; The report is `query` with a status stapled on, not a second engine: the same depth
  ;; resolution, the same rules, the same answer set.  Truncation tracking is a read of
  ;; the search, so it moves no answer.
  (tu/with-terms [canAct eligible baseCan U1 U2 CxE]
    (eligibility-kb kb canAct eligible baseCan U1 CxE)
    (v/assert kb (list baseCan U2) CxE)
    (let [goal (list eligible '?u)
          as-set #(into #{} (map (fn [s] (get s '?u))) %)]
      (doseq [d [0 1 2 3]]
        (is (= (as-set (v/query kb goal CxE {:max-depth d}))
               (as-set (:answers (v/query-status kb goal CxE {:max-depth d}))))
            (str "answers disagree at depth " d))))))

(tu/deftest-kb a-report-runs-in-one-concrete-context
  ;; A report is one search over one frontier, so a fanned read — a variable context, or
  ;; a query context — has no single frontier to report truncation off and is refused.
  (tu/with-terms [canAct eligible baseCan U1 CxE]
    (eligibility-kb kb canAct eligible baseCan U1 CxE)
    (let [goal    (list eligible '?u)
          refusal (fn [ctx] (try (v/query-status kb goal ctx {:max-depth 2}) nil
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (testing "a variable context is refused"
        (is (= :unsupported-context (:type (refusal '?ctx)))))
      (testing "and a query context is refused"
        (doseq [qc '[CxEverything CxInference CxNothing]]
          (is (= :unsupported-context (:type (refusal qc))) (str qc))))
      (testing "a concrete context answers"
        (is (= #{U1} (into #{} (map #(get % '?u)) (:answers (v/query-status kb goal CxE
                                                                            {:max-depth 2})))))))))

(tu/deftest-kb an-open-transitive-goal-reports-the-closure-it-did-not-enumerate
  ;; `(P ?x ?y)` over a transitive `P` answers the extent, so the two-hop `(R0 R2)` is
  ;; missing, and the report names `P` and reads `:incomplete`.
  (tu/with-terms [typeLargerThan biggerThan R0 R1 R2 CxT]
    (v/assert kb (list 'transitive typeLargerThan) CxT)
    (v/assert kb (list typeLargerThan R0 R1) CxT)
    (v/assert kb (list typeLargerThan R1 R2) CxT)
    (testing "both ends open: the extent, marked incomplete, at a depth and facts-only"
      (doseq [opts [{:max-depth 1} {:max-depth 0} nil]]
        (let [r (v/query-status kb (list typeLargerThan '?x '?y) CxT opts)]
          (is (= 2 (:count r)))
          (is (= [typeLargerThan] (:unenumerated r)))
          (is (= :incomplete (:status r)))
          (is (not (:truncated? r))))))
    (testing "one end bound: the closure, complete"
      (let [r (v/query-status kb (list typeLargerThan R0 '?y) CxT {:max-depth 1})]
        (is (= #{R1 R2} (into #{} (map #(get % '?y)) (:answers r))))
        (is (= [] (:unenumerated r)))
        (is (= :complete (:status r)))))
    (testing "a rule antecedent solved with both ends open"
      (v/assert-rule kb [(list typeLargerThan '?x '?y)] (list biggerThan '?x '?y) CxT
                     {:direction :backward})
      (let [r (v/query-status kb (list biggerThan '?x '?y) CxT {:max-depth 1})]
        (is (= [typeLargerThan] (:unenumerated r)))
        (is (= :incomplete (:status r)))))
    (testing "search-tree names it as well"
      (is (= [typeLargerThan]
             (:unenumerated (v/search-tree kb (list typeLargerThan '?x '?y) CxT
                                           {:max-depth 1})))))))

(tu/deftest-kb compare-tacticians-reads-incomplete-on-every-row-over-an-open-transitive-goal
  (tu/with-terms [typeLargerThan R0 R1 R2 CxT]
    (v/assert kb (list 'transitive typeLargerThan) CxT)
    (v/assert kb (list typeLargerThan R0 R1) CxT)
    (v/assert kb (list typeLargerThan R1 R2) CxT)
    (let [rows (v/compare-tacticians kb (list typeLargerThan '?x '?y) CxT {:max-depth 1})]
      (is (= #{:incomplete} (set (map :status rows))))
      (is (= #{[typeLargerThan]} (set (map :unenumerated rows))))
      (is (= 1 (count (set (map :answers rows))))))
    (testing "one end bound: every row complete"
      (let [rows (v/compare-tacticians kb (list typeLargerThan R0 '?y) CxT {:max-depth 1})]
        (is (= #{:complete} (set (map :status rows))))
        (is (= #{[]} (set (map :unenumerated rows))))))))

;; ---- a both-open transitive goal inside an evaluation ----------------------------
;; The join plans `(aheadOf ?x ?y)` before `(start ?x)` and `(finish ?y)`, so it is solved
;; with both ends open and the closure pair (R0 R2) the body needs is missed.  Under
;; `thereExists` that loses the answer; under `unknown` and `exceptWhen` it admits one the
;; closure refutes, and the predicate is named in `:unenumerated-in-guards` as well.
;; A stored exception's conjunction is canonicalized, which sorts `(start ?x)` and
;; `(finish ?y)` ahead of `aheadOf`, so the exception's body filters the pair with
;; `different` instead: a deferred test follows the generators however it is written, and
;; R0 R2 is the one pair that avoids R1.

(defn- open-pair-kb [kb aheadOf start finish R0 R1 R2 CxT]
  (v/assert kb (list 'transitive aheadOf) CxT)
  (v/assert kb (list aheadOf R0 R1) CxT)
  (v/assert kb (list aheadOf R1 R2) CxT)
  (v/assert kb (list start R0) CxT)
  (v/assert kb (list finish R2) CxT)
  (list 'thereExists '[?x ?y] (list 'and (list aheadOf '?x '?y) (list start '?x) (list finish '?y))))

(defn- unenumerated-keys [r] (select-keys r [:status :unenumerated :unenumerated-in-guards]))

(tu/deftest-kb an-open-transitive-goal-under-there-exists-loses-the-answer-and-reads-incomplete
  (tu/with-terms [aheadOf start finish R0 R1 R2 CxT]
    (let [body (open-pair-kb kb aheadOf start finish R0 R1 R2 CxT)
          want {:status :incomplete :unenumerated [aheadOf] :unenumerated-in-guards []}]
      (is (= want (unenumerated-keys (v/query-status kb body CxT {:max-depth 1}))))
      (let [r (v/ask-within kb body CxT {:max-ms 60000})]
        (is (= [] (:results r)))
        (is (= want (unenumerated-keys r)))))))

(tu/deftest-kb an-open-transitive-goal-under-unknown-admits-the-answer-and-names-a-guard
  (tu/with-terms [aheadOf start finish R0 R1 R2 CxT]
    (let [goal (list 'unknown (open-pair-kb kb aheadOf start finish R0 R1 R2 CxT))
          want {:status :incomplete :unenumerated [aheadOf] :unenumerated-in-guards [aheadOf]}]
      (is (= want (unenumerated-keys (v/query-status kb goal CxT {:max-depth 1}))))
      (let [r (v/ask-within kb goal CxT {:max-ms 60000})]
        (is (= [{}] (:results r)))
        (is (= want (unenumerated-keys r)))))))

(tu/deftest-kb an-open-transitive-goal-in-an-exception-admits-the-answer-and-names-a-guard
  (tu/with-terms [aheadOf start finish mark flagged R0 R1 R2 Z CxT]
    (open-pair-kb kb aheadOf start finish R0 R1 R2 CxT)
    (let [ex   (list 'thereExists '[?x ?y] (list 'and (list 'different '?y R1) (list 'different '?x R1)
                                                 (list aheadOf '?x '?y)))
          goal (list flagged '?z)
          want {:status :incomplete :unenumerated [aheadOf] :unenumerated-in-guards [aheadOf]}]
      (v/assert kb (list 'exceptWhen ex (list 'implies (list mark '?z) (list flagged '?z))) CxT
                {:direction :backward})
      (v/assert kb (list mark Z) CxT)
      (let [r (v/query-status kb goal CxT {:max-depth 1})]
        (is (= [{'?z Z}] (:answers r)))
        (is (= want (unenumerated-keys r))))
      (binding [v/*query-engine* :dfs]
        (is (= want (unenumerated-keys (v/prove-within kb goal CxT {:max-depth 1}))))))))
