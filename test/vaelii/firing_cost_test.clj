;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.firing-cost-test
  "What one forward firing costs the index **at the trigger position**, as counted reads.

  Three counted gates stood beside this one and none of them was about a firing.
  `assert_cost_test` prices the *assert* path and reaches chaining only through one
  workload whose rule has a single antecedent — so `chain/*matcher*` was never on its
  path at all, which is how the join went four years without a pin.  `join_lead_cost_test`
  and `lead_side_cost_test` hold *shapes* — flat against growing — and a shape says
  nothing about the constant beside it.  A read added to `fire-rules-for`, to
  `complete-antecedents`, or to `derive-conclusion` lands in none of the three.

  So this is the constant, for four firings that reach the trigger four different ways:

  - **`:single-antecedent`** — no join at all.  The floor: what a rule costs when the
    datum satisfies the whole antecedent list on its own.
  - **`:unfanned-join`** — a second antecedent whose functor has no sub-predicates.  The
    overwhelmingly common join, and the one `chain/join-matches` must answer through the
    trie: `res/match-pattern` fast-paths a singleton spec closure to a single `raw-match`,
    where the argument lead pays `matches-hierarchical`'s apparatus for a fan that is not
    there.  Measured over 2,000 firings, the lead cost 52,003 index reads against the
    trie's 48,003 for the same 2,000 conclusions.
  - **`:fanned-join`** — the same join over a functor with four sub-predicates, where the
    lead **is** the cheaper read and is taken.  The pair is what separates \"the lead is
    off\" from \"the lead is off everywhere\": a gate that lost the fanned case would pass
    with the argument lead deleted.
  - **`:symmetric-trigger`** — a firing whose trigger antecedent is symmetric, reached
    **only** through the datum's mirror.  `chain/symmetric-mirror` reads the fact's own
    `symmetric` declaration once per datum and `chain/trigger-bindings` tries both
    orientations at every position, which is what keeps a symmetric antecedent reading the
    same at the trigger as it does at a join — and with it the run's independence from
    arrival order.  The workload is built so the un-mirrored binding satisfies nothing:
    lose the mirror and the conclusion count goes to zero, which fails before any budget
    does.

  ## Why a count, and why exact

  `assert_cost_test`'s reasons, unchanged: an integer the engine computes rather than a
  measurement of the machine — no warm-up, no tolerance, identical on a loaded box — and
  exact rather than a ceiling, so a legitimate improvement fails this gate and is re-pinned
  by the commit that earns it, carrying its own size as data.

  ## What it does not catch

  - **Work that is not an index read.**  A taxonomy walk, an allocation, a record fetch.
    The counted calls are `IndexStore`'s; `record_fetch_cost_test` is the record-store half.
  - **A more expensive version of the same read.**  One `sentexes-with-arg` counts once
    whether it returns four handles or four million; `lein perf` holds that.
  - **Anything that scales.**  A cost growing with the KB is a ratio's subject, and
    `join_lead_cost_test` is the shape gate for these same calls.
  - **A configuration other than the shipped one**, and a backend other than `:memory`."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.profile :as prof]
            [vaelii.test-util :as tu]))

;; the instrument is process-wide, so a test that threw while collecting would hand the
;; next namespace a running tally
(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(def ^:private n
  "Firings per workload — one per trigger datum, and every workload concludes exactly
  this many."
  100)

(def ^:private firing-space
  "The KB every workload runs on: in-RAM, its own space, the reference TMS.  Pinned for
  `assert_cost_test`'s reasons — the **backend**, because the columnar store keeps its own
  tallies and a budget is a claim about one index; the **TMS**, because a budget is a claim
  about one configuration and `VAELII_TEST_TMS=dense` is a different one."
  (-> tu/plain-memory-space
      (update :space conj ::firing)
      (assoc :tms :reference)))

(defn- fresh [] (doto (v/open-kb firing-space) (tu/clear-kb!)))

(defn- ind [prefix i] (symbol (str prefix i)))

;; ---- the workloads -------------------------------------------------------
;;
;; Each returns `[kb trigger-handles conclusion-functor]`.  Everything loads with
;; `:chain? false`, so the whole corpus and the rule are in place before the instrument
;; starts and the one chaining run over the trigger set is all that is measured.

(defn- single-antecedent
  "One antecedent, satisfied by the datum itself — no join runs."
  []
  (let [kb (fresh)]
    (v/assert-rule kb ['(fc_one ?x)] '(fc_concl_a ?x) 'CxPerf
                   {:direction :forward :chain? false})
    [kb
     (mapv (fn [i] (v/assert kb (list 'fc_one (ind "FcO" i)) 'CxPerf
                             {:strength :monotonic :chain? false}))
           (range n))
     'fc_concl_a]))

(defn- unfanned-join
  "A join antecedent `(fcFn ?x ?y)` with `?x` bound and `fcFn` holding no sub-predicates —
  the case `join-matches` answers through the trie."
  []
  (let [kb (fresh)]
    (v/assert-rule kb ['(fc_trig ?x) '(fcFn ?x ?y)] '(fcConclB ?x ?y) 'CxPerf
                   {:direction :forward :chain? false})
    (dotimes [i n]
      (v/assert kb (list 'fcFn (ind "FcA" i) (ind "FcB" i)) 'CxPerf
                {:strength :monotonic :chain? false}))
    [kb
     (mapv (fn [i] (v/assert kb (list 'fc_trig (ind "FcA" i)) 'CxPerf
                             {:strength :monotonic :chain? false}))
           (range n))
     'fcConclB]))

(defn- fanned-join
  "The same join over `fcBroad`, which has four sub-predicates — so the trie would walk
  five times to confirm one membership and the argument lead is taken instead.  The facts
  are stated at a sub-predicate, so the fan is real and not a formality."
  []
  (let [kb (fresh)]
    (dotimes [i 4]
      (v/assert kb (list 'genl (symbol (str "fcSub" i)) 'fcBroad) 'CxPerf
                {:strength :monotonic}))
    (v/assert-rule kb ['(fc_trig ?x) '(fcBroad ?x ?y)] '(fcConclC ?x ?y) 'CxPerf
                   {:direction :forward :chain? false})
    (dotimes [i n]
      (v/assert kb (list 'fcSub0 (ind "FcA" i) (ind "FcB" i)) 'CxPerf
                {:strength :monotonic :chain? false}))
    [kb
     (mapv (fn [i] (v/assert kb (list 'fc_trig (ind "FcA" i)) 'CxPerf
                             {:strength :monotonic :chain? false}))
           (range n))
     'fcConclC]))

(defn- symmetric-trigger
  "A firing reachable **only** through the trigger datum's symmetric mirror.

  `fcSib` is declared symmetric, so `(fcSib FcAi FcBi)` is stored in the canonical
  argument order and *means* both.  The rule's second antecedent asks `(fc_ok ?y)`, and
  `fc_ok` holds of the `FcA` side alone — so the datum's own binding (`?y = FcBi`)
  satisfies nothing and the mirror's (`?y = FcAi`) is the one that fires.  Every
  conclusion here is `(fcConclD FcBi FcAi)`, arguments the other way round from the fact
  that produced it, which is the whole of the claim."
  []
  (let [kb (fresh)]
    (v/assert kb '(symmetric fcSib) 'CxPerf {:strength :monotonic})
    (v/assert-rule kb ['(fcSib ?x ?y) '(fc_ok ?y)] '(fcConclD ?x ?y) 'CxPerf
                   {:direction :forward :chain? false})
    (dotimes [i n]
      (v/assert kb (list 'fc_ok (ind "FcA" i)) 'CxPerf
                {:strength :monotonic :chain? false}))
    [kb
     (mapv (fn [i] (v/assert kb (list 'fcSib (ind "FcA" i) (ind "FcB" i)) 'CxPerf
                             {:strength :monotonic :chain? false}))
           (range n))
     'fcConclD]))

;; ---- the budgets ---------------------------------------------------------
;;
;; Measured, not designed, at `n` = 100 firings.  A family is **absent rather than pinned
;; at 0**, which is the stronger claim: a family the workload never reads is a key the
;; tally never emits, so one read of it fails the budget.
;;
;; Measured under the shipped default (`with-entailing` in `measure`), so `:functor-root`
;; carries the entailment's per-firing declaration lookup — 100 reads over the 100 firings
;; that a `VAELII_ASSERTIVE_ARG_TYPES=0` run does not spend.  Pinned on so the number is the
;; same whatever the root is set to.
;;
;; `:trie-lookup` is where the two join workloads part, and it is the reading to take them
;; by.  The unfanned join walks the trie once per firing (100) and the fanned one never
;; touches it, leading from the bound term's postings instead — which costs the two extra
;; `:argument-root` and `:argument-slot` reads per firing that separate their budgets.
;; Those are the same reads a *singleton* closure would spend on a fan that is not there,
;; which is why `:unfanned-join` reads 100/100 against `:fanned-join`'s 300/300.

(def ^:private budgets
  [{:name :single-antecedent
    :build single-antecedent
    :reads {:argument-root 200 :argument-slot 200 :exception-index 200
            :functor-root 301 :rule-index 200 :trie-counts 100}}

   {:name :unfanned-join
    :build unfanned-join
    :reads {:argument-root 100 :argument-slot 100 :exception-index 200
            :functor-root 303 :rule-index 200 :trie-counts 100 :trie-lookup 100}}

   {:name :fanned-join
    :build fanned-join
    :reads {:argument-root 300 :argument-slot 300 :exception-index 200
            :functor-root 303 :rule-index 200 :trie-counts 100}}

   ;; two `:trie-lookup` per firing, not one: the mirror is a second orientation to look
   ;; the conclusion's own handle up under, and both orientations reach `join-matches`
   {:name :symmetric-trigger
    :build symmetric-trigger
    :reads {:argument-root 100 :argument-slot 100 :exception-index 200
            :functor-root 303 :rule-index 200 :trie-counts 100 :trie-lookup 200}}])

;; ---- measuring -----------------------------------------------------------

(defn- measure
  "Build one workload, then chain its trigger set under the instrument.  The corpus is
  laid down outside the reading and inside the pinned configuration: a taxonomy built
  under one reader and priced under another would be a workload nobody runs."
  [build]
  (tu/with-shipped-config
    (tu/with-entailing                              ; the shipped default; budgets below are on-path
      (let [[kb trigs concl] (build)
            _    (prof/start)
            _    (chain/chain kb trigs nil)
            snap (prof/stop)]
        {:reads     (into {} (:reads snap))
         :concluded (count (v/sentexes-with-functor kb concl))
         :sentences (into #{} (map :sentence) (v/sentexes-with-functor kb concl))}))))

(defn- delta-report
  "The families whose count moved, as a table.  Every family either side names is listed,
  so one that appeared from nowhere reads as `0 -> 100` rather than going missing."
  [expected actual]
  (->> (sort (into (set (keys expected)) (keys actual)))
       (keep (fn [k]
               (let [e (get expected k 0), a (get actual k 0)]
                 (when (not= e a)
                   (format "    %-16s %6d -> %-6d  (%+d)" (name k) e a (- a e))))))
       (str/join "\n")))

(deftest firing-cost-is-what-it-was
  (doseq [{:keys [name build reads]} budgets]
    (testing (str "the " (clojure.core/name name) " workload")
      (let [got (measure build)]
        ;; the conclusion count first: a budget compared against a different number of
        ;; firings is comparing two workloads, and it is the assertion the symmetric
        ;; workload fails on if the mirror stops reaching the rule
        (is (= n (:concluded got))
            (str (clojure.core/name name) ": the workload fired a different number of "
                 "times, so its budget is about something else now"))
        (is (= reads (:reads got))
            (format (str "%s: the firing read budget moved.\n%s\n"
                         "  If this change is intended, re-pin the number — the diff is "
                         "the change's own per-firing index cost.\n"
                         "  If it is not, a constant was added to the trigger path and "
                         "neither `lein perf` nor the two shape gates can see it.")
                    (clojure.core/name name) (delta-report reads (:reads got))))))))

(deftest the-mirror-is-what-fires-the-symmetric-rule
  ;; The budget above holds the symmetric workload's *cost*; this holds what it derived.
  ;; Every conclusion carries its arguments the other way round from the fact that
  ;; produced it, so a run reaching the rule without the mirror concludes nothing at all
  ;; rather than concluding the same thing more cheaply.
  (let [got (measure symmetric-trigger)]
    (is (= n (count (:sentences got))))
    (is (every? (fn [[_ a b]] (and (str/starts-with? (str a) "FcB")
                                   (str/starts-with? (str b) "FcA")))
                (:sentences got))
        (str "each conclusion must name the mirrored orientation — the un-mirrored "
             "binding satisfies no second antecedent, so a firing in the stored order "
             "means the workload stopped testing what it is for: "
             (pr-str (take 3 (:sentences got)))))))

(deftest the-instrument-is-silent-when-off
  ;; The budgets are only meaningful if the protocols added no work when nobody is collecting.
  (testing "a chaining run outside `start`/`stop` records nothing"
    (is (false? (prof/profiling?)))
    (let [[kb trigs _] (unfanned-join)]
      (tu/with-shipped-config (chain/chain kb trigs nil)))
    (is (nil? (prof/snapshot)))))
