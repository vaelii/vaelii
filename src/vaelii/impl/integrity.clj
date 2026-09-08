;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting.

  Core reaches this reporting layer through `vaelii.impl.wiring`; the same knot exposes
  the specified audit's focused internal units without adding them to the public API."
  (:require [vaelii.impl.integrity-budget :as integrity-budget]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wiring :as wiring]))

(def integrity-opt-keys
  "The cooperative bounds `kb-integrity` reads."
  #{:max-work :max-ms :max-results})

(defn- check-opts! [options]
  (opts/check! options integrity-opt-keys "kb-integrity"
               "A bound nothing reads would make an integrity sweep unbounded in silence.")
  (doseq [[k ok? what] [[:max-work nat-int? "a non-negative integer"]
                        [:max-results nat-int? "a non-negative integer"]
                        [:max-ms #(and (number? %) (not (neg? (double %))))
                         "a non-negative number"]]
          :let [value (get options k)]
          :when (and (contains? options k) (not (ok? value)))]
    (throw (ex-info (str "kb-integrity " k " must be " what ", got " (pr-str value))
                    {:type :unknown-option :mismatch :bad-value
                     :option k :value value})))
  options)

(defn- categories [definitions specified]
  (cond-> {}
    (seq specified)   (assoc :all-specified-violations specified)
    (seq definitions) (assoc :definition-inconsistencies definitions)))

(defn- bounded-categories [definitions specified max-results]
  (if (nil? max-results)
    (categories definitions specified)
    (let [definitions (vec (take max-results definitions))
          remaining   (- max-results (count definitions))
          specified   (into {} (take remaining (sort-by (comp pr-str key) specified)))]
      (categories definitions specified))))

(defn- truncate-report [candidate-count reason meter definitions specified max-results]
  (merge {:status :truncated :reason reason :candidate-count candidate-count}
         (integrity-budget/snapshot meter)
         (bounded-categories definitions specified max-results)))

(defn- specified-findings
  "Audit one declared predicate at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (loop [audits (wiring/specified-declaration-audits kb context)
         findings {}]
    (if-let [[declaration result] (first audits)]
      (if (or (= :gap (:status result)) (seq (:violations result)))
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (integrity-budget/record-specified! declaration result)
            (recur (rest audits) (assoc findings declaration result))))
        (recur (rest audits) findings))
      {:status :complete :findings findings})))

(defn kb-integrity
  "Run the bounded integrity sweep in `context` over `candidate-terms`.

  A clean result is `{:status :audited :candidate-count n}`.  A result with findings
  is `{:status :gap :candidate-count n ...}`, adding either or both sparse categories:
  `:all-specified-violations` and `:definition-inconsistencies`.  The status therefore
  cannot be mistaken for success merely because one category is absent.

  `candidate-terms` must be a finite set of ground terms. `options` may bound the sweep
  by cooperative work units, wall-clock milliseconds, and returned findings:
  `{:max-work n :max-ms n :max-results n}`. Exhaustion returns `:status :truncated`,
  never a clean-looking `:audited` prefix.

  Reads only. Diagnostics raised by evaluating a query-only condition are collected in
  a private sink, so the live sentexes, belief and violations ledger do not move."
  ([kb candidate-terms context]
   (kb-integrity kb candidate-terms context nil))
  ([kb candidate-terms context options]
   (check-opts! options)
   (let [options         (or options {})
         candidate-count (when (set? candidate-terms) (count candidate-terms))
         meter           (integrity-budget/meter options)
         local-reports   (atom [])
         progress        (atom {:definitions [] :specified {}})]
     (binding [integrity-budget/*meter* meter
               integrity-budget/*progress* progress
               violations/*report-sink* local-reports]
       (try
         (let [definition-result
               (provers/definition-inconsistencies
                 kb candidate-terms context (:max-results options))
               definitions (:findings definition-result)]
           (swap! progress assoc :definitions definitions)
           (if (= :truncated (:status definition-result))
             (truncate-report candidate-count (:reason definition-result) meter definitions {}
                              (:max-results options))
             (let [remaining (when-let [limit (:max-results options)]
                               (- limit (count definitions)))
                   specified-result (specified-findings kb context remaining)
                   specified (:findings specified-result)]
               (swap! progress assoc :specified specified)
               (if (= :truncated (:status specified-result))
                 (truncate-report candidate-count :max-results meter definitions specified
                                  (:max-results options))
                 (let [findings (categories definitions specified)]
                   (integrity-budget/spend!)
                   (merge {:status (if (seq findings) :gap :audited)
                           :candidate-count candidate-count}
                          findings))))))
         (catch clojure.lang.ExceptionInfo e
           (if (= :integrity-budget-exhausted (:type (ex-data e)))
             (let [{:keys [definitions specified]} @progress]
               (truncate-report candidate-count (:reason (ex-data e)) meter
                                definitions specified (:max-results options)))
             (throw e))))))))
