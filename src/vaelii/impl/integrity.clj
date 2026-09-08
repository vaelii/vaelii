;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting.

  This namespace sits above `vaelii.core` because the aggregate composes the public
  `all-specified-violations` audit.  Core reaches it through `vaelii.impl.wiring`, the
  same deliberate layering inversion used by the specified audit itself."
  (:require [vaelii.core :as v]
            [vaelii.impl.integrity-budget :as integrity-budget]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.violations :as violations]))

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

(defn- truncate-report [candidate-count reason meter definitions specified]
  (merge {:status :truncated :reason reason :candidate-count candidate-count}
         (integrity-budget/snapshot meter)
         (categories definitions specified)))

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
             (truncate-report candidate-count (:reason definition-result) meter definitions {})
             (let [specified (v/all-specified-violations kb context)
                   remaining (when-let [limit (:max-results options)]
                               (- limit (count definitions)))
                   ordered   (sort-by (comp pr-str key) specified)
                   kept      (if remaining (into {} (take remaining ordered)) specified)]
               (swap! progress assoc :specified kept)
               (if (and remaining (> (count specified) remaining))
                 (truncate-report candidate-count :max-results meter definitions kept)
                 (let [findings (categories definitions specified)]
                   (integrity-budget/spend!)
                   (merge {:status (if (seq findings) :gap :audited)
                           :candidate-count candidate-count}
                          findings))))))
         (catch clojure.lang.ExceptionInfo e
           (if (= :integrity-budget-exhausted (:type (ex-data e)))
             (let [{:keys [definitions specified]} @progress]
               (truncate-report candidate-count (:reason (ex-data e)) meter
                                definitions specified))
             (throw e))))))))
