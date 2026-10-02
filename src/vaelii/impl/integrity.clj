;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting.

  This namespace sits below `vaelii.core`, which requires it: the aggregate reads the
  `predall` specified audit's focused per-declaration units and the `provers` definition
  pass, both of which sit below core themselves, so every call here points downward and
  the internal units stay off the public API."
  (:require [vaelii.impl.integrity-budget :as integrity-budget]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
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

(defn- categories [definitions specified widenings]
  (cond-> {}
    (seq specified)   (assoc :all-specified-violations specified)
    (seq definitions) (assoc :definition-inconsistencies definitions)
    (seq widenings)   (assoc :genl-arg-widening widenings)))

(defn- bounded-categories [definitions specified widenings max-results]
  (if (nil? max-results)
    (categories definitions specified widenings)
    (let [definitions (vec (take max-results definitions))
          remaining   (- max-results (count definitions))
          specified   (into {} (take remaining (sort-by (comp nm/print-key key) specified)))
          remaining   (- remaining (count specified))
          widenings   (vec (take remaining widenings))]
      (categories definitions specified widenings))))

(defn- truncate-report
  [candidate-count reason meter {:keys [definitions specified widenings]} max-results]
  (merge {:status :truncated :reason reason :candidate-count candidate-count}
         (integrity-budget/snapshot meter)
         (bounded-categories definitions specified widenings max-results)))

(defn- specified-findings
  "Audit one declared predicate at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (loop [audits (predall/specified-declaration-audits kb context)
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

;; ---- genl-arg-widening: a predicate genl edge that widens an argument type ----

(defn- own-arg-types
  "`{position #{type …}}` from the `arg` declarations `context` sees written on `pred`
  itself — the domain its author declared, before any super-predicate's declaration is
  read into it."
  [kb pred context]
  (reduce (fn [m [_ b]]
            (integrity-budget/spend!)
            (let [n (get b '?n) t (get b '?t)]
              (if (and (integer? n) (symbol? t) (not (sx/variable? t)))
                (update m n (fnil conj #{}) t)
                m)))
          {}
          (res/matches-visible kb (list 'arg pred '?n '?t) context)))

(defn- constraining-arg-types
  "`[position type declaring-predicate]` for every `arg` declaration binding `pred`'s
  tuples from `context`: `pred`'s own and every visible super-predicate's, read through
  `res/constraining-predicates`, the closure `assert`'s argument check reads."
  [kb pred context]
  (for [p     (res/constraining-predicates kb 'arg pred context)
        [_ b] (res/matches-visible kb (list 'arg p '?n '?t) context)
        :let  [n (get b '?n) t (get b '?t)]
        :when (and (integer? n) (symbol? t) (not (sx/variable? t)))]
    [n t p]))

(defn- declared-predicates
  "The predicates carrying a visible `arg` declaration of their own, in print order: the
  one open read of this pass, a census of declarations rather than of any extent."
  [kb context]
  (->> (res/matches-visible kb '(arg ?p ?n ?t) context)
       (keep (fn [[_ b]]
               (integrity-budget/spend!)
               (let [p (get b '?p)]
                 (when (and (symbol? p) (not (sx/variable? p))) p))))
       distinct
       (sort-by nm/print-key)))

(defn- edge-widenings
  "The findings for one visible edge `(genl spec super)`: each position where a type
  `spec` declares is subsumed by none of the types `super`'s constraint demands there.
  A `spec` position carrying several declared types is their intersection, so it is
  compatible with a demanded type as soon as one of them is subsumed by it."
  [kb tx spec own super context]
  (for [[n tq declared-on] (sort-by (fn [[n t p]] [n (nm/print-key t) (nm/print-key p)])
                                    (distinct (constraining-arg-types kb super context)))
        :let  [tps (get own n)]
        :when (seq tps)
        :when (do (integrity-budget/spend!)
                  (not-any? #(or (= % tq) (tax/genl? tx % tq context)) tps))
        tp    (sort-by nm/print-key tps)]
    (cond-> {:spec spec :genl super :arg n :spec-type tp :genl-type tq}
      (not= declared-on super) (assoc :genl-type-declared-on declared-on))))

(defn- widening-findings
  "Audit every visible predicate `genl` edge out of a predicate that declares its own
  argument types, one edge at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (loop [findings []
           units    (for [spec  (declared-predicates kb context)
                          :let  [own (own-arg-types kb spec context)]
                          super (sort-by nm/print-key (tax/direct-genls tx spec context))
                          :when (not= super spec)
                          finding (do (integrity-budget/spend!)
                                      (edge-widenings kb tx spec own super context))]
                      finding)]
      (if-let [finding (first units)]
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (integrity-budget/record-widening! finding)
            (recur (conj findings finding) (rest units))))
        {:status :complete :findings findings}))))

(defn kb-integrity
  "Run the bounded integrity sweep in `context` over `candidate-terms`.

  A clean result is `{:status :audited :candidate-count n}`.  A result with findings
  is `{:status :gap :candidate-count n ...}`, adding any of three sparse categories:
  `:all-specified-violations`, `:definition-inconsistencies` and `:genl-arg-widening`.
  The status therefore cannot be mistaken for success merely because a category is
  absent.

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
         progress        (atom {:definitions [] :specified {} :widenings []})
         max-results     (:max-results options)]
     (binding [integrity-budget/*meter* meter
               integrity-budget/*progress* progress
               violations/*report-sink* local-reports]
       (try
         (let [definition-result
               (provers/definition-inconsistencies
                 kb candidate-terms context max-results)
               definitions (:findings definition-result)]
           (swap! progress assoc :definitions definitions)
           (if (= :truncated (:status definition-result))
             (truncate-report candidate-count (:reason definition-result) meter
                              @progress max-results)
             (let [remaining (when max-results (- max-results (count definitions)))
                   specified-result (specified-findings kb context remaining)
                   specified (:findings specified-result)]
               (swap! progress assoc :specified specified)
               (if (= :truncated (:status specified-result))
                 (truncate-report candidate-count :max-results meter @progress max-results)
                 (let [remaining (when remaining (- remaining (count specified)))
                       widening-result (widening-findings kb context remaining)
                       widenings (:findings widening-result)]
                   (swap! progress assoc :widenings widenings)
                   (if (= :truncated (:status widening-result))
                     (truncate-report candidate-count :max-results meter @progress
                                      max-results)
                     (let [findings (categories definitions specified widenings)]
                       (integrity-budget/spend!)
                       (merge {:status (if (seq findings) :gap :audited)
                               :candidate-count candidate-count}
                              findings))))))))
         (catch clojure.lang.ExceptionInfo e
           (if-let [reason (integrity-budget/exhausted e)]
             (truncate-report candidate-count reason meter @progress
                              max-results)
             (throw e))))))))
