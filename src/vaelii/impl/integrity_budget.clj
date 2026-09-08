;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity-budget
  "The cooperative work meter used only while a bounded KB-integrity sweep runs.")

(def ^:dynamic *meter*
  "The current sweep's meter atom, or nil outside a bounded integrity read."
  nil)

(defn meter
  "A new meter for `opts`, stamped with its start and optional deadline."
  [opts]
  (let [start (System/nanoTime)]
    (atom {:work 0
           :max-work (:max-work opts)
           :start start
           :deadline (when-let [ms (:max-ms opts)]
                       (+ start (long (* ms 1e6))))})))

(defn snapshot
  "The public counters of meter `m`."
  [m]
  {:work (:work @m)
   :elapsed-ms (/ (double (- (System/nanoTime) (:start @m))) 1e6)})

(defn spend!
  "Spend one cooperative work unit, throwing before work beyond the bound begins."
  []
  (when-let [m *meter*]
    (let [{:keys [work max-work deadline]} @m
          now (System/nanoTime)]
      (cond
        (and deadline (>= now deadline))
        (throw (ex-info "KB-integrity wall-clock budget exhausted"
                        {:type :integrity-budget-exhausted :reason :max-ms}))

        (and max-work (>= work max-work))
        (throw (ex-info "KB-integrity work budget exhausted"
                        {:type :integrity-budget-exhausted :reason :max-work}))

        :else
        (swap! m update :work inc)))))
