;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting.

  This namespace sits below `vaelii.core`, which requires it: the aggregate composes the
  `predall` specified audit and the `provers` definition pass, both of which sit below
  core themselves, so every call here points downward."
  (:require [vaelii.impl.predall :as predall]
            [vaelii.impl.provers :as provers]))

(defn kb-integrity
  "Run the bounded integrity sweep in `context` over `candidate-terms`.

  A clean result is `{:status :audited :candidate-count n}`.  A result with findings
  is `{:status :gap :candidate-count n ...}`, adding either or both sparse categories:
  `:all-specified-violations` and `:definition-inconsistencies`.  The status therefore
  cannot be mistaken for success merely because one category is absent.

  `candidate-terms` must be a finite set of ground terms.  It bounds only the
  definitional pass; the specified pass audits its own finite declaration population.
  Reads only; nothing is filed, asserted, retracted, or repaired."
  [kb candidate-terms context]
  (let [definitions (provers/definition-inconsistencies kb candidate-terms context)
        specified   (predall/all-specified-violations kb context)
        findings    (cond-> {}
                      (seq specified)
                      (assoc :all-specified-violations specified)
                      (seq definitions)
                      (assoc :definition-inconsistencies definitions))]
    (merge {:status (if (seq findings) :gap :audited)
            :candidate-count (count candidate-terms)}
           findings)))
