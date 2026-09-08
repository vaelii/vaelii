;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting.

  This namespace sits above `vaelii.core` because the aggregate composes the public
  `all-specified-violations` audit.  Core reaches it through `vaelii.impl.wiring`, the
  same deliberate layering inversion used by the specified audit itself."
  (:require [vaelii.core :as v]
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
        specified   (v/all-specified-violations kb context)
        findings    (cond-> {}
                      (seq specified)
                      (assoc :all-specified-violations specified)
                      (seq definitions)
                      (assoc :definition-inconsistencies definitions))]
    (merge {:status (if (seq findings) :gap :audited)
            :candidate-count (count candidate-terms)}
           findings)))
