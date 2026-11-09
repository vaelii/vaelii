;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjointness-ratchet
  "The unknown-pair bound of the disjointness coverage ratchet, as pure functions over
  percentages, so `disjointness_ratchet_test` asserts the bound without a KB and
  `disjointness_audit_test` applies the bound to the starter KB's audit.")

(defn ratchet-verdict
  "The verdict on a `measured` unknown-pair percentage against the `committed` one.
  The measurement passes when it is at most `committed` plus `slack` percentage points
  and under `ceiling`. `:used` is the slack the measurement uses, zero at or under
  `committed`. `:warn?` is true for a pass that uses slack."
  [committed measured slack ceiling]
  (let [pass? (and (<= measured (+ committed slack)) (< measured ceiling))
        over  (- measured committed)]
    {:pass? pass?
     :used  (if (pos? over) over 0)
     :warn? (and pass? (pos? over))}))

(defn slack-lines
  "The two lines a `verdict` with `:warn?` prints: a GitHub Actions `::warning` workflow
  command, which the runner shows as an annotation on a green check, and the same
  numbers as a plain sentence for a local run. A verdict without `:warn?` prints none."
  [committed measured slack verdict]
  (if (:warn? verdict)
    [(format "::warning title=disjointness ratchet::used %.2fpp of the %.1fpp slack (committed %.2f%% → now %.2f%%)"
             (double (:used verdict)) (double slack) (double committed) (double measured))
     (format (str "disjointness ratchet: unknown pairs are %.2f%% of all pairs, %.2f percentage "
                  "points over the committed %.2f%%, inside the %.1f-point slack")
             (double measured) (double (:used verdict)) (double committed) (double slack))]
    []))
