;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjointness-ratchet-test
  "`ratchet-verdict` decides the unknown-pair bound of the disjointness coverage ratchet
  from four percentages, and `slack-lines` formats the warning a pass inside the slack
  prints. Both are pure, so this namespace loads no KB."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.disjointness-ratchet :as dr]))

(deftest a-measurement-inside-the-slack-passes-and-warns
  (let [v (dr/ratchet-verdict 6.59 6.80 0.5 10.0)]
    (is (true? (:pass? v)))
    (is (true? (:warn? v)))
    (is (< (Math/abs (- 0.21 (:used v))) 1e-9)
        "the verdict reports the 0.21 pp of slack the measurement uses")))

(deftest a-measurement-at-the-committed-value-passes-without-a-warning
  (let [v (dr/ratchet-verdict 6.59 6.59 0.5 10.0)]
    (is (true? (:pass? v)))
    (is (false? (:warn? v)))
    (is (zero? (:used v)))))

(deftest a-measurement-over-the-committed-value-plus-the-slack-fails
  (let [v (dr/ratchet-verdict 6.59 7.10 0.5 10.0)]
    (is (false? (:pass? v)))
    (is (false? (:warn? v)) "a failing verdict prints no warning, since the assertion reports it")))

(deftest a-measurement-at-or-over-the-ceiling-fails-inside-the-slack
  (is (false? (:pass? (dr/ratchet-verdict 9.80 10.0 0.5 10.0)))
      "10.0% is inside 9.80 + 0.5 and fails at the 10% ceiling")
  (is (false? (:pass? (dr/ratchet-verdict 9.80 10.2 0.5 10.0)))
      "10.2% is inside 9.80 + 0.5 and fails over the 10% ceiling"))

(deftest a-measurement-under-the-committed-value-passes-without-a-warning
  (let [v (dr/ratchet-verdict 6.59 6.20 0.5 10.0)]
    (is (true? (:pass? v)))
    (is (false? (:warn? v)))
    (is (zero? (:used v)) "an improvement uses no slack")))

(deftest a-pass-inside-the-slack-prints-a-workflow-warning-and-a-plain-line
  (let [v              (dr/ratchet-verdict 6.59 6.80 0.5 10.0)
        [command line] (dr/slack-lines 6.59 6.80 0.5 v)]
    (is (= "::warning title=disjointness ratchet::used 0.21pp of the 0.5pp slack (committed 6.59% → now 6.80%)"
           command))
    (is (= "disjointness ratchet: unknown pairs are 6.80% of all pairs, 0.21 percentage points over the committed 6.59%, inside the 0.5-point slack"
           line))))

(deftest a-verdict-without-a-warning-prints-nothing
  (is (empty? (dr/slack-lines 6.59 6.59 0.5 (dr/ratchet-verdict 6.59 6.59 0.5 10.0)))))
