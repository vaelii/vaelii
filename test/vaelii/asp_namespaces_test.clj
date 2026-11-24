;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-namespaces-test
  "The test namespaces that check for an answer-set solver, listed by name.

  A solver test is wrapped in `(when asp? …)`, where `asp?` is `(solver/available?)`
  read at namespace load.  On a box with no solver the body does not run and the
  namespace still reports as passing, so these namespaces assert nothing about the
  subsystem unless CI puts a solver on the box first.  The `asp` job in
  `.github/workflows/test.yml` is that job, and it runs the list
  `scripts/asp-namespaces.sh` derives from the tree.

  The job derives that list on every run, so a namespace that starts reading
  `solver/available?` is covered the day it lands.  This test compares the derived
  set with the list below, so the set *changing* is a red suite and a diff a
  reviewer sees, rather than a silent widening of what one CI job runs.

  ## On failure

  - **A namespace in the scan and not in the list.**  A new namespace is conditional on
    the solver.  Add it to `solver-namespaces` — the `asp` job already runs it.
  - **A namespace in the list and not in the scan.**  Its availability call is gone.
    Either the tests no longer need a solver, in which case take the row out, or the
    availability call was dropped by accident and those tests now fail on a box with no solver.
  - **The script prints nothing.**  The scan pattern no longer matches how the availability
    call is spelled, which turns the `asp` job into a no-op.  Fix `scripts/asp-namespaces.sh`,
    not this list."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.test-util :as tu]))

(def ^:private solver-namespaces
  "Every test namespace whose bodies are conditional on `solver/available?` — or, for
  `asp-solver-test`, on `clasp/available?`, which is the one that asserts the refusal an
  absent binary earns rather than skipping."
  #{'vaelii.asp-aspif-test
    'vaelii.asp-edge-test
    'vaelii.asp-label-test
    'vaelii.asp-programs-test
    'vaelii.asp-prover-test
    'vaelii.asp-solver-test
    'vaelii.cardinality-solve-test
    'vaelii.cli-test
    'vaelii.constraint-solve-test
    'vaelii.koinii-schedule-test
    'vaelii.labeling-test
    'vaelii.minimize-solve-test
    'vaelii.run-test
    'vaelii.solve-context-test
    'vaelii.solve-rule-test
    'vaelii.web-vantage-test})

(def ^:private availability-call
  "How the availability call is spelled, in the one place both the scan and the script read it."
  #"\((?:solver|clasp)/available\?\)")

(defn- scanned
  "The namespaces under `test/` whose source makes the availability call — the same scan
  `scripts/asp-namespaces.sh` runs, done here in Clojure so the test does not depend on
  a shell.

  This namespace is excluded by name: it quotes the availability call in order to scan
  for it, the same arrangement `check-prose.py` and `refusal-types-test` use to stay out
  of their own scans.  `scripts/asp-namespaces.sh` excludes the same one file."
  []
  (into #{}
        (comp (filter #(.isFile ^java.io.File %))
              (filter #(str/ends-with? (.getName ^java.io.File %) ".clj"))
              (filter #(re-find availability-call (slurp %)))
              (map (fn [^java.io.File f]
                     (-> (.getPath f)
                         (str/replace \\ \/)
                         (str/replace #"^test/" "")
                         (str/replace #"\.clj$" "")
                         (str/replace "/" ".")
                         (str/replace "_" "-")
                         symbol)))
              (remove #{'vaelii.asp-namespaces-test}))
        (file-seq (io/file "test"))))

(deftest the-solver-checking-namespaces-are-what-the-tree-holds
  (let [found (scanned)]
    (testing "the scan finds something — an empty list makes the asp CI job a no-op"
      (is (seq found)))
    (testing "no namespace is conditional on the solver that the list does not name"
      (is (empty? (remove solver-namespaces found))
          "add these to `solver-namespaces`; the asp job already runs them"))
    (testing "nothing in the list has lost its availability call"
      (is (empty? (remove found solver-namespaces))
          "these no longer read solver/available? — drop the row, or restore the availability call"))))

(deftest the-script-and-the-scan-agree
  (testing "scripts/asp-namespaces.sh derives the same set this test scans for"
    (let [script (io/file "scripts/asp-namespaces.sh")]
      (is (.exists script) "the asp job reads this script to pick its namespaces")
      (when (.exists script)
        (let [{:keys [exit out]} (shell/sh tu/bash "scripts/asp-namespaces.sh")]
          (is (zero? exit))
          (is (= solver-namespaces
                 (into #{} (map symbol) (remove str/blank? (str/split-lines out))))))))))
