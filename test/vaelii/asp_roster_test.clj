;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-roster-test
  "The test namespaces that gate on an answer-set solver, pinned as a roster.

  A solver test is wrapped in `(when asp? …)`, where `asp?` is `(solver/available?)`
  read at namespace load.  On a box with no solver the body does not run and the
  namespace still reports as passing, so these namespaces assert nothing about the
  subsystem unless CI puts a solver on the box first.  The `asp` job in
  `.github/workflows/test.yml` is that job, and it runs the list
  `scripts/asp-namespaces.sh` derives from the tree.

  The job derives that list on every run, so a namespace that starts reading
  `solver/available?` is covered the day it lands.  This test pins the derived
  set against the roster below, so the set *changing* is a red suite and a diff a
  reviewer sees, rather than a silent widening of what one CI job runs.

  ## On failure

  - **A namespace in the scan and not in the roster.**  Something new gates on the
    solver.  Add it to `roster` — the `asp` job already runs it.
  - **A namespace in the roster and not in the scan.**  Its gate is gone.  Either the
    tests no longer need a solver, in which case take the row out, or the gate was
    dropped by accident and those tests now fail on a box with no solver.
  - **The script prints nothing.**  The scan pattern no longer matches how the gate is
    spelled, which turns the `asp` job into a no-op.  Fix `scripts/asp-namespaces.sh`,
    not this list."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]))

(def ^:private roster
  "Every test namespace whose bodies gate on `solver/available?` — or, for
  `asp-solver-test`, on `clasp/available?`, which is the one that asserts the refusal an
  absent binary earns rather than skipping."
  #{'vaelii.asp-aspif-test
    'vaelii.asp-edge-test
    'vaelii.asp-label-test
    'vaelii.asp-solver-test
    'vaelii.constraint-solve-test
    'vaelii.koinii-schedule-test
    'vaelii.labeling-test
    'vaelii.solve-context-test
    'vaelii.sudoku-solve-test
    'vaelii.tsp-solve-test})

(def ^:private gate
  "How the gate is spelled, in the one place both the scan and the script read it."
  #"\((?:solver|clasp)/available\?\)")

(defn- scanned
  "The namespaces under `test/` whose source reads the gate — the same scan
  `scripts/asp-namespaces.sh` runs, done here in Clojure so the test does not depend on
  a shell.

  This namespace is excluded by name: it quotes the gate in order to scan for it, the
  same arrangement `check-prose.py` and `refusal-roster-test` use to stay off their own
  rosters.  `scripts/asp-namespaces.sh` excludes the same one file."
  []
  (into #{}
        (comp (filter #(.isFile ^java.io.File %))
              (filter #(str/ends-with? (.getName ^java.io.File %) ".clj"))
              (filter #(re-find gate (slurp %)))
              (map (fn [^java.io.File f]
                     (-> (.getPath f)
                         (str/replace #"^test/" "")
                         (str/replace #"\.clj$" "")
                         (str/replace "/" ".")
                         (str/replace "_" "-")
                         symbol)))
              (remove #{'vaelii.asp-roster-test}))
        (file-seq (io/file "test"))))

(deftest the-solver-gated-roster-is-what-the-tree-holds
  (let [found (scanned)]
    (testing "the scan finds something — an empty list makes the asp CI job a no-op"
      (is (seq found)))
    (testing "nothing gates on the solver that the roster does not name"
      (is (empty? (remove roster found))
          "add these to `roster`; the asp job already runs them"))
    (testing "nothing in the roster has lost its gate"
      (is (empty? (remove found roster))
          "these no longer read solver/available? — drop the row, or restore the gate"))))

(deftest the-script-and-the-scan-agree
  (testing "scripts/asp-namespaces.sh derives the same set this test scans for"
    (let [script (io/file "scripts/asp-namespaces.sh")]
      (is (.exists script) "the asp job reads this script to pick its namespaces")
      (when (.exists script)
        (let [{:keys [exit out]} (shell/sh "bash" (.getPath script))]
          (is (zero? exit))
          (is (= roster
                 (into #{} (map symbol) (remove str/blank? (str/split-lines out))))))))))
