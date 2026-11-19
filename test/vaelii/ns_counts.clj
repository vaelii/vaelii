;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ns-counts
  "Per-namespace assertion counts, for a suite total that moves between runs.

  `scripts/test-backends.sh` checks that every configuration ran the same number of
  assertions, because a run that quietly skipped something is indistinguishable from a green run.  When
  that check fails the next question is always *which namespace*, and the suite's own
  output cannot answer it: `lein test` prints one total for 297 namespaces.

  Bisecting the total is the obvious move and it is the wrong one.  A namespace list
  passed to `lein test` is not the set `lein test :default` discovers (304 files against
  297 namespaces here), and naming namespaces explicitly changes the order they run in —
  so a search over subsets can report a difference the whole suite does not have, or miss
  one it does.  Both happen.  Counting per namespace inside **one ordinary run** avoids
  the question entirely: same discovery, same order, same fixtures.

  Off unless `VAELII_TEST_NS_COUNTS` is true, and it changes nothing when on — the counts
  are read from `clojure.test`'s own counters, which are already being maintained.

      VAELII_TEST_NS_COUNTS=1 lein test :default 2>&1 | grep NSCOUNT > a.txt
      VAELII_TEST_NS_COUNTS=1 lein test :default 2>&1 | grep NSCOUNT > b.txt
      diff a.txt b.txt          # the namespace whose count moved

  One line per namespace, tab-separated, prefixed `NSCOUNT` so it survives a grep out of
  a log that is otherwise full of ticks and timings.

  `VAELII_TEST_VERDICTS` installs the per-test counterpart, `install-verdicts!`: one
  `TESTVERDICT` line per test var, which `lein test-red` inverts (scripts/test-selector.sh)."
  (:require [clojure.test :as t]))

(defn- assertions ^long [c]
  (+ (long (:pass c 0)) (long (:fail c 0)) (long (:error c 0))))

(defn- failures ^long []
  (let [c (when t/*report-counters* @t/*report-counters*)]
    (+ (long (:fail c 0)) (long (:error c 0)))))

(defn- emit!
  "Print through a writer over `System/out` rather than `*out*`: `lein test` rebinds the
  latter to capture a namespace's output, and a line written there would be buffered into
  the report instead of the log."
  [^String line]
  (doto (java.io.PrintWriter. System/out true) (.println line) (.flush)))

(defn install!
  "Wrap `clojure.test/report`'s `:end-test-ns` so each namespace prints what it ran.
  Idempotent — installing twice leaves one wrapper, since the second wraps the first and
  the first is what the second calls."
  []
  (let [orig (get-method t/report :end-test-ns)]
    (defmethod t/report :end-test-ns [m]
      (when orig (orig m))
      ;; The counter is read as-is, never diffed against the previous namespace.
      ;; Leiningen rebinds `*report-counters*` per namespace, so what is in it here is
      ;; already this namespace's own tally — diffing it against the one before produced
      ;; alternating positives and negatives that paired off to nothing, which is what
      ;; a difference of two unrelated refs looks like.
      (emit! (format "NSCOUNT\t%s\t%d"
                     (ns-name (:ns m))
                     (assertions (when t/*report-counters* @t/*report-counters*))))))
  :installed)

(defn install-verdicts!
  "Wrap `clojure.test/report`'s `:begin-test-var` and `:end-test-ns` so each test var
  prints `TESTVERDICT <ns/name> pass|fail`.  A var's tally runs from its
  `:begin-test-var` to the next one or to its namespace's end, so a failure an `:each`
  fixture reports after the body counts against the test it ran after."
  []
  (let [begin  (get-method t/report :begin-test-var)
        end-ns (get-method t/report :end-test-ns)
        open   (atom nil)
        close! (fn []
                 (when-let [[v n] @open]
                   (reset! open nil)
                   (emit! (format "TESTVERDICT\t%s\t%s" v
                                  (if (= n (failures)) "pass" "fail")))))]
    (defmethod t/report :begin-test-var [m]
      (close!)
      (when begin (begin m))
      (reset! open [(symbol (:var m)) (failures)]))
    (defmethod t/report :end-test-ns [m]
      (close!)
      (when end-ns (end-ns m))))
  :installed)

(defonce ^:private repeats (atom nil))

(defn install-repeat!
  "Wrap `clojure.test/test-ns` so it runs each namespace `n` times in a row, fixtures
  included, and answers the sum of the runs' counters.  A second install sets `n` and
  keeps the one wrapper.  Each run reports its own `:begin-test-ns`, so `lein test`
  prints a `lein test <ns>` line per run and `scripts/lib/ns-timings.sh` reads a row per
  run."
  [n]
  (when-not (first (reset-vals! repeats n))
    (alter-var-root #'t/test-ns
                    (fn [test-ns]
                      (fn [ns] (reduce (fn [acc _] (merge-with + acc (test-ns ns))) {} (range @repeats))))))
  :installed)
