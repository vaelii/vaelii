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
  a log that is otherwise full of ticks and timings."
  (:require [clojure.test :as t]))

(defn- assertions ^long [c]
  (+ (long (:pass c 0)) (long (:fail c 0)) (long (:error c 0))))

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
