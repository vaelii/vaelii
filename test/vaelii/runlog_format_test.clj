;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.runlog-format-test
  "The run ledger's columns and format version, pinned.

  `scripts/lib/runlog.sh` appends one row to `logs/runs.tsv` per check run, and
  vaelii-top reads it.  vaelii-top lives in another repository (vaelii-tools), so
  nothing in this one fails when the ledger's shape changes under it.  This test
  runs the writer into a scratch file and pins what it wrote: the header, the
  field count of a row, and the `format` value.

  ## On failure

  - **The writer appends a column.**  A reader keys on column names, so the format
    stays where it is.  Add the name to `columns` below.
  - **The writer renames or drops a column, or a value means something else.**  Raise
    `RUNLOG_FORMAT` in `runlog.sh`, then change `columns` and `row-format` below.
  - Either way, vaelii-top's `runs.parse_ledger` in vaelii-tools owes a matching
    change: it reads the names this test pins."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def ^:private columns
  ["started" "epoch" "seconds" "kind" "variant" "state" "revision" "dirty"
   "subject" "summary" "log" "format"])

(def ^:private row-format "1")

(defn- with-ledger
  "Call `f` with a ledger file in a fresh directory, and delete both after."
  [f]
  (let [dir    (.toFile (Files/createTempDirectory "vaelii-runlog-" (into-array FileAttribute [])))
        ledger (io/file dir "runs.tsv")]
    (try (f ledger)
         (finally (doseq [^File x (reverse (file-seq dir))] (.delete x))))))

(defn- record!
  "Source the writer and append one row to `ledger`. The summary carries a tab and
  a newline, which the writer must squash rather than let add a column or a row."
  [^File ledger]
  (shell/sh "bash" "-c"
            (str ". scripts/lib/runlog.sh && runlog_start && "
                 "runlog_record lint - passed $'11/11\\tclean\\nsecond line' logs/lint/run-1.log")
            :env (assoc (into {} (System/getenv)) "RUNLOG_FILE" (.getPath ledger))))

(defn- rows [^File ledger]
  (mapv #(str/split % #"\t" -1) (str/split-lines (slurp ledger))))

(deftest a-new-ledger-carries-the-pinned-columns
  (with-ledger
    (fn [ledger]
      (is (zero? (:exit (record! ledger))))
      (is (zero? (:exit (record! ledger))))
      (let [[header & body] (rows ledger)]
        (testing "the header names the pinned columns, in order"
          (is (= columns header)))
        (testing "every row has one field per column"
          (is (= 2 (count body)))
          (is (every? #(= (count columns) (count %)) body)))
        (testing "each row states the format it was written in"
          (is (every? #(= row-format (get (zipmap header %) "format")) body)))
        (testing "a tab or newline in a value does not add a column or a row"
          (is (= "11/11 clean second line" (get (zipmap header (first body)) "summary"))))))))

(deftest a-ledger-with-no-format-column-gets-the-new-header
  (with-ledger
    (fn [ledger]
      (let [old    (str/join "\t" (butlast columns))
            row    (str/join "\t" ["2026-09-01T10:00:00" "1788256800" "60" "test" ":default"
                                   "passed" "abc12345" "0" "a subject" "ok" "target/gate/run-1"])]
        (spit ledger (str old "\n" row "\n"))
        (is (zero? (:exit (record! ledger))))
        (let [[header earlier later & more] (rows ledger)]
          (is (= columns header) "the header is replaced once, in place")
          (is (= (str/split row #"\t") earlier) "the rows already written are kept as they were")
          (is (= row-format (get (zipmap header later) "format")))
          (is (nil? more)))))))
