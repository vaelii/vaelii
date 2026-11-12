;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.coverage
  "The instrumented JVMs `scripts/coverage.sh` runs, and one coverage measurement from
  their hits. `install!`, which a lein injection runs before cloverage instruments,
  replaces cloverage's probe and leaves the forms an earlier JVM hit without one.
  `write-hits` is the cloverage custom report each JVM runs, and `-main` sums the hits of
  every JVM and writes cloverage's HTML report, summary table and threshold verdict over
  the sums. Cloverage is resolved at the call, so this namespace loads on a classpath
  without it. See scripts/coverage.sh."
  (:require [clojure.java.io :as io]
            [clojure.string :as str])
  (:import (java.util.concurrent.atomic AtomicInteger)
           (java.util.zip GZIPInputStream GZIPOutputStream)))

(defn write-hits-file
  "Writes `covered`, cloverage's instrumented forms in instrumentation order, to the
  gzipped file `f` as `lib<TAB>file<TAB>line<TAB>hits` rows. A form with no line number
  has an empty line field."
  [f covered]
  (io/make-parents (io/file f))
  (with-open [w (io/writer (GZIPOutputStream. (io/output-stream (io/file f))))]
    (doseq [{:keys [lib file line hits]} covered]
      (.write w (str lib \tab file \tab line \tab (.get ^AtomicInteger hits) \newline)))))

(defn write-hits
  "Cloverage's `--custom-report` entry point: `write-hits-file` of every form this JVM
  instrumented, to `<output>/hits.tsv.gz`."
  [{:keys [output]}]
  (let [covered @@(requiring-resolve 'cloverage.coverage/*covered*)
        f       (io/file output "hits.tsv.gz")]
    (write-hits-file f covered)
    (println "Wrote" (count covered) "form hit counts to" (.getPath f))))

(defn- read-hits [f]
  (with-open [r (io/reader (GZIPInputStream. (io/input-stream (io/file f))))]
    (mapv #(str/split % #"\t" -1) (line-seq r))))

(defn first-hit-cover
  "Cloverage's probe `cover` reduced to its first call per form: the returned probe calls
  `cover` when the form's slot in `seen` is unset and sets it, and does nothing after.
  A covered form's hit count reads 1, or more when threads race on its first hit. A form
  index past the end of `seen` calls `cover` every time."
  [cover ^booleans seen]
  (fn [idx]
    (let [i (int idx)]
      (if (< i (alength seen))
        (when-not (aget seen i)
          (aset seen i true)
          (cover idx))
        (cover idx)))))

(defn skipping-track-coverage
  "Cloverage's `track-coverage`, which registers a form and returns `(capture idx form)`,
  returning `(do form)` instead when `(skip? idx)` holds. The `do` keeps the compiler on
  the path the probed form took: a bare var symbol at the head of an invocation sends it
  down the primitive-signature path, which reads the head unexpanded and throws. Every
  form is registered, so the form indices and the `write-hits` rows are those of a run
  that skips none."
  [track-coverage skip?]
  (fn [line-hint form]
    (let [captured (track-coverage line-hint form)]
      (if (skip? (second captured))
        (with-meta (list 'do form) (meta form))
        captured))))

(defn install!
  "Run by a lein injection before cloverage instruments: replaces `cover` with
  `first-hit-cover` over 2^21 slots. Given `hits-file`, the `write-hits` file of an
  earlier JVM over the same source and options, `track-coverage` also leaves every form
  that JVM hit without a probe."
  ([] (install! nil))
  ([hits-file]
   (alter-var-root (requiring-resolve 'cloverage.coverage/cover)
                   first-hit-cover (boolean-array (bit-shift-left 1 21)))
   (when hits-file
     (let [rows (read-hits hits-file)
           hit  (boolean-array (count rows))]
       (dotimes [i (count rows)]
         (aset hit i (pos? (parse-long (peek (rows i))))))
       (alter-var-root (requiring-resolve 'cloverage.coverage/track-coverage)
                       skipping-track-coverage
                       (fn [idx] (and (< idx (alength hit)) (aget hit (int idx)))))
       (println "Leaving" (count (filter true? hit)) "of" (count rows)
                "forms without a probe, as hit in" hits-file)))))

(defn merged-forms
  "The forms of the `write-hits` files `fs`, each with its hits summed across the files,
  in the shape cloverage's `covered` returns. Throws unless every file names the same
  forms in the same order, which holds when every JVM instrumented the same source
  with the same options."
  [fs]
  (let [[base & more] (mapv read-hits fs)
        ident         #(mapv pop %)
        base-ident    (ident base)]
    (doseq [[f rows] (map vector (rest fs) more)
            :when (not= base-ident (ident rows))]
      (throw (ex-info (str f " names different forms from " (first fs)
                           " (" (count rows) " rows against " (count base) ")")
                      {:type :coverage-mismatch :file f :base (first fs)})))
    (apply mapv
           (fn [& rows]
             (let [[lib file line] (first rows)
                   hits            (transduce (map #(parse-long (peek %))) + rows)]
               {:tracked true
                :lib     (symbol lib)
                :file    file
                :line    (when (seq line) (parse-long line))
                :hits    hits
                :covered (pos? hits)}))
           base more)))

(defn- parse-args [args]
  (loop [[a b & more :as args] args, opts {:files []}]
    (cond
      (empty? args)          opts
      (= a "--output")       (recur more (assoc opts :output b))
      (= a "--fail-under")   (recur more (assoc opts :fail-under (parse-double b)))
      :else                  (recur (rest args) (update opts :files conj a)))))

(defn -main
  "`--output DIR [--fail-under PCT] HITS-FILE…`. Writes the HTML report to DIR, which it
  creates, prints cloverage's summary table, and exits 3 when the lower of the forms and
  lines percentages is under PCT, as cloverage's `--fail-threshold` does."
  [& args]
  (let [{:keys [output fail-under files]} (parse-args args)
        _     (when (or (nil? output) (empty? files))
                (throw (ex-info "usage: --output DIR [--fail-under PCT] HITS-FILE…" {})))
        forms ((requiring-resolve 'cloverage.report/gather-stats) (merged-forms files))
        {:keys [percent-forms-covered percent-lines-covered]}
        ((requiring-resolve 'cloverage.report/total-stats) forms)
        under? (and fail-under (< (min percent-forms-covered percent-lines-covered) fail-under))]
    (println "Merged" (count files) "hit files")
    (.mkdirs (io/file output))
    ((requiring-resolve 'cloverage.report.html/report) output forms)
    ((requiring-resolve 'cloverage.report.console/summary) forms 50 80 false)
    (when under?
      (println "Failing build as coverage is below threshold of" fail-under "%"))
    (shutdown-agents)
    (System/exit (if under? 3 0))))
