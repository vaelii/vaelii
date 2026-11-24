;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.clasp
  "Subprocess wrapper around the clasp ASP solver, or the clingo executable, which takes
   the same flags and answers the same JSON (`*clasp-binary*`).

   Takes ASPIF text on stdin and reads the JSON `Result` of `--outf=2`.  clasp's exit
   codes encode the solve outcome (10 sat, 20 unsat, 30 optimum) and are not errors; a
   run throws only when clasp does not run or answers nothing parseable.  The five modes
   are `solve`'s.  The search flags are `search-args`, and the limits are docs/asp.md's
   \"The solve limit\" and \"The time limit\".

   `run-clasp` owns the process: it returns only after the process has exited, and kills
   it with every descendant at the deadline and on a throw out of the wait."
  (:require
   [cheshire.core :as json]
   [clojure.java.io :as io]
   [clojure.string :as str]
   [vaelii.impl.config :as config])
  (:import
   [java.lang ProcessHandle]
   [java.util.concurrent TimeUnit]))

(defn- configured-binary
  "`vaelii.clasp.bin`, else `VAELII_CLASP_BIN`, else `clasp`; a blank value is unset."
  []
  (or (some-> (System/getProperty "vaelii.clasp.bin") str/trim not-empty)
      (some-> (System/getenv "VAELII_CLASP_BIN") str/trim not-empty)
      "clasp"))

(def ^{:dynamic true
       :doc "Name (or absolute path) of the executable `solve` runs: clasp, or clingo, whose
   application takes clasp's flags and writes the same `--outf=2` JSON.  Read once at load
   from `configured-binary`; bind to point `solve` at another install or a test stub."}
  *clasp-binary* (configured-binary))

(def ^:private mode-args
  "The argv tail per mode, in the long spelling clasp and clingo's control both read.  The
   enumerating modes run `--opt-mode=optN`, over optimal models only.  `:label` runs
   `--opt-mode=opt --models=0`, which streams each improving witness, so a run the limit
   stops still has its best one (`:best-effort`) where `optN` yields none before the proof.
   `:sat` is `--models=1`, the first model of a program with no objective."
  {:label                ["--opt-mode=opt"  "--models=0"]
   :sat                  ["--models=1"]
   :all-optima           ["--opt-mode=optN" "--models=0"]
   :classify-true        ["--opt-mode=optN" "--enum-mode=cautious" "--models=0"]
   :classify-supportable ["--opt-mode=optN" "--enum-mode=brave"    "--models=0"]})

(defn mode-flags
  "`mode`'s flags under solve options `opts`, or nil for a mode `mode-args` lacks.
   `:among` sets which models count: `:optimal` (the mode's own), `:all`
   (`--opt-mode=ignore`), or a cost vector (`--opt-mode=enum,…`, every model whose cost is
   lexicographically at most it).  A positive `:models` caps an `:all-optima` enumeration,
   and `:project?` adds `--project`, one model per distinct projection."
  [mode {:keys [among models project?]}]
  (when-let [flags (mode-args mode)]
    (let [opt-mode (cond (contains? #{nil :optimal} among) nil
                         (= :all among)                  "--opt-mode=ignore"
                         :else                           (str "--opt-mode=enum," (str/join "," among)))]
      (cond-> (if opt-mode
                (conj (filterv #(not (str/starts-with? % "--opt-mode=")) flags) opt-mode)
                flags)
        (and (= :all-optima mode) (pos-int? models))
        (->> (mapv #(if (= "--models=0" %) (str "--models=" models) %)))
        project? (conj "--project")))))

(defn optimal-only?
  "Do solve options `opts` count optimal models only, as `mode-flags` reads `:among`?"
  [opts]
  (contains? #{nil :optimal} (:among opts)))

(defn without-optimum
  "`result` of a solve under `opts`, which claims no optimum when `opts` admit non-optimal
   models (`optimal-only?`): its `:optimum` status reads `:sat` and its `:cost` and `:costs`
   are nil.  Under `:among :all` each `:witness-costs` entry is nil too: clasp reports no
   cost when it ignores the objective."
  [result opts]
  (if (optimal-only? opts)
    result
    (cond-> (assoc result :cost nil :costs nil
                   :status (if (= :optimum (:status result)) :sat (:status result)))
      (and (= :all (:among opts)) (:witness-costs result))
      (update :witness-costs #(mapv (constantly nil) %)))))

(defn solve-seconds
  "The seconds one solve under `opts` may run: `:time-limit`, else `config/asp-time-limit`."
  [opts]
  (or (:time-limit opts) (config/asp-time-limit)))

(defn- deadline-ms
  "Milliseconds the JVM waits on one clasp process before killing it: the time limit
   plus the larger of the time limit and 10 s, so 120 s at the default.  Nil when the
   time limit (`solve-seconds`) is 0, which lifts both.  clasp stops itself at
   `--time-limit`, so this fires only on a process that did not."
  [opts]
  (let [n (long (solve-seconds opts))]
    (when (pos? n) (* 1000 (+ n (max n 10))))))

(defn- kill-tree!
  "Kill `p` and every process it started, then wait for `p` to exit.  The descendants
   are read first: once `p` is gone they are no longer its descendants."
  [^Process p]
  (run! #(.destroyForcibly ^ProcessHandle %) (iterator-seq (.iterator (.descendants p))))
  (.destroyForcibly p)
  (.waitFor p))

(defn- run-clasp
  "Run `*clasp-binary*` with `args` and `in` on stdin, under solve options `opts`' time
   limit: `{:exit :out :err}`.

   The process is exec'd directly (no shell), so a missing binary is an IOException,
   never the shell's exit-127 convention.  Both are `:solver-unavailable`: a missing
   binary, and a process still running at `deadline-ms`, which is killed with its
   descendants first.  stdin is written and stdout and stderr read on their own
   threads, so a process that reads nothing or writes more than a pipe buffer cannot
   block the wait."
  [args ^String in opts]
  (let [^Process p (try
                     (.start (ProcessBuilder. ^java.util.List (into [*clasp-binary*] args)))
                     (catch java.io.IOException e
                       (throw (ex-info (str "clasp binary not found: " (pr-str *clasp-binary*)
                                            " — put clasp on PATH, or name it or a clingo"
                                            " executable with VAELII_CLASP_BIN")
                                       {:type :solver-unavailable :binary *clasp-binary*} e))))
        out (future (slurp (.getInputStream p) :encoding "UTF-8"))
        err (future (slurp (.getErrorStream p) :encoding "UTF-8"))
        ms  (deadline-ms opts)]
    ;; a process that exits without reading all of stdin breaks the pipe; its answer is
    ;; on stdout, and the write has nothing to add
    (future (try (with-open [w (io/writer (.getOutputStream p) :encoding "UTF-8")]
                   (.write w in))
                 (catch java.io.IOException _ nil)))
    (let [exited? (try (if ms
                         (.waitFor p (long ms) TimeUnit/MILLISECONDS)
                         (do (.waitFor p) true))
                       (catch Throwable e (kill-tree! p) (throw e)))]
      (when-not exited?
        (kill-tree! p)
        (throw (ex-info (str "clasp did not exit within " ms " ms (VAELII_ASP_TIME_LIMIT"
                             " plus its grace) and was killed")
                        {:type :solver-unavailable :binary *clasp-binary* :deadline-ms ms})))
      {:exit (.exitValue p) :out @out :err @err})))

(defn- invoke-clasp
  "Run clasp with `argv` and `aspif-text` on stdin. Returns parsed JSON.
   Throws when clasp cannot be run or does not exit by its deadline (`run-clasp`), or
   produces unparseable output — UNSAT is a valid outcome, not an error."
  [argv aspif-text opts]
  (let [{:keys [exit out err]} (run-clasp (into ["--outf=2"] argv) aspif-text opts)]
    (if (str/blank? out)
      (throw (ex-info (str "clasp produced no output (exit " exit ") — a solve answers"
                           " JSON on stdout under --outf=2, so an empty body is clasp"
                           " failing to run; its stderr held "
                           (pr-str (str/trim (str err))))
                      {:type :solver-failed :exit exit :err err :argv argv}))
      (try
        (json/parse-string out true)
        (catch Exception e
          (throw (ex-info (str "clasp output does not parse as JSON — a solve runs under"
                               " --outf=2, so a non-JSON body comes from something"
                               " answering in clasp's place; exit " exit ", and the body"
                               " opens " (pr-str (subs out 0 (min 200 (count out)))))
                          {:type :solver-failed :exit exit :out out :err err} e)))))))

(defn- all-witnesses [parsed]
  (or (-> parsed :Call first :Witnesses) []))

(defn- stopped-short?
  "Did clasp stop before its search finished: the solve limit, the time limit, or a
   signal?  The time limit and a signal are flags beside `Result`; the solve limit shows
   only as `More: yes`.  A search that holds every model its `--models` cap asks for says
   `More: yes` by design (`capped?`), so it did not stop short."
  [parsed capped?]
  (boolean (or (some #(= 1 (get parsed (keyword %))) ["TIME LIMIT" "INTERRUPTED"])
               (and (= "yes" (-> parsed :Models :More)) (not capped?)))))

(defn- status-of [parsed capped?]
  (if (stopped-short? parsed capped?)
    :interrupted
    (case (:Result parsed)
      "OPTIMUM FOUND" :optimum
      "SATISFIABLE"   :sat
      "UNSATISFIABLE" :unsat
      :unknown)))

(defn- time-limit-args
  "`--time-limit=N` for a positive time limit under `opts` (`solve-seconds`), nothing for 0."
  [opts]
  (let [n (solve-seconds opts)]
    (when (pos? n) [(str "--time-limit=" n)])))

(defn search-args
  "The flags under which a solve's search is a function of its program alone: one
   thread, clasp's own default seed (1) stated rather than assumed, the optimization
   strategy, and `--solve-limit=N` for a positive solve limit.  The strategy and the limit
   are solve options `opts`' `:opt-strategy` (clasp's spelling) and `:solve-limit`, else
   `config/asp-opt-strategy` and `config/asp-solve-limit`.  The limit counts
   conflicts, so it stops a search at the same point on any machine, where
   `--time-limit` stops it wherever the machine has got to.  In-process clingo's control
   takes the same flags (`vaelii.impl.asp.clingo`)."
  ([] (search-args nil))
  ([{:keys [opt-strategy solve-limit]}]
   (let [n (or solve-limit (config/asp-solve-limit))]
     (cond-> ["--parallel-mode=1" "--seed=1"
              (str "--opt-strategy=" (or opt-strategy (config/asp-opt-strategy)))]
       (pos? n) (conj (str "--solve-limit=" n))))))

(defn- optimum-costs
  "clasp's optimum cost vector, one entry per minimize level, highest first; nil with no
   minimize statement, or for UNSAT."
  [parsed]
  (-> parsed :Models :Costs))

(defn- optimum-cost
  "The highest level's optimum cost, or nil: the result's `:cost`."
  [parsed]
  (first (optimum-costs parsed)))

(defn- value-of [witness]
  (vec (or (:Value witness) [])))

(defn- optimal-witnesses
  "The witnesses whose whole cost vector equals the reported optimum, dropping the
   improving witnesses clasp streams before it.  A multi-level program reports one cost
   per level, so the whole vector is compared."
  [parsed]
  (let [costs (optimum-costs parsed)]
    (if (nil? costs)
      (all-witnesses parsed)
      (filter #(= costs (:Costs %)) (all-witnesses parsed)))))

(defn- objective?
  "Does `aspif-text` hold a minimize statement over at least one literal?  ASPIF writes
  one as `2 <priority> <n> <lit w>…`.  Without one every model costs the same, so a
  search for improving models has nothing to improve and enumerates them all."
  [aspif-text]
  (boolean (re-find #"(?m)^2 -?\d+ [1-9]" aspif-text)))

(defn solve
  "Run clasp on `aspif-text` in `mode` under solve options `opts` (`mode-flags`,
   `search-args`, `time-limit`).  Modes: `:label` one minimum-cost witness, `:sat` the
   first witness, `:all-optima` every minimum-cost witness (every witness `:among` admits),
   and `:classify-true` / `:classify-supportable` the atoms in every / some such witness.

   Returns:
     :status    — :optimum | :sat | :best-effort | :unsat | :interrupted | :unknown
     :atoms     — vector of atom-name strings
     :cost      — optimum cost, `:costs` its vector by level, highest first (nil if none)
     :witnesses — vector of value vectors, `:witness-costs` their costs (`:all-optima`)
     :raw       — full parsed JSON (for diagnostics)

   A `:label` solve runs under `:sat`'s flags for a program with no objective, and for
   `opts` admitting non-optimal models (`optimal-only?`).
   `:interrupted` is a search the solve limit, the time limit or a signal stopped; a
   stopped `:label` or `:sat` solve holding a witness is `:best-effort` instead."
  ([aspif-text mode] (solve aspif-text mode nil))
  ([aspif-text mode opts]
   (let [run     (if (and (= :label mode) (not (and (objective? aspif-text) (optimal-only? opts))))
                   :sat
                   mode)
         argv    (or (mode-flags run opts)
                     (throw (ex-info (str "unknown clasp mode: " (pr-str mode) " — want one of "
                                          (pr-str (vec (sort (keys mode-args)))))
                                     {:type :unknown-option :mismatch :bad-value :mode mode :valid (keys mode-args)})))
         parsed  (invoke-clasp (concat argv (search-args opts) (time-limit-args opts)) aspif-text opts)
         capped? (case run
                   :sat        (boolean (seq (all-witnesses parsed)))
                   :all-optima (and (pos-int? (:models opts))
                                    (>= (long (if (optimal-only? opts)
                                                (or (-> parsed :Models :Optimal) 0)
                                                (count (all-witnesses parsed))))
                                        (long (:models opts))))
                   false)
         status  (status-of parsed capped?)]
     (without-optimum
      (case mode
        (:label :sat)
        (let [best (first (optimal-witnesses parsed))]
          {:status (if (and (= :interrupted status) best) :best-effort status)
           :atoms  (value-of best)
           :cost   (optimum-cost parsed)
           :costs  (optimum-costs parsed)
           :raw    parsed})

        :all-optima
        (let [ws (if (optimal-only? opts) (optimal-witnesses parsed) (all-witnesses parsed))]
          {:status        status
           :atoms         (value-of (first ws))
           :cost          (optimum-cost parsed)
           :costs         (optimum-costs parsed)
           :witnesses     (mapv value-of ws)
           :witness-costs (mapv #(some-> (:Costs %) vec) ws)
           :raw           parsed})

        (:classify-true :classify-supportable)
        ;; the last streamed witness is the converged consequence set
        {:status status
         :atoms  (value-of (last (all-witnesses parsed)))
         :cost   (optimum-cost parsed)
         :costs  (optimum-costs parsed)
         :raw    parsed})
      opts))))

(defn available?
  "True if the clasp binary runs in the current environment."
  []
  (try
    (zero? (long (:exit (run-clasp ["--version"] "" nil))))
    (catch Exception _ false)))
