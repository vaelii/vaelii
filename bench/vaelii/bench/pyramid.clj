;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.pyramid
  "W4 join-pyramid driver at 1k — a faithful in-repo replica of the field
  benchmark cell (`run-w4`): the 4-rule pyramid a←b1,b2 / b1←c1,c2 / b2←c3,c4 /
  c1←d1,d2 over the seeded base relations, forward-chained to fixpoint
  (semi-naive), then the full `a` extent read off the stored records and gated
  against the corpus's a_ext.sha1.

  Modes:
    time [reps]     — run the workload `reps` times in one JVM, one line per run
    verify <path>   — one run, then a handle-free content dump to <path>
    profile         — one warmup run, then a run with clj-async-profiler around
                      the timed section (needs the +repl profile on the classpath)
  Any mode takes flag suffixes, composable: `-ref` runs the placement fast paths
  off (that A/B's reference side), `-nosup` enumerates every trigger of a firing
  rather than one (the duplicate-suppression A/B), `-rete` matches through the alpha
  memories (the matcher A/B) — `time-ref`, `verify-nosup`, `time-rete-ref`.

  `VAELII_PYRAMID_CORPUS` names the corpus directory (the one holding
  `vaelii.txt` and `expected/a_ext.sha1`) and is required — see `corpus-dir`.

  Run: VAELII_PYRAMID_CORPUS=<corpus>/join.1k \\
       lein with-profile +bench run -m vaelii.bench.pyramid time 3

  The reading needs C2, and project.clj's top-level `:jvm-opts` declares it:
  leiningen's `:base` profile caps a project JVM at `-XX:TieredStopAtLevel=1`
  when LEIN_JVM_OPTS names \"Tiered\", and the declared vector replaces `:base`'s
  copy.  A run that names `-XX:TieredStopAtLevel=4` by hand no longer changes the
  compiler level.

  Heap: join.1k's fixpoint is ~400 MB resident (the `heap-used-mb` figure each
  `time` line prints).  join.10k derives ~2.7M `a` pairs plus intermediates and its
  fixpoint does NOT fit `-Xmx40g` on the boxed `:memory` pair — pass
  `-XX:+ExitOnOutOfMemoryError` on any big run, or an OOM is ~19 minutes of GC
  thrash before the same death."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rete :as rete]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import (java.security MessageDigest)))

(defn- corpus-dir
  "The join.1k corpus directory, named by `VAELII_PYRAMID_CORPUS`.

  Required, with no fallback. The corpus is a field-harness artifact — it is not
  in this repo and there is no path inside it that would find one, so a default
  could only be an absolute path naming whoever wrote it. Resolved per call
  rather than at load, so requiring this namespace without the variable set is
  fine and only a run needs it."
  []
  (or (System/getenv "VAELII_PYRAMID_CORPUS")
      (throw (ex-info (str "VAELII_PYRAMID_CORPUS is unset. Set it to the join.1k "
                           "corpus directory — the one holding vaelii.txt and "
                           "expected/a_ext.sha1.")
                      {:env "VAELII_PYRAMID_CORPUS"}))))

(def ^:private bench-context 'CxFieldBench)

(defn- sha1-of-lines
  "SHA-1 hex of the canonical form of `lines` — identical to the field harness's
  refanswers/sha1-of-lines (dedup, ASCII sort, newline-terminated)."
  [lines]
  (let [md (MessageDigest/getInstance "SHA-1")]
    (doseq [^String line (sort (distinct (seq lines)))]
      (.update md (.getBytes (str line "\n") "US-ASCII")))
    (format "%040x" (BigInteger. 1 (.digest md)))))

(defn- fresh-kb []
  (let [kb (v/open-kb {:backend :memory :space 44
                       :recover? false})]
    (p/clear-records! (:records kb))
    (p/clear-index! (:index kb))
    kb))

(defn- load-corpus! [kb]
  (with-open [r (io/reader (str (corpus-dir) "/vaelii.txt"))]
    (doseq [line (line-seq r) :when (not (str/blank? line))]
      (v/assert kb (edn/read-string line) bench-context {:chain? false}))))

(defn- add-rules! [kb]
  (doseq [[head l1 l2] '[[c1 d1 d2] [b1 c1 c2] [b2 c3 c4] [a b1 b2]]]
    (v/assert-rule kb [(list l1 '?x '?z) (list l2 '?z '?y)] (list head '?x '?y)
                   bench-context {:direction :forward :chain? false})))

(defn- timed-section
  "The cell's timed region: fixpoint + full `a` extent read.  Returns the lines."
  [kb]
  (v/forward-chain kb {:max-depth 1000000 :max-derivations 1000000000})
  (into [] (comp (map :sentence) (map (fn [[_ x y]] (str x " " y))))
        (v/sentexes-with-functor kb 'a)))

(def ^:private rete?
  "Whether a run tracks the KB into the alpha memories and matches through them
  (`rete/rete-match-pattern` root-bound over `chain/*matcher*` by `-main`'s `-rete`
  flag); tracking is per KB, so `run-once` consults this after the corpus loads."
  (atom false))

(defn run-once
  "One full cell run.  `around` (fn [thunk] -> result) wraps the timed section —
  identity for a plain run, the profiler for a profiled one."
  ([] (run-once (fn [t] (t))))
  ([around]
   (let [kb  (fresh-kb)
         _   (load-corpus! kb)
         _   (add-rules! kb)
         _   (when @rete? (rete/track! kb))
         exp (str/trim (slurp (str (corpus-dir) "/expected/a_ext.sha1")))
         t0  (System/nanoTime)
         lines (around #(timed-section kb))
         ms  (/ (- (System/nanoTime) t0) 1e6)
         got (sha1-of-lines lines)]
     {:kb kb :ms ms :a-count (count (distinct lines)) :pass (= exp got)
      :got got :exp exp})))

(defn- content-dump
  "The fixpoint's whole content, handle-free: every stored sentex as
  [sentence context truth strength believed?], every justification as
  [consequence-content informant-content antecedent-content-set strength], both
  sorted by print form.  Two runs that derived the same knowledge print the same
  file whatever handles they allocated."
  [kb]
  (let [recs (:records kb)
        tms  (reasoning/tms kb)
        sent (fn [h] (let [s (p/get-sentex recs h)] [(:sentence s) (:context s)]))
        sxs  (sort-by pr-str
                      (map (fn [id]
                             (let [s (p/get-sentex recs id)]
                               [(:sentence s) (:context s) (:truth s) (:strength s)
                                (boolean (jtms/in? tms id))]))
                           (p/sentex-ids recs)))
        js   (sort-by pr-str
                      (map (fn [j]
                             [(sent (:consequence j))
                              (if (integer? (:informant j)) (sent (:informant j)) (:informant j))
                              (set (map sent (:antecedents j)))
                              (:strength j)])
                           (jtms/justifications tms)))]
    (with-out-str
      (println "== sentexes" (count sxs))
      (doseq [s sxs] (prn s))
      (println "== justifications" (count js))
      (doseq [j js] (prn j))
      (println "== blocked" (count (jtms/blocked tms))
               "defeated" (count (jtms/defeated tms))
               "superseded" (count (jtms/superseded tms))))))

(defn -main [& [mode reps]]
  ;; flags suffix the mode and compose (`time-rete-ref`): `-ref` runs the placement
  ;; fast paths off (`observe/*chain-fast-paths*` root-bound false — the reference
  ;; side of that A/B); `-nosup` enumerates every trigger of a firing
  ;; (`chain/*suppress-duplicate-firings*` root-bound false — the reference side of
  ;; that one); `-rete` matches through the alpha memories
  ;; (`chain/*matcher*` root-bound to `rete/rete-match-pattern`, each KB tracked
  ;; after its corpus loads — the matcher A/B)
  (let [parts (str/split (or mode "time") #"-")
        flags (set (rest parts))
        mode  (first parts)]
    (when (flags "ref")
      (alter-var-root #'observe/*chain-fast-paths* (constantly false)))
    (when (flags "nosup")
      (alter-var-root #'chain/*suppress-duplicate-firings* (constantly false)))
    (when (flags "rete")
      (reset! rete? true)
      (alter-var-root #'chain/*matcher* (constantly rete/rete-match-pattern)))
    (case mode
      "time"
      (dotimes [i (or (some-> reps parse-long) 1)]
        (let [{:keys [kb ms a-count pass]} (run-once)
              _    (System/gc)
              rt   (Runtime/getRuntime)
              used (quot (- (.totalMemory rt) (.freeMemory rt)) (* 1024 1024))]
          ;; the KB is still reachable here, so post-gc used heap is the fixpoint's
          ;; resident footprint — records, index, TMS — not allocation churn
          (println (format "PYRAMID run=%d ms=%.1f a-count=%d gate=%s heap-used-mb=%d"
                           i ms a-count pass used))
          (identity kb)))

      ;; verify <path>: one run, then the handle-free content dump to <path> — diff
      ;; a plain one against a `-ref` one to prove the fixpoints identical.
      "verify"
      (let [{:keys [kb pass]} (run-once)]
        (spit reps (content-dump kb))
        (println (format "PYRAMID verify gate=%s dump=%s" pass reps)))

      "profile"
      (let [start (requiring-resolve 'clj-async-profiler.core/start)
            stop  (requiring-resolve 'clj-async-profiler.core/stop)
            warm  (run-once)]
        (println (format "PYRAMID warmup ms=%.1f gate=%s" (:ms warm) (:pass warm)))
        (let [r (run-once (fn [t]
                            (start {:event :cpu})
                            (let [v (t)]
                              (println "PYRAMID collapsed:"
                                       (str (stop {:generate-flamegraph? false})))
                              v)))]
          (println (format "PYRAMID profiled ms=%.1f a-count=%d gate=%s"
                           (:ms r) (:a-count r) (:pass r))))))
    (shutdown-agents)
    (System/exit 0)))
