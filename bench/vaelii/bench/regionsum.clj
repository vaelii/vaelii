;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.regionsum
  "How much region-relabel work phase 3 of `rebuild-tms` does, and whether insertion
  order is why — the number
  `doc/design/persistence-prompts/08-bulk-tms-rebuild.md` items 1 and 2 rest on.

  Phase 3 adds each stored justification through `jtms/add-justification`, which either
  hits the redundant-justification fast path (O(1)) or **resettles** the consequence's
  affected region (`add-just*`, jtms.clj).  The cost of the phase is therefore
  `Σ_j |R_j|` — the region relabelled per add, summed — and whether that sum is ~M (every
  region a singleton, nothing a bulk mode can save) or ≫M (hash-order percolation, so a
  `sort` or a bulk-load protocol helps) is a percolation quantity on the corpus's derivation shape
  that the code does not settle.  This measures it, with **no engine change**:
  `reset-touched!` before each add and `(count (touched tms))` after is exactly that add's
  relabelled region — `relabel-region*` records the region as `:touched`, and the fast
  path records only the lone consequence.  Resetting touched between adds moves no belief
  and no region: `:in`, `:groundable` and `:classes` never read it, so the replay measures
  the real rebuild and only the touched bookkeeping (which this does not report) differs.

  Two orders, per item 2: hash order (`p/justification-ids` returns a `set`) against
  **sorted id order**, a cheap proxy for derivation/topological order since handles are
  allocated as records are derived.  If sorting collapses `Σ|R_j|` toward M, the fix for
  [08] is a `sort` in `rebuild-tms` and a comment, not a protocol change; if it stays ≫M in
  both orders the bulk-load protocol is worth building; if it is ~M in both, phase 3 is already linear
  and [08] is `dropped` carrying this number.

  The corpus is generated **with forward rules** (`:chain? true`) into a `:disk` store and
  reopened cold, so the store holds justifications and the replay builds a real derived
  graph — the case a `:chain? false` figure skips.

  Run: `lein with-profile +bench run -m vaelii.bench.regionsum [sizes…]`
    (default 100000 500000 1000000.  Large sizes want heap:
     `lein with-profile +bench update-in :jvm-opts conj '\"-Xmx24g\"' -- run -m vaelii.bench.regionsum …`)"
  (:require [vaelii.core :as v]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.host.io.generate :as gen]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- plumbing -----------------------------------------------------------

(defn- tmpdir ^String []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-regionsum-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defmacro ^:private ms
  "Milliseconds of evaluating `body` (value discarded)."
  [& body]
  `(let [t0# (System/nanoTime)] ~@body (/ (- (System/nanoTime) t0#) 1e6)))

(defn- gc! [] (dotimes [_ 3] (System/gc) (Thread/sleep 80)))

;; ---- the corpus ---------------------------------------------------------
;; A generated KB with forward rules, so the store holds justifications and the phase-3
;; replay has a derived structure to relabel.  Individuals are held at the fact count so
;; joins stay sparse, and `:max-derivations` caps the cascade near `n`.

(defn- gen-disk!
  "Generate a corpus with rules into a fresh `:disk` store at `dir`, then close it."
  [^String dir n]
  (let [kb (v/open-kb {:records :disk :index :memory :dir dir :recover? false})]
    (v/clear! kb)
    (let [summary (gen/load-into kb {:facts n :rules 6 :individuals n
                                     :types 200 :predicates 40 :chain? true
                                     :max-derivations (quot n 2)})]
      (disk/close-dir! dir)
      summary)))

(defn- reopen-cold
  "A fresh KB over the on-disk store — empty TMS and taxonomy, records durable."
  [^String dir]
  (v/open-kb {:records :disk :index :memory :dir dir :recover? false}))

;; ---- the probe: phase 3, one add at a time, region size read off touched -------

(defn- region-probe
  "Replay `rebuild-tms`'s phases 2 and 3 over a cold reopen, adding justifications in
  `order-fn` order and summing `|R_j|` per add.  Nodes and premises are built first (the
  prerequisite of `add-justification`), exactly as `rebuild-tms` orders them.  Returns
  `{:adds :skipped :sum :singletons :maxregion :ms}` — `:sum` is `Σ|R_j|`, `:singletons`
  the adds whose region was one node (a first derivation with no consequences yet, or a
  fast-path hit), `:maxregion` the largest single region."
  [^String dir order-fn]
  (let [kb      (reopen-cold dir)
        _       (reindex/reindex kb)
        tms     (reasoning/tms kb)
        rec     (:records kb)
        live    (p/sentex-ids rec)
        stored? (fn [h] (or (not (integer? h)) (some? (p/get-sentex rec h))))]
    (doseq [id live] (jtms/ensure-node tms id 0))
    (doseq [id (p/premise-ids rec) :when (contains? live id)]
      (jtms/add-premise tms id (p/premise-strength rec id)))
    (let [ids     (order-fn (p/justification-ids rec))
          adds    (volatile! 0) skipped (volatile! 0)
          sum     (volatile! 0) singles (volatile! 0) mx (volatile! 0)
          loop-ms (ms (doseq [id ids
                              :let [d (p/get-justification rec id)] :when d]
                        (if (and (stored? (:consequence d)) (every? stored? (:antecedents d)))
                          (do (jtms/reset-touched! tms)
                              (jtms/add-justification tms d)
                              (let [r (count (jtms/touched tms))]
                                (vswap! adds inc)
                                (vswap! sum + r)
                                (when (= 1 r) (vswap! singles inc))
                                (when (> r @mx) (vreset! mx r))))
                          (vswap! skipped inc))))]
      {:adds @adds :skipped @skipped :sum @sum
       :singletons @singles :maxregion @mx :ms loop-ms})))

;; ---- reporting ----------------------------------------------------------

(defn- report-orders
  "Run the probe in both orders over `dir` and print the Σ|R_j| table."
  [^String dir]
  (gc!)
  (let [h (region-probe dir seq)
        _ (gc!)
        s (region-probe dir sort)]
    (println (format "  justifications added: %,d  (skipped unrooted: %,d)"
                     (long (:adds h)) (long (:skipped h))))
    (println (format "%-8s %16s %10s %12s %12s %12s"
                     "order" "Σ|R_j|" "Σ/M" "singletons" "max|R_j|" "loop ms*"))
    (doseq [[label r] [["hash" h] ["sorted" s]]]
      (println (format "%-8s %16d %10.3f %11d%% %12d %12.1f"
                       label (long (:sum r))
                       (/ (double (:sum r)) (max 1.0 (double (:adds r))))
                       (long (Math/round (* 100.0 (/ (double (:singletons r))
                                                     (max 1.0 (double (:adds r)))))))
                       (long (:maxregion r)) (double (:ms r)))))
    (println (format "  hash/sorted Σ|R_j|: %.2f×  (>1 ⇒ id order collapses region work — [08] item 2)"
                     (/ (double (:sum h)) (max 1.0 (double (:sum s))))))
    (println "  * loop ms carries a reset-touched! per add (measurement overhead); the decider is Σ/M, not ms")))

(defn- run-size [n]
  (let [dir (tmpdir)]
    (try
      (let [summary (gen-disk! dir n)]
        (println (format "%n=== %,d facts → %,d records, %,d derived%s ==="
                         (long n) (long (:stored summary)) (long (:derived summary 0))
                         (if (:truncated? summary) " (chain truncated)" "")))
        (report-orders dir))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

(defn- realkb-run
  "Measure Σ|R_j| over an **existing** `:disk` store — the real corpus's own derivation
  shape, which is what the percolation quantity actually depends on.  Opens read-only for
  the tms rebuild (the durable records are never written; the index is rebuilt in RAM), so
  it does not disturb the store.  Do not run against a store another process holds open."
  [^String dir]
  (when-not dir
    (throw (ex-info "regionsum realkb needs a store directory" {:usage "run -m vaelii.bench.regionsum realkb <dir>"})))
  (let [kb   (reopen-cold dir)
        recs (count (p/sentex-ids (:records kb)))]
    (disk/close-dir! dir)
    (println (format "%n=== real KB at %s → %,d records ===" dir (long recs)))
    (report-orders dir)))

;; ---- main ---------------------------------------------------------------

(defn -main [& args]
  (println "region-sum — phase-3 Σ|affected-region| by insertion order")
  (if (= "realkb" (first args))
    (realkb-run (second args))
    (let [sizes (if (seq args) (map parse-long args) [100000 500000 1000000])]
      (doseq [n sizes] (run-size n))))
  (shutdown-agents)
  (System/exit 0))
