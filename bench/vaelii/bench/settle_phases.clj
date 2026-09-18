;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.settle-phases
  "Where a bulk settle spends its **wall clock**, attributed to the four cost centres —
  the reading `settle-parallelism.md`'s candidates are each argued against, and which
  `vaelii.impl.settle-phases` collects.

  Two shapes, the ones prompts 02 and 03 divide:

  * **the additive load** — one forward rule and `n` facts, chaining ON, so the settle
    machinery runs per assert: a stream of small relabels, a chain firing per fact, and
    the discovery/resolution the sparse contradictions cost.
  * **the replay recover** — `recover` over the loaded store, which rebuilds the network
    from stored justifications with no chaining at all.  On a durable store the
    justification fetch lands in `:belief` (the replay's driver), which is the phase a
    memory backend has nothing in.

  Both are read on `:memory` and on `:disk-log`, since a durable store's fetch cost lands
  in a different centre than the memory backend's.

  **The reading is a distribution, not a mean.**  One root-edge move relabels the whole
  graph and a leaf edge moves nothing (`settle_region_cost_test`), so the per-settle
  records carry each centre's self-time and the settle's region size, and the report
  prints median, p95 and the costliest settle beside the run split — the discipline
  `docs/profile.md` holds a design-cited arm to.

  Run: `lein bench-settlephases [n] [memory|disk|both]`
  (defaults 200000 both).  Wall-clock is UNTRUSTED under contention: the split (a ratio
  between centres measured in one run) survives a shared box, but the absolute
  millisecond does not — re-run the 1M/10M loads solo, as `scale-100m.md` Phase 0 does.

  This is the caller `settle-phases` has in mind when its docstring says nothing there
  formats: the percentiles and the split are taken here."
  (:require [clojure.string :as str]
            [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- generation (well-formed for the real assert path) ------------------
;; The additive load fires one forward rule per `relA` fact and sprinkles a fixed,
;; non-scaling number of `P`/`¬P` default pairs, so discovery and resolution are exercised
;; without the standing set growing with `n` — a real corpus's contradictions are sparse,
;; and a set that scaled with `n` would make discovery quadratic and unrepresentative.

(def ^:private centres [:belief :discovery :resolution :chaining :finish :glue :outside])

(defn- config [n]
  (let [M (max 1000 (quot n 4))]
    {:n n
     :inds    (u/terms "Ind" M)
     :ctxs    (mapv #(symbol (str "CxCtx" %)) (range 8))
     :ind-cum (u/zipf-cumulative M 1.0)}))

(defn- gen-facts
  "Pre-generate `n` `relA` facts as `[sentence context]`, deterministic Zipf, into a
  vector — so the generation is out of the timed window and `:outside` is the assert
  path's own cost (canon, checks, index, minting), not the harness's."
  [^java.util.Random rng {:keys [n inds ctxs ind-cum]}]
  (let [out (object-array n)]
    (dotimes [i n]
      (let [a (nth inds (zipf-sample ind-cum rng))
            b (nth inds (zipf-sample ind-cum rng))
            c (nth ctxs (.nextInt rng (count ctxs)))]
        (aset out i [(list 'relA a b) c])))
    (vec out)))

;; ---- measurement --------------------------------------------------------

(defn- ms ^double [^long nanos] (/ nanos 1e6))

(defn- pct
  "The `p`-th percentile of a sorted long vector (nearest-rank), 0 for empty."
  ^long [^longs sorted p]
  (let [n (alength sorted)]
    (if (zero? n) 0
        (aget sorted (min (dec n) (long (Math/floor (* (/ (double p) 100.0) n))))))))

(defn- report
  "Print one reading: the run split by centre, then the per-settle distribution."
  [label {:keys [run settles]}]
  (let [total (double (reduce + 0 (vals run)))]
    (println)
    (println (format "── %s ── %,d settles, %.1f ms total (UNTRUSTED absolute)"
                     label (count settles) (ms (long total))))
    (println (format "%-11s %12s %8s %12s %12s" "centre" "run ms" "run %" "p50 ms" "p95 ms"))
    (println (apply str (repeat 58 \-)))
    (doseq [c centres]
      (let [rc  (long (get run c 0))
            per (long-array (sort (map (fn [s] (long (get (:nanos s) c 0))) settles)))]
        (when (or (pos? rc) (pos? (pct per 95)))
          (println (format "%-11s %12.1f %7.1f%% %12.3f %12.3f"
                           (name c) (ms rc) (* 100.0 (/ rc total))
                           (ms (pct per 50)) (ms (pct per 95)))))))
    (println (apply str (repeat 58 \-)))
    (println (format "%-11s %12.1f %7.1f%%" "TOTAL" (ms (long total)) 100.0))
    ;; region-size distribution and the costliest settle, the case a mean hides
    (let [regions (long-array (sort (map #(long (:region %)) settles)))]
      (println (format "region size: p50=%d  p95=%d  max=%d"
                       (pct regions 50) (pct regions 95) (pct regions 100))))
    (when (seq settles)
      (let [top (apply max-key :total settles)]
        (println (format "costliest settle: total=%.2fms region=%d passes=%d  %s"
                         (ms (:total top)) (:region top) (:passes top)
                         (str/join " " (for [c centres
                                             :let [nv (long (get (:nanos top) c 0))]
                                             :when (pos? nv)]
                                         (format "%s=%.2f" (name c) (ms nv))))))))))

(defn- measure [f]
  (phases/start)
  (f)
  (phases/stop))

;; ---- loading (real assert path) -----------------------------------------

(defn- load-additive!
  "Assert the eight context edges so a fact sees the rule, one forward rule, `defeats`
  standing monotonic contradictions, and the `n` pre-generated `relA` facts with chaining
  ON — the stream of per-assert settles a bulk load runs.  The rule sits in `CxUniverse`
  and the facts in its `genlCx` descendants, so each `relA` fires the rule and derives a
  `relB`.

  `defeats` is 0 for the clean additive load (chaining-dominated).  A positive count is
  the **contradiction-density** knob: a standing monotonic defeat is revived by
  `clear-defeats!` and re-resolved on *every* later settle, so `defeats` of them turn each
  assert's settle into an O(`defeats`) discovery-and-resolution pass — the cost the
  clash-discovery candidate targets, measured against a count."
  [kb ctxs defeats facts]
  (doseq [c ctxs] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse {}))
  (v/assert-rule kb ['(relA ?x ?y)] '(relB ?x ?y) 'CxUniverse {:direction :forward})
  (dotimes [i defeats]
    (v/assert kb (list 'spq (symbol (str "SpNeg" i))) 'CxUniverse {})
    (v/assert kb (list 'not (list 'spq (symbol (str "SpNeg" i)))) 'CxUniverse {:strength :monotonic}))
  (doseq [[s c] facts] (v/assert kb s c {})))

(defn- run-backend [n defeats backend]
  (let [dir  (when (= backend :disk-log)
               (str (System/getProperty "java.io.tmpdir") "/vaelii-phases-"
                    (System/currentTimeMillis)))
        opts (cond-> {:backend backend :space (max 18 (+ 2 (- 64 (Long/numberOfLeadingZeros (dec (long n))))))}
               dir (assoc :dir dir))
        rng  (java.util.Random. 42)
        cfg  (config n)
        _    (println (format "\n### backend %s — generating %,d facts…" (name backend) n))
        facts (gen-facts rng cfg)
        kb   (v/open-kb opts)]
    (println (format "### loading (additive, chaining on, %d standing defeats)…" defeats))
    (report (format "LOAD %s · %s · n=%,d"
                    (if (pos? defeats) (str "clash·" defeats "defeats") "additive")
                    (name backend) n)
            (measure #(load-additive! kb (:ctxs cfg) defeats facts)))
    (println (format "    stored: %,d sentexes, %,d justifications, %,d JTMS nodes"
                     (count (p/sentex-ids (:records kb)))
                     (count (p/justification-ids (:records kb)))
                     (count (jtms/datums (reasoning/tms kb)))))
    ;; ---- the replay shape: recover the loaded store ----
    (println (format "### recovering (replay, no chaining)…"))
    (if dir
      ;; a durable store: reopen and recover, so the justification fetch is a real disk read
      (let [kb2 (v/open-kb (assoc opts :recover? false))]
        (report (format "RECOVER replay · %s · n=%,d" (name backend) n)
                (measure #(v/recover kb2))))
      (report (format "RECOVER replay · %s · n=%,d" (name backend) n)
              (measure #(v/recover kb))))))

(defn -main
  "`lein bench-settlephases [n] [memory|disk|both] [defeats=<k>]`.  Loads the clean additive
  shape by default; `defeats=<k>` seeds `k` standing contradictions to read the
  contradiction-density shape."
  [& args]
  (let [n       (or (some #(try (Long/parseLong %) (catch Exception _ nil)) args) 200000)
        which   (some #{"memory" "disk" "both"} (map str/lower-case args))
        defeats (or (some #(when-let [m (re-matches #"defeats=(\d+)" %)] (Long/parseLong (second m))) args) 0)
        backs   (case which
                  "memory" [:memory]
                  "disk"   [:disk-log]
                  [:memory :disk-log])]
    (println (format "vaelii settle-phase harness — n=%,d — backends %s — defeats %d — -Xmx≈%.1f GB"
                     n (str/join "," (map name backs)) defeats
                     (/ (.maxMemory (Runtime/getRuntime)) (* 1024.0 1024 1024))))
    (println "Split (ratio between centres in one run) is contention-immune; absolute ms is not.")
    (doseq [b backs] (run-backend n defeats b))
    (println "\n=== settle-phase harness complete ===")
    (shutdown-agents)))
