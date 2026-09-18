;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.scale
  "Measure the walls the index-scale study left unmeasured, above all the **JTMS**.

  `vaelii.bench.memory` loads through `kb/create-sentex` (put + index, no truth
  maintenance), so it never builds the JTMS and never measured it.  This harness loads
  through the **real `vaelii.core/assert` path**, so every fact becomes a JTMS premise
  node — and then reads the retained object-graph size of each of a KB's four resident
  components (index / records / JTMS / taxonomy) with jol.

  **Two kinds of number, and only one is trustworthy on a shared machine.**

  - **RAM by component (trusted).**  jol's `GraphLayout` walks an object subgraph and
    sums shallow sizes — a structural reading that does not depend on wall-clock, so a
    concurrent load elsewhere on the box cannot move it.  The per-component bytes/fact
    are linear, so a modest N extrapolates to 100M.  This is the deliverable.
  - **Wall-clock (untrusted under contention).**  Load throughput, reindex, and recover
    are timed but are meaningless while another process contends for CPU/RAM.  They print
    under an UNTRUSTED banner and must be re-run on an idle machine.

  Component objects are reached through the concrete backends: the index is the
  `MemoryKvBackend`'s state map, records the `MemoryRecordStore`'s, and the JTMS /
  taxonomy are their state atoms.  Per-component sizes double-count structure shared
  between components (interned symbols above all), so a deduped combined total is
  reported alongside — the gap is the shared structure.

  Run: `lein bench-scale [premise-facts] [rule-facts] [reference|dense]`
  (defaults 200000 50000 reference).  The TMS rep is the third arg, so
  prompt 09 takes both representations by invoking twice — heap isolation
  per rep is why it is two JVMs, not two runs in one.  Spaces auto-size to
  the fact count (≥20 / ≥22, clear of the test block 14-15 and the other
  bench harnesses' 9/10), so 1M does not load at load-factor 1."
  (:require [clojure.string :as str]
            [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [org.openjdk.jol.info GraphLayout]))

;; ---- generation (well-formed for the real assert path) ------------------
;; Predicates lowercase-initial (camelCase), individuals Capitalized, contexts
;; `Cx`-prefixed CapitalCamel — the naming invariants v/assert enforces.

(defn- gen-fact
  "One synthetic fact `[sentence context]`: a Zipf predicate, 2-3 Zipf-individual
  arguments, and — with probability `compound-frac` — a compound last argument
  `(qtyFn <int> <unit>)`, so the structural trie is exercised."
  [^java.util.Random rng {:keys [preds inds units ctxs pred-cum ind-cum compound-frac]}]
  (let [pred    (nth preds (zipf-sample pred-cum rng))
        ctx     (nth ctxs (.nextInt rng (count ctxs)))
        arity   (+ 2 (.nextInt rng 2))
        a       (nth inds (zipf-sample ind-cum rng))
        rest-as (repeatedly (dec arity) #(nth inds (zipf-sample ind-cum rng)))
        rest-as (if (< (.nextDouble rng) compound-frac)
                  (concat (butlast rest-as)
                          [(list 'qtyFn (.nextInt rng 1000)
                                 (nth units (.nextInt rng (count units))))])
                  rest-as)]
    [(apply list pred a rest-as) ctx]))

;; ---- measurement primitives ---------------------------------------------

(defn- retained
  "Retained heap of the reachable object graph rooted at `objs`, in bytes (jol).  When
  several roots are passed, structure reachable from more than one is counted once —
  a deduped total."
  ^long [objs]
  (.totalSize ^GraphLayout (GraphLayout/parseInstance (into-array Object objs))))

(defn- gc! []
  (dotimes [_ 5] (System/gc) (System/runFinalization) (Thread/sleep 40)))

(defn- components
  "The four resident components' root objects, reached through the concrete backends."
  [kb]
  {:index    @(:state (:backend (:index kb)))
   :records  @(:state (:records kb))
   :jtms     (reasoning/tms kb)
   :taxonomy @(reasoning/taxonomy kb)})

(defn- ms [t0] (/ (- (System/nanoTime) t0) 1e6))

;; ---- loading (real assert path) -----------------------------------------

(defn- load-premises!
  "Assert `n` facts as premises through v/assert with {:chain? false} — no rules, so
  the JTMS ends as pure premise nodes (the dominant term at 100M).  Duplicate Zipf
  draws find-or-create to one handle, so the *stored* count is what bytes/fact divides
  by, not n."
  [kb ^java.util.Random rng {:keys [n] :as cfg}]
  (let [sample (java.util.ArrayList.)
        t0     (System/nanoTime)]
    (dotimes [i n]
      (let [[s c] (gen-fact rng cfg)]
        (v/assert kb s c {:chain? false})
        (when (zero? (mod i 500)) (.add sample [s c]))
        (when (and (pos? i) (zero? (mod i 50000)))
          (println (format "  … %,d asserts (%.0f/s, untrusted)" i
                           (/ i (/ (- (System/nanoTime) t0) 1e9)))))))
    {:ms (ms t0) :sample (vec sample)}))

(defn- load-with-rule!
  "Assert one forward rule `(relA ?x ?y) ⇒ (relB ?x ?y)` and `n` `relA` facts with
  chaining ON, so each distinct fact derives a `relB` twin — a justification
  per derivation.  Isolates the per-justification JTMS cost the premise-only run cannot see."
  [kb ^java.util.Random rng {:keys [n inds ind-cum ctxs]}]
  (v/assert-rule kb ['(relA ?x ?y)] '(relB ?x ?y) (first ctxs) {:direction :forward})
  (let [t0 (System/nanoTime)]
    (dotimes [_ n]
      (let [a (nth inds (zipf-sample ind-cum rng))
            b (nth inds (zipf-sample ind-cum rng))]
        (v/assert kb (list 'relA a b) (first ctxs))))
    {:ms (ms t0)}))

;; ---- report -------------------------------------------------------------

(def ^:private GiB (* 1024.0 1024 1024))

(defn- report-components [kb label]
  (let [stored (count (p/sentex-ids (:records kb)))
        dedns  (count (p/justification-ids (:records kb)))
        ;; through the public accessors, so the harness reads either TMS
        ;; representation without materializing a snapshot of the dense one.
        ;; The justification count is the network's own, deliberately not the
        ;; store's `dedns` above — the two agreeing is the thing worth seeing.
        nodes  (count (jtms/datums (reasoning/tms kb)))
        justs  (count (jtms/justifications (reasoning/tms kb)))
        comps  (components kb)
        sizes  (into {} (map (fn [[k o]] [k (retained [o])])) comps)
        combined (retained (vals comps))
        whole    (retained [kb])
        per    #(double (/ % (max 1 stored)))
        at100_m #(/ (* (per %) 1e8) GiB)]
    (println)
    (println (format "── %s ── %,d stored sentexes, %,d justifications | JTMS %,d nodes, %,d justifications"
                     label stored dedns nodes justs))
    (println (format "%-14s %14s %14s %16s" "component" "MB" "bytes/fact" "@100M (GB)"))
    (println (apply str (repeat 62 \-)))
    (doseq [k [:index :records :jtms :taxonomy]]
      (let [b (sizes k)]
        (println (format "%-14s %14.1f %14.0f %16.1f"
                         (name k) (/ b 1048576.0) (per b) (at100_m b)))))
    (let [sum (reduce + (vals sizes))]
      (println (apply str (repeat 62 \-)))
      (println (format "%-14s %14.1f %14.0f %16.1f" "sum-of-parts" (/ sum 1048576.0) (per sum) (at100_m sum)))
      (println (format "%-14s %14.1f %14.0f %16.1f  (shared structure counted once)"
                       "deduped total" (/ combined 1048576.0) (per combined) (at100_m combined)))
      (println (format "%-14s %14.1f %14.0f %16.1f  (whole KB graph)"
                       "whole-kb (jol)" (/ whole 1048576.0) (per whole) (at100_m whole))))
    {:stored stored :dedns dedns :nodes nodes :justs justs :sizes sizes :jtms (:jtms sizes)}))

(defn- config [n]
  (let [P (max 50 (quot n 400))
        M (max 1000 (quot n 4))]
    {:n n
     :preds (u/terms "pr" P)
     :inds  (u/terms "Ind" M)
     :units (u/terms "unit" 10)
     :ctxs  (mapv #(symbol (str "CxCtx" %)) (range 8))
     :pred-cum (u/zipf-cumulative P 1.2)
     :ind-cum  (u/zipf-cumulative M 1.0)
     :compound-frac 0.1}))

(defn- space-for
  "The smallest hash-space `:space` that holds `n` facts with ≈2× headroom, floored
  at `floor` so the small defaults are unchanged.  `:space` is log2 of the bucket
  count, so a load at load-factor 1 (space = ⌈log2 n⌉) is what this avoids."
  [n floor]
  (max floor (+ 1 (- 64 (Long/numberOfLeadingZeros (dec (long (max 1 n))))))))

(defn -main [& args]
  (let [nums   (keep #(try (Long/parseLong %) (catch Exception _ nil)) args)
        tms    (some #{:reference :dense} (map #(keyword (str/lower-case %)) args))
        tms    (or tms :reference)
        n      (or (first nums) 200000)
        rn     (or (second nums) 50000)
        spaceA (space-for n 20)
        spaceB (space-for (* 2 rn) 22)          ; Run B's rule derives a twin per fact
        xmx    (/ (.maxMemory (Runtime/getRuntime)) GiB)]
    (println (format "vaelii scale harness (Phase 0) — %,d premise facts, %,d rule facts — TMS :%s — -Xmx≈%.1f GB"
                     n rn (name tms) xmx))
    (println (format "spaces: Run A :space %d, Run B :space %d" spaceA spaceB))
    (println "RAM-by-component is jol retained size: structural, contention-immune → TRUSTED.")
    (println "Wall-clock (load/s, reindex, recover) is UNTRUSTED while another load runs on this box.")

    ;; ---- Run A: premises only (the clean per-premise-node JTMS cost) ----
    (let [kb  (v/open-kb {:backend :memory :space spaceA :tms tms :recover? false})
          _   (do (p/clear-records! (:records kb)) (p/clear-index! (:index kb)))
          rng (java.util.Random. 42)
          {lms :ms} (load-premises! kb rng (config n))]
      (gc!)
      (let [a (report-components kb "Run A: premises only (no rules)")]
        ;; ---- untrusted wall-clock, on the same populated KB ----
        (println)
        (println "── wall-clock (UNTRUSTED under contention; re-run solo) ──")
        (println (format "  load          : %.1f s  (%,.0f facts/s)" (/ lms 1000.0) (/ (:stored a) (/ lms 1000.0))))
        (let [t0 (System/nanoTime) r (v/reindex kb)] (println (format "  reindex index : %.1f s  (%s)" (/ (ms t0) 1000.0) (pr-str r))))
        (let [t0 (System/nanoTime)] (v/recover kb)   (println (format "  recover tms+tax: %.1f s" (/ (ms t0) 1000.0))))))

    ;; ---- Run B: rules fire (the per-justification / justification cost) ----
    (let [kb  (v/open-kb {:backend :memory :space spaceB :tms tms :recover? false})
          _   (do (p/clear-records! (:records kb)) (p/clear-index! (:index kb)))
          rng (java.util.Random. 7)
          {lms :ms} (load-with-rule! kb rng (config rn))]
      (gc!)
      (let [b (report-components kb "Run B: one forward rule firing per fact")]
        (println)
        (println (format "  chained load  : %.1f s  (%,.0f facts/s, UNTRUSTED)" (/ lms 1000.0) (/ rn (/ lms 1000.0))))
        (println (format "  JTMS per (node+just): ≈ %.0f bytes  over %,d nodes + %,d justs"
                         (double (/ (:jtms b) (max 1 (+ (:nodes b) (:justs b))))) (:nodes b) (:justs b)))))
    (shutdown-agents)))
