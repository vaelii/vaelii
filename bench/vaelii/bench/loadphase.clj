;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.loadphase
  "Where a bulk load's wall clock goes, phase by phase.

  `bulk-assert-facts!` already turns four things off — the definitional checks, the
  `arg` store query, the dedup trie-walk and provenance — plus `{:chain? false}` and
  one deferred settle.  What is left is the write path itself, and nothing said which
  part of it costs what.  This is the instrument that says.

  **Method: a cumulative peel.**  The same corpus is loaded through the same entry point
  repeatedly, each run with one more phase stubbed out, from the outside in.  The
  difference between two consecutive runs is that phase's cost, and the deltas sum to
  the baseline by construction — so there is no unattributed residue to argue about.
  The order is chosen so a phase is peeled *before* anything it reads: the negation
  coincidence probe reads the index, so it goes first; the index write is peeled before
  the record write, which is peeled before canonicalization.

  Every stub is a `with-redefs-fn` of a var the load path calls, so the un-stubbed
  phases run their real code — this measures the engine, not a model of it.  A peeled
  run stores less than a real one, which is the point; `verify!` is the run that checks
  the unpeeled entry point still holds its contract on the same corpus.

  **The index sub-split** is the measurement the count-maintenance suspect stands or
  falls on.  The trie counter at every prefix is a write per level per fact, and the
  only defensible way to price it is to make it free: a `KvBackend` decorator drops the
  `:increment` ops out of every batch and leaves the rest alone.  A second decorator
  drops the whole batch, which prices the key-stream computation against the backend
  apply.  Both keep `index-sentex` running its real code.

  **The guard arm** is the third mode, and it prices one decision rather than a phase:
  `kb/note-opposed!`'s guard against posting a body that is opposed at neither end.  It
  alternates the two arms A-B-B-A inside one JVM, because a JVM loading the same corpus a
  dozen times drifts and a fixed A-then-B order reports that drift as the difference.

  Run: `lein bench-loadphase [n] [repeats] [full|guard]`  (default 200000, 1, full)."
  (:require [vaelii.core :as v]
            [vaelii.impl.assert-entry :as entry]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

(def ^:private bench-context 'CxLoadPhase)
(def ^:private edge-pred 'benchEdge)

;; ---- the corpus ---------------------------------------------------------
;; The shape the field harness loads: a fan-out-8 edge set over n/8 nodes, every fact
;; ground, well-formed and pairwise distinct — the two preconditions bulk mode trades
;; on.  Held in memory rather than streamed, so no EDN parse sits inside the
;; measurement; the decomposition is of the assert path, not of a file reader.

(defn- corpus [^long n]
  (let [m     (max 1 (quot n 8))
        nodes (object-array m)]
    (dotimes [i m] (aset nodes i (symbol (str "Ln" i))))
    (into []
          (map (fn [^long i]
                 (let [s (quot i 8)
                       t (mod (+ (* s 8) (mod i 8) 1) m)]
                   (list edge-pred (aget nodes (int s)) (aget nodes (int t))))))
          (range n))))

;; ---- the KB -------------------------------------------------------------

(defn- fresh-kb
  "An empty KB on the in-memory pair.  Every space is cleared on open, so a run never
  measures the previous run's residue."
  ([] (fresh-kb 12))
  ([space]
   (let [kb (v/open-kb {:backend :memory :space space :recover? false})]
     (p/clear-records! (:records kb))
     (p/clear-index! (:index kb))
     kb)))

(defn- drop-kb! [kb]
  (p/clear-records! (:records kb))
  (p/clear-index! (:index kb)))

(defn- gc! [] (dotimes [_ 3] (System/gc) (Thread/sleep 60)))

(defn- load! [kb facts] (v/bulk-assert-facts! kb facts bench-context))

;; ---- the peel ladder ----------------------------------------------------
;; Each rung turns off one phase.  `nil` is what every stub returns: `merge-with into`
;; over nil is the empty map and `into` over nil adds nothing, so a stubbed rung runs
;; the same shape of code with that phase's work removed.

(defn- nothing [& _] nil)

(defn- no-index-create
  "`create-sentex` without the index write — canonicalize and store the record."
  ([kb s c] (no-index-create kb s c nil))
  ([kb sentence context strength]
   (let [sx (cond-> (res/kb-sentex kb sentence context)
              strength (assoc :strength strength))
         h  (p/put-sentex (:records kb) sx)]
     [h (assoc sx :id h)])))

(defn- no-store-create
  "`create-sentex` without the record write either — canonicalize only."
  ([kb s c] (no-store-create kb s c nil))
  ([kb sentence context strength]
   (let [sx (cond-> (res/kb-sentex kb sentence context)
              strength (assoc :strength strength))]
     [-1 (assoc sx :id -1)])))

(def ^:private canon-cache (atom nil))

(defn- no-canon-create
  "`create-sentex` with canonicalization removed too — one sentex, reused."
  ([kb s c] (no-canon-create kb s c nil))
  ([kb sentence context strength]
   [-1 (or @canon-cache
           (reset! canon-cache (cond-> (res/kb-sentex kb sentence context)
                                 strength (assoc :strength strength)
                                 true     (assoc :id -1))))]))

(def ^:private rungs
  "The peel order, outermost first.  Rung i's redef map is every entry from rung 1 to i
  merged, so a later `create-sentex` stub replaces the earlier one."
  [{#'settle/settle nothing}
   {#'integrate/sentex-added                 nothing
    #'kb/rewritable-sentex?                  (fn [& _] false)
    #'special/derive-functional-equalities   nothing
    #'special/equate-existing                nothing
    #'special/deduce-lifts                   nothing
    #'special/deduce-arg-types               nothing
    #'special/entail-existing                nothing
    #'special/subsumption-seeds              nothing
    #'special/visibility-seeds               nothing
    #'violations/report                      nothing}
   {#'entry/mark-premise nothing}
   {#'kb/note-opposed! nothing}
   {#'observe/notify-add   nothing
    #'observe/note-change  nothing
    #'observe/cache-handle! nothing}
   {#'kb/create-sentex no-index-create}
   {#'kb/create-sentex no-store-create}
   {#'kb/create-sentex no-canon-create}])

(def ^:private rung-names
  ["baseline — the whole bulk-assert path"
   "settle (one, deferred)"
   "special-predicate suite + violations"
   "JTMS node + premise mark"
   "P/¬P coincidence set"
   "observation call sites"
   "index write (key streams + backend)"
   "record store write"
   "canonicalization"
   "residual — public assert prelude, dispatch, mapv"])

(defn- redefs-through [i] (reduce merge {} (take i rungs)))

(defn- timed
  "Elapsed milliseconds of `(f)` run under redef map `m`."
  [m f]
  (let [t0 (System/nanoTime)]
    (if (seq m) (with-redefs-fn m f) (f))
    (/ (- (System/nanoTime) t0) 1e6)))

;; ---- the index sub-split ------------------------------------------------
;; Two `KvBackend` decorators over the real one.  `index-sentex` runs unchanged in
;; both; what changes is how much of the batch it produced actually lands.

(defn- backend-decorator
  "Delegate every `KvBackend` op to `inner`, with `kv-batch`'s op list passed through
  `xform` first.  Reads are untouched, so `count-at` still answers off what landed."
  [inner xform]
  (reify p/KvBackend
    (kv-get             [_ k]   (p/kv-get inner k))
    (kv-put             [_ k x] (p/kv-put inner k x))
    (kv-delete          [_ k]   (p/kv-delete inner k))
    (kv-increment       [_ k]   (p/kv-increment inner k))
    (kv-decrement       [_ k]   (p/kv-decrement inner k))
    (kv-add-to-set      [_ k m] (p/kv-add-to-set inner k m))
    (kv-remove-from-set [_ k m] (p/kv-remove-from-set inner k m))
    (kv-members         [_ k]   (p/kv-members inner k))
    (kv-member?         [_ k m] (p/kv-member? inner k m))
    (kv-count           [_ k]   (p/kv-count inner k))
    (kv-intersect       [_ ks]  (p/kv-intersect inner ks))
    (kv-batch           [_ ops] (p/kv-batch inner (xform ops)))
    (kv-entries         [_]     (p/kv-entries inner))
    (kv-load            [_ es]  (p/kv-load inner es))
    (kv-clear!          [_]     (p/kv-clear! inner))))

(defn- with-backend
  "`kb` with its index store rebuilt over a decorated backend."
  [kb xform]
  (assoc kb :index (kv/->KvIndexStore (backend-decorator (:backend (:index kb)) xform))))

(defn- drop-increments [ops] (into [] (remove #(= :increment (first %))) ops))
(defn- drop-everything [_] [])

;; ---- the runs -----------------------------------------------------------

(defn- one-ladder
  "The peel ladder over `facts` — `[ms …]`, rung 0 (baseline) first."
  [facts]
  (mapv (fn [i]
          (gc!)
          (let [kb (fresh-kb)
                ms (timed (redefs-through i) #(load! kb facts))]
            (drop-kb! kb)
            ms))
        (range 0 (inc (count rungs)))))

(defn- split-run
  "The rung-5 configuration (everything above the index write peeled) with the index
  backend decorated — the arm that prices what a batch's ops cost."
  [facts xform]
  (gc!)
  (let [kb (fresh-kb)
        ms (timed (redefs-through 5) #(load! (with-backend kb xform) facts))]
    (drop-kb! kb)
    ms))

(defn- bulk-writes-run
  "The full baseline with the memory backend's transient accumulation engaged — what
  the write path costs when the trie map is not rebuilt per fact."
  [facts]
  (gc!)
  (let [kb (fresh-kb)
        t0 (System/nanoTime)]
    (mem/with-bulk-writes (:backend (:index kb))
      (load! kb facts))
    (let [ms (/ (- (System/nanoTime) t0) 1e6)]
      (drop-kb! kb)
      ms)))

;; ---- the guard arm ------------------------------------------------------
;; `kb/note-opposed!` writes to the coincidence set and the negation memo only for a
;; body that is opposed before the store or after it.  This arm posts for every body
;; instead, which is what prices the guard: the post is a `conj` into a `:dirty` set
;; that grows to the size of the corpus, so it is the one phase of a load whose
;; per-fact cost rises with N.  Interleaved with the real one in a single JVM, so
;; ambient load lands on both arms rather than on whichever ran second.

(defn- always-post-opposed!
  [kb sentence]
  (let [b (sx/canon (kb/body-under-not sentence))]
    (swap! (reasoning/opposed kb) (if (@#'kb/opposed? (:index kb) b) conj disj) b)
    (swap! (reasoning/negations kb) (fn [m] (-> m
                                                (update :by-body dissoc b)
                                                (update :dirty (fnil conj #{}) b))))))

(defn- baseline-run [facts redefs]
  (gc!)
  (let [kb (fresh-kb)
        ms (timed redefs #(load! kb facts))]
    (drop-kb! kb)
    ms))

(defn- median [xs] (nth (sort xs) (quot (count xs) 2)))

(defn- report-guard
  "Alternate the two arms `repeats` times, **A-B-B-A within each pair**, and report every
  pair's ratio beside the median of them.

  The order alternation is not decoration.  A JVM loading the same corpus a dozen times
  drifts — the heap fills, the collector works harder, and a later run is slower than an
  earlier one whatever it is running.  With a fixed A-then-B order that drift lands
  entirely on B, and the ratio reports the drift as if it were the difference.  Each arm
  here takes one early slot and one late slot per pair, so the drift cancels.  The
  per-pair spread is printed for the same reason: a 4% claim off pairs that scatter 20%
  is a claim about the box."
  [n repeats facts]
  (println (format "%n── the coincidence-post guard, %,d facts × %d ABBA pairs ──" n repeats))
  (println (format "%-14s %12s %12s %10s" "pair" "guarded ms" "posting ms" "ratio"))
  (let [unguarded {#'kb/note-opposed! always-post-opposed!}
        pairs (mapv (fn [i]
                      (let [a (baseline-run facts {})
                            b (baseline-run facts unguarded)
                            c (baseline-run facts unguarded)
                            d (baseline-run facts {})
                            kept   (/ (+ a d) 2.0)
                            posted (/ (+ b c) 2.0)]
                        (println (format "%-14d %12.1f %12.1f %9.3f×"
                                         (inc i) kept posted (/ kept posted)))
                        [kept posted]))
                    (range repeats))
        kept   (median (map first pairs))
        posted (median (map second pairs))]
    (println (format "%-14s %12.1f %12.1f %9.3f×   (%.2f vs %.2f µs/fact)"
                     "median" kept posted (/ kept posted)
                     (* 1000.0 (/ kept n)) (* 1000.0 (/ posted n))))))

;; ---- reporting ----------------------------------------------------------

(defn- report-ladder [n mss]
  (let [total (double (first mss))
        us    (fn [ms] (* 1000.0 (/ (double ms) n)))]
    (println (format "%n── peel ladder, %,d facts ──" n))
    (println (format "%-52s %10s %9s %8s" "phase" "ms" "µs/fact" "share"))
    (doseq [i (range 1 (count mss))]
      (let [d (- (double (nth mss (dec i))) (double (nth mss i)))]
        (println (format "%-52s %10.1f %9.2f %7.1f%%"
                         (nth rung-names i) d (us d) (* 100.0 (/ d total))))))
    (let [resid (double (last mss))]
      (println (format "%-52s %10.1f %9.2f %7.1f%%"
                       (last rung-names) resid (us resid) (* 100.0 (/ resid total)))))
    (println (format "%-52s %10.1f %9.2f %7.1f%%   (%,.0f facts/s)"
                     "TOTAL" total (us total) 100.0 (/ (double n) (/ total 1000.0))))))

(defn- report-split [n full no-incr no-batch]
  (let [us (fn [ms] (* 1000.0 (/ (double ms) n)))]
    (println (format "%n── index write, split (%,d facts) ──" n))
    (println (format "%-52s %10s %9s" "component" "ms" "µs/fact"))
    (doseq [[label ms] [["count maintenance (:increment ops)" (- full no-incr)]
                        ["postings — trie edges, leaves, terms, roots" (- no-incr no-batch)]
                        ["key streams + the rest of rung 5" no-batch]]]
      (println (format "%-52s %10.1f %9.2f" label (double ms) (us ms))))))

(defn- verify!
  "The ladder's rungs store less than a real load; this does not.  A plain
  `bulk-assert-facts!` over the corpus against the same facts asserted one-by-one with
  `assert {:chain? false}` — the contract `bulk-assert-facts!` publishes, checked on
  the corpus the ladder measured."
  [facts]
  (let [a (fresh-kb 12)
        _ (v/bulk-assert-facts! a facts bench-context)
        na (v/count-with-functor a edge-pred)
        _ (drop-kb! a)
        b (fresh-kb 13)
        _ (doseq [f facts] (v/assert b f bench-context {:chain? false}))
        nb (v/count-with-functor b edge-pred)
        _ (drop-kb! b)]
    (println (format "%nparity with per-fact assert: %s (%,d vs %,d of %,d facts)"
                     (if (= na nb (count facts)) "OK" "MISMATCH") na nb (count facts)))))

(defn -main
  "`[n repeats mode]` — `mode` is `full` (the ladder, the index split and the transient
  arm) or `guard` (the alternating guard arm alone, which is the cheap re-check)."
  [& args]
  (let [n       (or (some-> ^String (first args) parse-long) 200000)
        repeats (or (some-> ^String (second args) parse-long) 1)
        mode    (or (nth args 2 nil) "full")
        facts   (corpus n)]
    (println (format "load-path decomposition — :memory pair — %,d facts, %d repeat(s), %s"
                     n repeats mode))
    (let [warm (fresh-kb)]                       ; so the ladder is not measuring the JIT
      (load! warm (subvec facts 0 (min n 20000)))
      (drop-kb! warm))
    (verify! (subvec facts 0 (min n 5000)))
    (when (= mode "guard")
      (report-guard n repeats facts)
      (shutdown-agents)
      (System/exit 0))
    (dotimes [r repeats]
      (when (> repeats 1) (println (format "%n=== repeat %d ===" (inc r))))
      (report-ladder n (one-ladder facts))
      (let [full     (split-run facts identity)
            no-incr  (split-run facts drop-increments)
            no-batch (split-run facts drop-everything)]
        (report-split n full no-incr no-batch))
      (println "\n── the transient-accumulation arm ──")
      (let [b (bulk-writes-run facts)]
        (println (format "with-bulk-writes baseline: %.1f ms (%,.0f facts/s)"
                         b (/ (double n) (/ b 1000.0))))))
    (shutdown-agents)))
