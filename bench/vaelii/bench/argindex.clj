;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.argindex
  "What the **argument-root index** costs the belief-settle (`recover`) hot path — the
  measuring stick for the index-layout experiment, phase 1.

  Settling belief over a large corpus is dominated by the definitional-clash sweep:
  `settle/clash-nogoods` walks every believed sentex a pair could form, and each of the
  routes it takes into the index — the `could-clash?` gate's `count-with-arg`, the
  `partner-contexts` vantage read's `sentexes-with-arg`, and `arbitrable-violations`'
  `matches-visible` — narrows on the **argument-root** key `[:argument-root pred pos
  term]`.  That key is a four-element *vector*, and unlike every other index family
  (context / functor / term / rule, all compact int-keyed) it routes to the slow
  fallback (`dense_roots/route :argument-root → :fallback → MemoryKvBackend.kv-members`),
  where a `PersistentHashMap.find` compares the whole vector via `APersistentVector`'s
  `doEquiv`.  A real 11M-sentex settle spent ~28% CPU in that comparison and ~98% of its
  allocation materializing the posting-list seqs the read returns.

  This harness has two layers, both reproducible and both meant to be re-run **verbatim**
  by the two later agents who implement index-layout variants — comparability is the
  whole point:

  * **micro** — isolates one argument-root probe.  A hot subject sits at argument 1 of
    `fanout` facts spread across `contexts` contexts; a `(relOf Subj ?y)` query reads the
    one wide `[:argument-root relOf 1 Subj]` posting and the context filter keeps only the
    visible share.  Reports per-probe wall clock, the raw index read as a fraction of the
    full match, and — the metric a variant is judged on — **returned-vs-matched**: how many
    candidate handles the probe hands back against how many survive `unify` and the
    context filter.  A fanout sweep shows the probe cost is a real fraction of the whole.

  * **macro** — an end-to-end `reindex` + `recover` over a generated corpus that declares
    disjointness (so `constraint-nogoods`' O(1) gate opens and the clash sweep actually
    runs — a corpus declaring none short-circuits and never touches the argument roots).
    Reports reindex and recover wall clock and the bytes `recover` allocates, and prints
    the `prof` read tally as evidence the sweep read the argument roots.

  Returned-vs-matched is captured by `vaelii.impl.profile/record-sift`, an opt-in hook at
  `resolution/matches-hierarchical` — off during timing (a bare deref), on only inside a
  `prof/start`…`prof/stop` window, where it realizes the candidate seq to count it.

  * **join** — the v3 metric.  A probe with TWO ground argument columns, where the
    non-leading column is locally selective, run under each `res/*arg-intersect*`
    strategy over one corpus.  Reports returned / **unified** (unify attempts) / matched,
    per-probe wall clock and allocation per sweep, so the single-column lead (`:off`) and
    the multi-column narrowing sit side by side on identical answer sets.

  Run: `lein bench-argindex micro [--subjects n --fanout n --contexts n --samples n]`
       `lein bench-argindex macro [--individuals n --memberships n --types n --branching b
                                   --disjoints n --predicates n --clashes n]`
       `lein bench-argindex join  [--subjects n --fanout n --objects n --contexts n --samples n]`
       `lein bench-argindex both` runs micro + macro at their defaults.
       `lein bench-argindex columnar` / `disk-columnar` run the macro on the columnar index
       (memory / durable records) — the path whose argument reads go through `DenseRoots`,
       which v4 gives native argument columns; `macro-compare` runs `:memory` then columnar.
  Uses spaces 48 (micro), 49 (macro), 50 (join) and 51 (columnar macro), clear of the test
  block and other harnesses; disk-columnar runs in a throwaway temp dir."
  (:require [vaelii.core :as v]
            [vaelii.impl.disk.backend :as disk-backend]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.resolution :as res])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]))

;; ---- measurement plumbing -----------------------------------------------

(defmacro ^:private timed
  "[result nanoseconds]."
  [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (- (System/nanoTime) t0#)]))

(def ^:private ^ThreadMXBean thread-mx
  (let [b (ManagementFactory/getThreadMXBean)]
    (when (instance? ThreadMXBean b)
      (.setThreadAllocatedMemoryEnabled ^ThreadMXBean b true))
    b))

(defn- all-thread-allocated
  "Bytes allocated across **every** live thread so far, out of the JVM's TLAB accounting
  (`com.sun.management.ThreadMXBean`).  Summed rather than current-thread-only because a
  settle may fan onto worker threads; a thread that is created and dies inside one
  measured region is undercounted, which is the one caveat on the number."
  ^long []
  (let [ids (.getAllThreadIds thread-mx)
        arr (.getThreadAllocatedBytes thread-mx ids)]
    (areduce arr i acc 0 (let [v (aget arr i)] (if (pos? v) (+ acc v) acc)))))

;; ---- naming (well-formed for the real v/assert path) --------------------
;; predicates lowercase-initial camelCase; individuals/types/contexts Capitalized —
;; the invariants v/assert enforces.  Types are lowercase-initial symbols ending `_t`,
;; the shape bench/checks.clj uses so a type is indistinguishable from a predicate applied to a term.

(defn- type-name [i] (symbol (str "bt" i "_t")))
(defn- ind-name  [i] (symbol (str "BI" i)))
(defn- pred-name [i] (symbol (str "bp" i "Of")))
(defn- subj-name [i] (symbol (str "Subj" i)))
(defn- obj-name  [i] (symbol (str "Obj" i)))
(defn- shadow-ctx [k] (symbol (str "CxSh" k)))

(defn- parent-of [branching i]
  (if (zero? i) 'thing (type-name (quot (dec i) branching))))

(defn- ancestor-chain
  "Type indices from `i` up to the root, `i` first."
  [branching i]
  (take-while some? (iterate (fn [j] (when (pos? j) (quot (dec j) branching))) i)))

;; =========================================================================
;; MICRO — one argument-root probe
;; =========================================================================

(def ^:private micro-defaults
  {:subjects 300     ; distinct hot subjects — one probe apiece, so the cache never warms
   :fanout   400     ; facts per subject at argument 1 = the argument-root posting's width
   :contexts 8       ; contexts the fanout is spread across; 1 is visible → returned/matched ≈ this
   :samples  5})     ; measured passes over the subjects, after a warm-up

(defn- build-micro!
  "A KB whose argument-1 roots are **wide**: each of `subjects` hot subjects sits at
  argument 1 of `fanout` `(relOf Subj Obj)` facts, round-robined across `contexts`
  sibling contexts of which only `CxAsk` is visible from `CxAsk`.  So one
  `[:argument-root relOf 1 Subj]` posting holds `fanout` handles and a query from
  `CxAsk` matches the `fanout/contexts` stored there."
  [kb {:keys [subjects fanout contexts]}]
  (v/assert kb (list 'genlCx 'CxAsk 'CxCore) 'CxCore {:chain? false})
  (doseq [k (range (dec contexts))]
    (v/assert kb (list 'genlCx (shadow-ctx k) 'CxCore) 'CxCore {:chain? false}))
  (let [ctx-at (fn [n] (if (zero? (mod n contexts)) 'CxAsk (shadow-ctx (dec (mod n contexts)))))]
    (v/with-deferred-settle kb
      (dotimes [s subjects]
        (let [subj (subj-name s)]
          (dotimes [f fanout]
            (v/assert kb (list 'relOf subj (obj-name f)) (ctx-at f) {:chain? false}))))))
  'CxAsk)

(defn- micro-probe-raw
  "The scoped argument-root **lookup** `lead-candidates` performs, in isolation — no
  unify, no cache — over every hot subject.  This is the vector-key hash probe
  (`[:argument-root relOf 1 Subj]` → `dense_roots :fallback` → `kv-members` → the
  `doEquiv` the profile flagged), which hands back the posting set by *reference*: O(1),
  so its aggregate cost in a settle is driven by the count of probes, not their width.
  Returns [total-handles nanoseconds]."
  [kb subjects]
  (let [ix (:index kb)]
    (timed
     (loop [s 0, acc 0]
       (if (< s subjects)
         (recur (inc s) (+ acc (count (p/sentexes-with-args ix 'relOf {1 (subj-name s)}))))
         acc)))))

(defn- micro-probe-walk
  "The **materialization** the consumer pays: walking the returned posting as a seq, which
  is where `PersistentHashMap$ArrayNode$Seq.create` — ~98% of the real settle's
  allocation — is spent, and the one part that scales with the posting's width.
  Returns [total-handles nanoseconds]."
  [kb subjects]
  (let [ix (:index kb)]
    (timed
     (loop [s 0, acc 0]
       (if (< s subjects)
         (let [post (p/sentexes-with-args ix 'relOf {1 (subj-name s)})
               c    (loop [t (seq post), n 0] (if t (recur (next t) (inc n)) n))]
           (recur (inc s) (+ acc (long c))))
         acc)))))

(defn- micro-probe-match
  "The full clash-arm call `arbitrable-violations` makes — `res/matches-visible` on a
  bound-argument-1 literal — with the literal cache OFF so each probe hits the index.
  Returns [total-matches nanoseconds]."
  [kb ctx subjects]
  (binding [lc/*enabled* false]
    (timed
     (loop [s 0, acc 0]
       (if (< s subjects)
         (recur (inc s) (+ acc (count (res/matches-visible kb (list 'relOf (subj-name s) '?y) ctx))))
         acc)))))

(defn- micro-sift
  "returned-vs-matched over the same probes, read off the `:sift` tally — a separate,
  profiled pass so the timing runs above are unperturbed."
  [kb ctx subjects]
  (prof/start)
  (binding [lc/*enabled* false]
    (dotimes [s subjects]
      (res/matches-visible kb (list 'relOf (subj-name s) '?y) ctx)))
  (let [snap (prof/stop)]
    (:sift snap)))

(defn- fmt-sift [sift]
  (let [rows (vals sift)
        ret  (reduce + 0 (map :returned rows))
        uni  (reduce + 0 (map (fn [r] (or (:unified r) 0)) rows))
        mat  (reduce + 0 (map :matched rows))]
    {:returned ret :unified uni :matched mat
     :ratio    (double (/ ret (max 1 mat)))
     :uni-ratio (double (/ uni (max 1 mat)))}))

(defn- run-micro-once [kb ctx {:keys [subjects samples] :as opts}]
  ;; warm the JIT
  (micro-probe-raw kb subjects)
  (micro-probe-walk kb subjects)
  (micro-probe-match kb ctx subjects)
  (let [raws (repeatedly samples #(micro-probe-raw kb subjects))
        wlks (repeatedly samples #(micro-probe-walk kb subjects))
        mats (repeatedly samples #(micro-probe-match kb ctx subjects))
        raw-ns (/ (double (reduce + (map second raws))) samples subjects)
        wlk-ns (/ (double (reduce + (map second wlks))) samples subjects)
        mat-ns (/ (double (reduce + (map second mats))) samples subjects)
        handles (double (/ (ffirst raws) subjects))
        matched (double (/ (ffirst mats) subjects))
        sift    (fmt-sift (micro-sift kb ctx subjects))]
    (println (format "  fanout %,6d | lookup %7.2f µs (%,.0f handles) | walk %8.2f µs | full match %8.2f µs (%,.0f matched) | returned/matched %,.0f/%,.0f = %.1f×"
                     (long (:fanout opts))
                     (/ raw-ns 1000.0) handles
                     (/ wlk-ns 1000.0)
                     (/ mat-ns 1000.0) matched
                     (double (:returned sift)) (double (:matched sift)) (:ratio sift)))
    {:fanout (:fanout opts) :lookup-us (/ raw-ns 1000.0) :walk-us (/ wlk-ns 1000.0)
     :match-us (/ mat-ns 1000.0) :handles handles :matched matched :sift sift}))

(defn run-micro [opts]
  (println (format "\n=== MICRO: one argument-root probe ===  subjects %,d, contexts %d, samples %d"
                   (long (:subjects opts)) (long (:contexts opts)) (long (:samples opts))))
  (println "  lookup = p/sentexes-with-args [:argument-root relOf 1 Subj] hash probe (cache-free, O(1))")
  (println "  walk   = materializing the returned posting as a seq (the ~98%-alloc cost, O(width))")
  (println "  full match = res/matches-visible (relOf Subj ?y) from CxAsk (the clash-arm call)")
  (println "  returned/matched from prof :sift (matches-hierarchical); ratio ≈ contexts")
  ;; sensitivity: lookup is ~flat (O(1) hash probe); walk and full match track fanout (width)
  (println "\n  -- fanout sensitivity (posting width drives walk + match, not the O(1) lookup) --")
  (doseq [fan [50 (:fanout opts) (* 2 (long (:fanout opts)))]]
    (let [o  (assoc opts :fanout fan)
          kb (doto (v/open-kb {:backend :memory :space 48 :recover? false}) (v/clear!))
          ctx (build-micro! kb o)]
      (v/reindex kb)
      (run-micro-once kb ctx o)))
  (println))

;; =========================================================================
;; JOIN — multi-bound-argument narrowing (the v3 metric)
;; =========================================================================
;; A probe `(relT Subj Obj ?z)` binds TWO indexable columns.  The single-column lead
;; picks the tightest one (`Subj` at argument 1, `fanout` facts) and lets `unify` reject
;; every candidate whose `Obj` at argument 2 disagrees; multi-column narrowing intersects
;; the two argument roots at the probe, so only the conjunction reaches `unify`.  The
;; second column is *globally* wider than the first (every subject relates to every
;; object, so `Obj@2` spans `subjects × fanout/objects` facts) yet *locally* selective
;; (one object is `1/objects` of a subject's fanout) — the exact shape where leading with
;; the min-count column returns a wasteful superset and the intersection pays.
;;
;; Runs each `*arg-intersect*` strategy over the SAME corpus (`:off` is the pre-v3
;; single-column lead — the before), reporting per-probe wall clock, allocation per
;; sweep, and the `prof` returned/unified/matched.  `unified` is the unify-attempt count
;; the change moves: `:off` unifies the whole visible column, the narrowing strategies
;; unify only the matched conjunction, so `unified` collapses toward `matched`.

(def ^:private join-defaults
  {:subjects 300   ; hot subjects — one probe apiece, so no literal-cache warming
   :fanout   400   ; facts per subject at argument 1 = the leading column's width
   :objects  10    ; distinct argument-2 objects; local selectivity of column 2 = 1/objects
   :contexts 8     ; contexts the fanout is spread across; only CxAsk is visible
   :samples  5})

(defn- val-name [s f] (symbol (str "Val" s "v" f)))   ; CapitalCamelCase, no underscore

(defn- build-join!
  "A ternary corpus `(relT Subj Obj Val)`: each of `subjects` hot subjects sits at
  argument 1 of `fanout` facts, whose argument-2 `Obj` round-robins over `objects` and
  whose context round-robins over `contexts` (only `CxAsk` visible).  So `Subj@1` holds
  `fanout` handles, `Obj@2` holds `subjects × fanout/objects` (wider than `Subj@1`), and
  their intersection under `relT` holds `fanout/objects` — the local narrowing the probe
  wants and the min-count lead misses."
  [kb {:keys [subjects fanout objects contexts]}]
  (v/assert kb (list 'genlCx 'CxAsk 'CxCore) 'CxCore {:chain? false})
  (doseq [k (range (dec contexts))]
    (v/assert kb (list 'genlCx (shadow-ctx k) 'CxCore) 'CxCore {:chain? false}))
  (let [ctx-at (fn [n] (if (zero? (mod n contexts)) 'CxAsk (shadow-ctx (dec (mod n contexts)))))]
    (v/with-deferred-settle kb
      (dotimes [s subjects]
        (let [subj (subj-name s)]
          (dotimes [f fanout]
            (v/assert kb (list 'relT subj (obj-name (mod f objects)) (val-name s f))
                      (ctx-at f) {:chain? false}))))))
  'CxAsk)

(defn- join-sweep
  "One probe apiece over every hot subject — `(relT Subj Obj ?z)` from `ctx`, cache OFF so
  each hits the index.  Returns total matches."
  [kb ctx subjects obj]
  (binding [lc/*enabled* false]
    (loop [s 0, acc 0]
      (if (< s subjects)
        (recur (inc s) (+ acc (count (res/matches-visible kb (list 'relT (subj-name s) obj '?z) ctx))))
        acc))))

(defn- join-sift
  "returned/unified/matched over the same probes, off the `:sift` tally — a separate,
  profiled pass so the timing runs are unperturbed."
  [kb ctx subjects obj]
  (prof/start)
  (binding [lc/*enabled* false]
    (dotimes [s subjects]
      (res/matches-visible kb (list 'relT (subj-name s) obj '?z) ctx)))
  (fmt-sift (:sift (prof/stop))))

(defn- run-join-strategy [kb ctx {:keys [subjects samples]} obj strat]
  (binding [res/*arg-intersect* strat]
    (join-sweep kb ctx subjects obj)                       ; warm the JIT under this strategy
    (let [times     (repeatedly samples #(second (timed (join-sweep kb ctx subjects obj))))
          per-probe (/ (double (reduce + times)) samples subjects)
          a0        (all-thread-allocated)
          _         (join-sweep kb ctx subjects obj)
          alloc     (- (all-thread-allocated) a0)
          sift      (join-sift kb ctx subjects obj)]
      (println (format "  %-5s | probe %8.3f µs | alloc/sweep %,13d B | returned %,8.0f  unified %,7.0f  matched %,6.0f | ret/mat %5.1f×  uni/mat %5.1f×"
                       (name strat) (/ per-probe 1000.0) (long alloc)
                       (double (:returned sift)) (double (:unified sift)) (double (:matched sift))
                       (:ratio sift) (:uni-ratio sift)))
      (assoc sift :strat strat :probe-us (/ per-probe 1000.0) :alloc alloc))))

(defn run-join [opts]
  (println (format "\n=== JOIN: multi-bound-argument narrowing ===  subjects %,d, fanout %,d, objects %d, contexts %d, samples %d"
                   (long (:subjects opts)) (long (:fanout opts)) (long (:objects opts))
                   (long (:contexts opts)) (long (:samples opts))))
  (println "  probe (relT Subj Obj ?z) — column 1 (Subj) wide, column 2 (Obj) locally 1/objects selective")
  (println "  :off = pre-v3 single leading column; :two/:all/:gated intersect the argument roots")
  (println "  unified = candidates reaching unify (the metric v3 moves); matched = survivors")
  (let [kb  (doto (v/open-kb {:backend :memory :space 50 :recover? false}) (v/clear!))
        ctx (build-join! kb opts)
        obj (obj-name 0)]
    (v/reindex kb)
    (println (format "  built %,d sentexes\n" (long (v/sentex-count kb))))
    (let [rows (doall (map #(run-join-strategy kb ctx opts obj %) [:off :two :all :gated]))
          base (first (filter #(= :off (:strat %)) rows))
          two  (first (filter #(= :two (:strat %)) rows))]
      (when (zero? (long (:matched base)))
        (println "\n  WARNING: zero matches — knobs left the probe object invisible; pick fanout ≥ lcm(objects,contexts)"))
      (when (and base two (pos? (long (:matched base))))
        (println (format "\n  :off → :two  returned %,.0f → %,.0f (%.1f× fewer)  |  unified %,.0f → %,.0f (%.1f× fewer)  |  answer set identical (matched %,.0f = %,.0f)"
                         (double (:returned base)) (double (:returned two))
                         (/ (double (:returned base)) (max 1.0 (double (:returned two))))
                         (double (:unified base)) (double (:unified two))
                         (/ (double (:unified base)) (max 1.0 (double (:unified two))))
                         (double (:matched base)) (double (:matched two)))))
      (println)
      rows)))

;; =========================================================================
;; MACRO — reindex + recover over a corpus that fires the clash sweep
;; =========================================================================

(def ^:private macro-defaults
  {:types        6000
   :branching    3
   :individuals  18000
   :memberships  4       ; ≥2 so `could-clash?` opens for every membership → the sweep reads its root
   :predicates   20
   :disjoints    300     ; opens `constraint-nogoods`' O(1) gate so `clash-nogoods` runs at all
   :clashes      400})   ; individuals holding a declared-disjoint pair — real argument-root matches + sift

(defn- build-macro!
  "A KB shaped like the definitional-clash sweep's diet: a deep genl tree with
  disjointness declared between subtrees (the gate-opener), individuals each holding
  `memberships` non-clashing types from their own ancestor chain (so every membership is
  a `could-clash?` candidate whose argument-1 root the sweep reads), and `clashes`
  individuals holding both sides of one declared-disjoint pair (so `arbitrable-violations`
  reads the argument roots and `matches-hierarchical` records returned-vs-matched)."
  [kb {:keys [types branching individuals memberships predicates disjoints clashes]}]
  (let [ctx 'CxBench]
    (v/assert kb (list 'genlCx ctx 'CxCore) 'CxCore {:chain? false})
    (v/with-deferred-settle kb
      (doseq [i (range types)]
        (v/assert kb (list 'genl (type-name i) (parent-of branching i)) ctx {:chain? false}))
      ;; disjointness between different subtrees of the root's children
      (doseq [d (range disjoints)]
        (let [a (+ 1 (* 2 d)) b (+ 2 (* 2 d))]
          (when (and (< a types) (< b types))
            (v/assert kb (list 'disjoint (type-name a) (type-name b)) ctx {:chain? false}))))
      (doseq [i (range predicates)]
        (v/assert kb (list 'arg (pred-name i) 1 (type-name 0)) ctx {:chain? false})
        (v/assert kb (list 'arg (pred-name i) 2 (type-name 0)) ctx {:chain? false}))
      ;; every individual holds `memberships` types off one leaf's ancestor chain —
      ;; comparable types, nothing disjoint, so the sweep does the full could-clash read
      ;; and the disjointness test admits
      (doseq [i (range individuals)]
        (let [leaf (+ (quot types 2) (mod i (quot types 2)))]
          (doseq [t (take memberships (ancestor-chain branching leaf))]
            (v/assert kb (list (type-name t) (ind-name i)) ctx {:chain? false}))))
      ;; the real clashes: hold both sides of the first declared-disjoint pair (types 1,2)
      (doseq [c (range clashes)]
        (let [x (symbol (str "CI" c))]
          (v/assert kb (list (type-name 1) x) ctx {:chain? false})
          (v/assert kb (list (type-name 2) x) ctx {:chain? false}))))
    ctx))

(defn- read-summary
  "The argument-root traffic a `prof` snapshot recorded, as the slow-path evidence line."
  [snap]
  (let [reads (:reads snap)
        sift  (fmt-sift (:sift snap))]
    {:argument-root (get reads :argument-root 0)
     :argument-slot (get reads :argument-slot 0)
     :functor-root  (get reads :functor-root 0)
     :context-root  (get reads :context-root 0)
     :sift          sift}))

(defn- settle-and-report
  "Reindex + recover over an already-built `kb`, then a profiled recover for the read
  tally — the measurement half the macro is for, factored out so the SAME numbers can be
  read off `:memory` and off the columnar / disk-columnar path (where the argument reads
  bottom out on `DenseRoots`).  Returns a result map so a caller diffing two index
  backends has the figures, not just the print."
  [kb n]
  ;; the two halves of an open, exactly as bench/reindex.clj times them
  (let [[res ix-ns] (timed (reindex/reindex kb))
        a0          (all-thread-allocated)
        [_  rec-ns] (timed (v/recover kb))
        rec-bytes   (- (all-thread-allocated) a0)
        contras     (count (v/contradictions kb))
        viols       (count (v/violations kb))]
    (println (format "  reindex   %8.2f s   (%,d sentexes, %,d rules)"
                     (/ ix-ns 1e9) (long (:sentexes res)) (long (:rules res))))
    (println (format "  recover   %8.2f s   (the belief-settle hot path)" (/ rec-ns 1e9)))
    (println (format "  allocated %,d bytes  (%.1f MB, %,.0f B/sentex) during recover"
                     rec-bytes (/ rec-bytes 1048576.0) (double (/ rec-bytes (max 1 n)))))
    (println (format "  belief: %,d contradictions, %,d violations" contras viols))
    ;; evidence: a profiled recover so the read tally attributes the sweep to the roots
    (println "\n  -- slow-path evidence: prof :reads over one recover --")
    (prof/start)
    (v/recover kb)
    (let [snap (prof/stop)
          {:keys [argument-root argument-slot functor-root context-root sift]} (read-summary snap)]
      (println (format "  argument-root reads %,d | argument-slot reads %,d | functor-root %,d | context-root %,d"
                       (long argument-root) (long argument-slot) (long functor-root) (long context-root)))
      (println (format "  matches-hierarchical returned/matched: %,d / %,d = %.1f×"
                       (long (:returned sift)) (long (:matched sift)) (:ratio sift)))
      (when (zero? (long argument-root))
        (println "  WARNING: zero argument-root reads — the clash sweep did not probe the roots (gate closed?)"))
      (println)
      {:reindex-s (/ ix-ns 1e9) :recover-s (/ rec-ns 1e9) :recover-bytes rec-bytes
       :sentexes n :contradictions contras :violations viols
       :argument-root argument-root :argument-slot argument-slot
       :functor-root functor-root :context-root context-root :sift sift})))

(defn- macro-header [tag opts]
  (println (format "\n=== MACRO [%s]: reindex + recover ===  types %,d (branching %d), individuals %,d × %d memberships, %,d disjoint pairs, %,d clashes"
                   tag (long (:types opts)) (long (:branching opts)) (long (:individuals opts))
                   (long (:memberships opts)) (long (:disjoints opts)) (long (:clashes opts)))))

(defn- run-macro-open
  "Open a KB on `open-opts`, build the clash-sweep corpus, and settle+report.  The corpus
  is the same shape and size on every backend (`build-macro!`), so the numbers are
  comparable across `:memory`, `:memory-columnar` and `:disk-columnar`."
  [tag open-opts opts]
  (macro-header tag opts)
  (let [kb (doto (v/open-kb (merge {:recover? false :constraints :arbitrate} open-opts))
             (v/clear!))
        [_ build-ns] (timed (build-macro! kb opts))
        n  (v/sentex-count kb)]
    (println (format "  built %,d sentexes in %.1f s" (long n) (/ build-ns 1e9)))
    (settle-and-report kb n)))

(defn run-macro
  "The original macro, on the `:memory` backend — unchanged, so `lein bench-argindex both`
  still reports the v2/v3 memory wins verbatim."
  [opts]
  (run-macro-open "memory" {:backend :memory :space 49} opts))

(defn run-macro-columnar
  "The macro on `:memory-columnar` — memory records, the native columnar trie, and the
  argument-root reads through `DenseRoots` (its int-keyed roots backend), where a scoped
  key packs into a long and the predicate-agnostic reads union over the slot roster."
  [opts]
  (run-macro-open "memory-columnar → DenseRoots" {:backend :memory-columnar :space 51} opts))

(defn- rm-rf! [^java.io.File f]
  (when (.isDirectory f) (doseq [c (.listFiles f)] (rm-rf! c)))
  (.delete f))

(defn run-macro-disk-columnar
  "The macro on `:disk-columnar` — durable records, the columnar index rebuilt on open,
  arg-root reads through `DenseRoots` over its in-RAM fallback.  A throwaway temp dir, torn
  down after; the index is unmapped here (a fresh open rebuilds it), which is the same
  representation the arg-root reads take mapped, since the roots ride the resident fallback
  blob rather than the mapped run (`dense_roots`/`index_snapshot`)."
  [opts]
  (let [dir (str (System/getProperty "java.io.tmpdir") "/vaelii-argindex-diskcol-" (System/nanoTime))]
    (try
      (run-macro-open "disk-columnar → DenseRoots" {:backend :disk-columnar :dir dir} opts)
      (finally
        ;; fsync + close the durable stores and release the lock before the dir goes —
        ;; an open handle would otherwise keep the tree around (test teardown does the same)
        (try (disk-backend/close-dir! dir) (catch Throwable _))
        (rm-rf! (java.io.File. dir))))))

;; ---- entry --------------------------------------------------------------

(defn- parse-args [defaults args]
  (reduce (fn [m [k v]] (assoc m (keyword (subs k 2)) (Long/parseLong v)))
          defaults
          (partition 2 args)))

(defn -main [& args]
  (let [mode (first args)
        rest (next args)]
    (case mode
      "micro" (run-micro (parse-args micro-defaults rest))
      "macro" (run-macro (parse-args macro-defaults rest))
      "join"  (run-join (parse-args join-defaults rest))
      ;; the columnar / disk-columnar macro — the path v4's native argument columns on
      ;; `DenseRoots` moves.  `columnar` is memory records + the columnar index (DenseRoots
      ;; over an in-RAM fallback); `disk-columnar` durable records with the same index.
      "columnar"      (run-macro-columnar      (parse-args macro-defaults rest))
      "disk-columnar" (run-macro-disk-columnar (parse-args macro-defaults rest))
      ;; the same corpus settled on both index backends, back to back, so the memory
      ;; numbers and the DenseRoots numbers sit side by side in one run
      "macro-compare" (let [o (parse-args macro-defaults rest)]
                        (run-macro o)
                        (run-macro-columnar o))
      ("both" nil) (do (run-micro (parse-args micro-defaults rest))
                       (run-macro (parse-args macro-defaults rest)))
      (do (println "usage: lein bench-argindex micro|macro|join|both|columnar|disk-columnar|macro-compare [--knob n ...]")
          (System/exit 1))))
  (shutdown-agents)
  (System/exit 0))
