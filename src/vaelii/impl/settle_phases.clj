;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.settle-phases
  "Where a settle spends its **wall clock**, attributed to the four cost centres —
  one switch, off by default, free when off.

  `vaelii.impl.profile` counts what the index is *asked*; this is its wall-clock twin
  for belief.  The question a parallelism study asks is which phase of a bulk settle
  owns the time, and the four centres a settle divides into are:

  * **`:belief`** — the belief fixpoint: `clear-defeats!`, the revival reconcile, the
    `defeat!`/`refresh-after-defeat` relabel inside `resolve-contradictions`, and the
    `add-justification` replay `recovery/rebuild-tms` composes.  The relabel is the work
    `settle-parallelism.md`'s partition-relabel candidate would divide.
  * **`:discovery`** — the nogood scans `constraint-nogoods`, `negation-nogoods` and
    `preserving-nogoods`, the read-only clash-finding a clash-discovery candidate would
    run in parallel.
  * **`:resolution`** — the decision `resolve-contradictions` takes over the nogoods it
    was handed: `decide-nogood` and the edge solver, minus the discovery and the relabel
    the decision drives (those are charged to their own centres).
  * **`:chaining`** — the generative join `chain` / `chain-all` runs, the forward
    inference a parallel-chaining candidate would divide.  A bulk load fires it per
    assert; a `recover` does not fire it at all.

  Two sentinels catch the time no centre names: **`:finish`** is `settle-finish`'s
  cache reconcile and exposure sweeps, **`:glue`** is settle-loop bookkeeping between
  the spans, and **`:outside`** is everything between one settle and the next — the
  assert path's canonicalization, checks, index and minting.

  ## Self-time, not inclusive time

  The centres nest: `resolve-contradictions` calls the discovery scans and drives the
  relabel, `chain` drives its own `add-justification`.  So a phase is charged only its
  **self-time** — the interval while its span is on top of the stack.  Entering a nested
  span charges the parent up to that instant and pauses it; leaving resumes it.  The six
  buckets therefore partition the whole run and sum to it, which an inclusive reading
  (parent time counting its children twice) does not.

  ## Off by default, and free when off

  The switch and the store are one atom, nil when off, so `with-phase` off a timing run
  is a deref and a `nil?` check, which is what `vaelii.impl.profile` costs its call
  sites.  `add-justification` is not wrapped — it is charged through the `:belief` span
  its driver opens (`defeat!`, `rebuild-tms`) or the `:chaining` span its driver opens
  (`chain`) — so the per-assert JTMS path carries no probe at all.

  On, it is two `System/nanoTime` reads and two mutations of an unsynchronized
  `ArrayDeque`/`HashMap` per span.  A settle is single-writer (docs/nmtms.md), so the
  store is mutated in place with no lock, and a run under the instrument answers the
  same belief as one without it, more slowly — the bargain `profile` already takes.

  ## Reading it

  `stop` returns plain data: the run totals per centre, and a per-settle record carrying
  each centre's self-time, the settle's relabelled region size and its pass count.  The
  region size is what a mean over settles hides — one root-edge retraction moves the
  whole graph and a leaf edge moves nothing — so the record is per settle and the
  percentiles are the caller's to take.  `vaelii.bench.settle-phases` is the caller that
  has an opinion; nothing here formats.

  A held namespace (`vaelii.impl.types.prover` states what that means): it defines the `Clock` type its instrument hints on, and requires no vaelii namespace, so the development browser's reloader never re-evaluates it, and an edit to it takes a restart."
  (:import [java.util ArrayDeque ArrayList HashMap]))

;; nil when off.  One atom rather than a flag beside a store, so a call site cannot read
;; the switch on and the store as nil — the `profile` arrangement.
(defonce ^:private clock (atom nil))

;; All fields are final refs whose contents are mutable, so the single writer mutates in
;; place without `set!` (which a deftype allows only inside its own methods): the long
;; cells are one-element arrays, the maps and the deque are the java originals.
(deftype ^:private Clock [^ArrayDeque stack   ; phase keywords, top = the current centre
                          ^HashMap    run      ; centre -> long[1], whole-run self-time
                          ^HashMap    cur      ; centre -> long[1], this settle's self-time
                          ^ArrayList  settles  ; finished per-settle records (maps)
                          ^longs      t         ; last charge stamp (nanos)
                          ^longs      insettle  ; 1 while inside a settle bracket, else 0
                          ^longs      region    ; this settle's relabelled region size
                          ^longs      passes])  ; this settle's pass count

(defn profiling?
  "Is the instrument collecting?"
  []
  (some? @clock))

(defn start
  "Begin collecting, dropping whatever a previous run left.  Bare, not `!`: the tally is
  derived from a workload nobody stored, so re-running the workload recomputes it."
  []
  (reset! clock (->Clock (ArrayDeque.) (HashMap.) (HashMap.) (ArrayList.)
                         (long-array [(System/nanoTime)]) (long-array 1)
                         (long-array 1) (long-array 1)))
  nil)

(defn- cell ^longs [^HashMap m k]
  (or ^longs (.get m k)
      (let [a (long-array 1)] (.put m k a) a)))

(defn- charge!
  "Charge the interval since the last stamp to the centre on top of the stack (or the
  right sentinel when no span is open), and re-stamp.  The one primitive every enter,
  leave and bracket goes through."
  [^Clock c ^long now]
  (let [^ArrayDeque st (.stack c)
        ^longs tarr  (.t c)
        ^longs inarr (.insettle c)
        p  (or (.peek st) (if (zero? (aget inarr 0)) :outside :glue))
        dt (- now (aget tarr 0))]
    (let [^longs r (cell (.run c) p)] (aset r 0 (+ (aget r 0) dt)))
    (when (== 1 (aget inarr 0))
      (let [^longs u (cell (.cur c) p)] (aset u 0 (+ (aget u 0) dt))))
    (aset tarr 0 now)))

(defn enter!
  "Open a span for centre `p`: charge the parent up to now, then push `p`.  A deref and a
  `nil?` check when the instrument is off."
  [p]
  (when-let [^Clock c @clock]
    (charge! c (System/nanoTime))
    (.push ^ArrayDeque (.stack c) p)
    nil))

(defn leave!
  "Close the current span: charge it up to now, then pop.  Guards an empty stack so a
  span entered while the instrument was off (and toggled on mid-span) cannot underflow."
  []
  (when-let [^Clock c @clock]
    (let [^ArrayDeque st (.stack c)]
      (when-not (.isEmpty st)
        (charge! c (System/nanoTime))
        (.pop st)))
    nil))

(defmacro with-phase
  "Run `body` inside a span for centre `p`.  Off a timing run this is a deref, a `nil?`
  check and the body; on one it brackets the body with `enter!`/`leave!` so the centre is
  charged its self-time even if `body` throws."
  [p & body]
  `(do (enter! ~p)
       (try ~@body (finally (leave!)))))

(defn begin-settle!
  "Bracket the start of one settle: charge the pre-settle interval to `:outside`, then
  start a fresh per-settle tally."
  []
  (when-let [^Clock c @clock]
    (charge! c (System/nanoTime))
    (.clear ^HashMap (.cur c))
    (aset ^longs (.insettle c) 0 1)
    (aset ^longs (.region c) 0 0)
    (aset ^longs (.passes c) 0 0)
    nil))

(defn note-region!
  "Record this settle's relabelled region size, read once at the finish."
  [^long n]
  (when-let [^Clock c @clock] (aset ^longs (.region c) 0 n) nil))

(defn note-passes!
  "Record this settle's pass count."
  [^long n]
  (when-let [^Clock c @clock] (aset ^longs (.passes c) 0 n) nil))

(defn end-settle!
  "Bracket the end of one settle: charge the tail, file the per-settle record, and mark
  the instrument outside a settle again."
  []
  (when-let [^Clock c @clock]
    (charge! c (System/nanoTime))
    (let [nanos (persistent!
                 (reduce (fn [m e] (assoc! m (key e) (aget ^longs (val e) 0)))
                         (transient {}) (.entrySet ^HashMap (.cur c))))
          total (reduce + 0 (vals nanos))]
      (.add ^ArrayList (.settles c)
            {:nanos nanos :total total
             :region (aget ^longs (.region c) 0) :passes (aget ^longs (.passes c) 0)}))
    (.clear ^HashMap (.cur c))
    (aset ^longs (.insettle c) 0 0)
    nil))

(defn snapshot
  "The tallies so far as plain data, or nil when the instrument is off:

      {:run     {centre nanos}          whole-run self-time per centre
       :settles [{:nanos {centre nanos} :total :region :passes} …]}

  A read, not a stop — the run keeps collecting."
  []
  (when-let [^Clock c @clock]
    {:run (persistent!
           (reduce (fn [m e] (assoc! m (key e) (aget ^longs (val e) 0)))
                   (transient {}) (.entrySet ^HashMap (.run c))))
     :settles (vec (.toArray ^ArrayList (.settles c)))}))

(defn stop
  "Charge the final interval, return the snapshot, and clear the instrument."
  []
  (when-let [^Clock c @clock]
    (charge! c (System/nanoTime))
    (let [s (snapshot)]
      (reset! clock nil)
      s)))
