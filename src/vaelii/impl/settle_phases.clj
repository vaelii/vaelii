;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.settle-phases
  "The wall-clock self-time of each settle, charged to the cost centre on top of the
  calling thread's span stack.  Each thread keeps its own stack and tallies, and
  `snapshot` merges them.  One atom, nil when off, so a span off a timing run is a deref
  and a `nil?` check.  `vaelii.bench.settle-phases` reads it.  See docs/nmtms.md, \"Where
  the time goes, measured\".

  A held namespace (`vaelii.impl.types.prover` states what that means): it defines the `Clock` type its instrument hints on, and requires no vaelii namespace, so the development browser's reloader never re-evaluates it, and an edit to it takes a restart."
  (:import [java.util ArrayDeque HashMap Map Map$Entry]
           [java.util.concurrent ConcurrentHashMap ConcurrentLinkedQueue]))

;; one atom rather than a flag beside a store, so no call site reads the switch on and
;; the store nil
(defonce ^:private clock (atom nil))

;; One per thread that charged a span.  All fields are final refs whose contents are
;; mutable, so the owning thread mutates in place without `set!` (which a deftype allows
;; only inside its own methods): the long cells are one-element arrays.  `run` and
;; `settles` are concurrent because `snapshot` reads them from another thread.
(deftype ^:private Clock [^ArrayDeque stack   ; phase keywords, top = the current centre
                          ^ConcurrentHashMap run ; centre -> long[1], whole-run self-time
                          ^HashMap    cur      ; centre -> long[1], this settle's self-time
                          ^ConcurrentLinkedQueue settles ; finished per-settle records
                          ^longs      t         ; last charge time (nanos)
                          ^longs      insettle  ; 1 while inside a settle bracket, else 0
                          ^longs      region    ; this settle's relabelled region size
                          ^longs      passes])  ; this settle's pass count

;; One timing run: each thread's `Clock`, and every `Clock` in the order threads first
;; charged a span.
(deftype ^:private Run [^ThreadLocal mine ^ConcurrentLinkedQueue clocks])

(defn- clock-of
  "The calling thread's `Clock` in run `r`, made on its first span with its charge time
  set to now."
  ^Clock [^Run r]
  (or (.get ^ThreadLocal (.mine r))
      (let [c (->Clock (ArrayDeque.) (ConcurrentHashMap.) (HashMap.) (ConcurrentLinkedQueue.)
                       (long-array [(System/nanoTime)]) (long-array 1)
                       (long-array 1) (long-array 1))]
        (.set ^ThreadLocal (.mine r) c)
        (.add ^ConcurrentLinkedQueue (.clocks r) c)
        c)))

(defn profiling?
  "Is the instrument collecting?"
  []
  (some? @clock))

(defn start
  "Begin collecting, dropping whatever a previous run left.  Bare, not `!`: the tally is
  derived from a workload nobody stored, so re-running the workload recomputes it."
  []
  (let [r (->Run (ThreadLocal.) (ConcurrentLinkedQueue.))]
    (clock-of r)
    (reset! clock r))
  nil)

(defn- cell ^longs [^Map m k]
  (or ^longs (.get m k)
      (let [a (long-array 1)] (.put m k a) a)))

(defn- charge!
  "Charge the interval since the last charge time to the centre on top of the stack (or
  the right sentinel when no span is open), and record the time again.  The one primitive
  every enter, leave and bracket goes through."
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
  (when-let [r @clock]
    (let [c (clock-of r)]
      (charge! c (System/nanoTime))
      (.push ^ArrayDeque (.stack c) p))
    nil))

(defn leave!
  "Close the current span: charge it up to now, then pop.  Guards an empty stack so a
  span entered while the instrument was off (and toggled on mid-span) cannot underflow."
  []
  (when-let [r @clock]
    (let [c (clock-of r)
          ^ArrayDeque st (.stack c)]
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
  (when-let [r @clock]
    (let [c (clock-of r)]
      (charge! c (System/nanoTime))
      (.clear ^HashMap (.cur c))
      (aset ^longs (.insettle c) 0 1)
      (aset ^longs (.region c) 0 0)
      (aset ^longs (.passes c) 0 0))
    nil))

(defn note-region!
  "Record this settle's relabelled region size, read once at the finish."
  [^long n]
  (when-let [r @clock] (aset ^longs (.region (clock-of r)) 0 n) nil))

(defn note-passes!
  "Record this settle's pass count."
  [^long n]
  (when-let [r @clock] (aset ^longs (.passes (clock-of r)) 0 n) nil))

(defn end-settle!
  "Bracket the end of one settle: charge the tail, file the per-settle record, and mark
  the instrument outside a settle again."
  []
  (when-let [r @clock]
    (let [c (clock-of r)]
      (charge! c (System/nanoTime))
      (let [nanos (persistent!
                   (reduce (fn [m e] (assoc! m (key e) (aget ^longs (val e) 0)))
                           (transient {}) (.entrySet ^HashMap (.cur c))))
            total (reduce + 0 (vals nanos))]
        (.add ^ConcurrentLinkedQueue (.settles c)
              {:nanos nanos :total total
               :region (aget ^longs (.region c) 0) :passes (aget ^longs (.passes c) 0)}))
      (.clear ^HashMap (.cur c))
      (aset ^longs (.insettle c) 0 0))
    nil))

(defn snapshot
  "The tallies so far as plain data, or nil when the instrument is off:

      {:run     {centre nanos}          whole-run self-time per centre, summed over threads
       :settles [{:nanos {centre nanos} :total :region :passes} …]}

  `:settles` holds each thread's records in its order, threads in the order they first
  charged a span.  A read, not a stop — the run keeps collecting."
  []
  (when-let [^Run r @clock]
    (let [cs (vec (.toArray ^ConcurrentLinkedQueue (.clocks r)))]
      {:run (reduce (fn [m ^Clock c]
                      (reduce (fn [m ^Map$Entry e]
                                (update m (.getKey e) (fnil + 0) (aget ^longs (.getValue e) 0)))
                              m (.entrySet ^ConcurrentHashMap (.run c))))
                    {} cs)
       :settles (into [] (mapcat #(.toArray ^ConcurrentLinkedQueue (.settles ^Clock %))) cs)})))

(defn stop
  "Charge the calling thread's final interval, return the snapshot, and clear the
  instrument."
  []
  (when-let [r @clock]
    (charge! (clock-of r) (System/nanoTime))
    (let [s (snapshot)]
      (reset! clock nil)
      s)))
