;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.budget
  "Resource-bounded / anytime realization of an answer stream.

  The engine's query paths are **lazy** — `ask`, `query`, and the level stack
  all yield one solution at a time, paying per result consumed.  Resource-bounding
  is therefore the *consumer-side* discipline of realizing that stream under a
  bound and reporting whether it ran dry or was cut short — and resumption falls
  out of laziness for free, because the unrealized tail **is** the continuation.

  A **budget** is a map of optional bounds (any subset; nil / {} means unbounded):

    :max-ms       wall-clock milliseconds — a soft deadline, checked *between*
                  yielded results (between DFS steps and node expansions in
                  `prove-within`), and inside one only by a walk that reads
                  `*deadline*` (the argument-preservation prover's claim walk);
                  every other single pull or step runs to its end
    :max-results  stop after this many solutions
    :max-cost     a qualitative prover-cost ceiling — a tier keyword (see
                  `vaelii.impl.provers/cost-tiers`).  Honored by `ask-within`,
                  which drops provers above the tier before the stream is built;
                  ignored *here*, since it selects *which* work runs, not how much
                  of a stream to realize.
    :max-depth    transformation (rule-expansion) depth — honored by `prove-within`
    :max-term-growth
                  how many levels of compound nesting a subgoal may add over what its
                  own derivation path has already met (`res/default-max-term-growth`,
                  8) — the DFS prover's other termination guard, honored by
                  `prove-within` through `prove-bounds`

  A key outside those five is refused (`:unknown-option`, `check-budget!`): every
  bound is optional, so a misspelt one is not missing — the run is simply unbounded,
  in silence.

  A **partial result** — the anytime contract returned by `collect` / `from-batch`
  / `resume`:

    :results      the solutions realized in *this* step (a vector)
    :status       :complete  the source ran dry — the answer is exhaustive
                  :timeout   :max-ms elapsed with work remaining
                  :capped    :max-results reached with work remaining
    :count        (count :results)
    :elapsed-ms   wall-clock spent in this step
    :resume       nil when :complete; otherwise a 1-arg fn (budget -> partial
                  result) that continues exactly where this step stopped

  `:results` are per-step, **not cumulative**: concatenate across steps for the
  whole answer.  The resume continuation captures an in-memory lazy tail (or, for
  `prove-within`, the DFS goal stack), so resumption is **in-process only** — it
  does not survive a restart, and holding one retains its captured state in the heap
  (see the single-writer contract in docs/storage.md)."
  (:require [vaelii.impl.opts :as opts]))

(def ask-budget-keys
  "Every bound `ask-within` reads: the wall clock, the result cap, and the qualitative
  prover-cost ceiling.  **Not `:max-depth` / `:max-term-growth`**, which bound rule
  expansion `ask` does not do — the same split `vaelii.core/ask-opt-keys` makes for `ask`."
  #{:max-ms :max-results :max-cost})

(def prove-budget-keys
  "Every bound `prove-within` reads: the wall clock, the result cap, and the two guards on
  rule expansion.  **Not `:max-cost`**, an `ask` concept `prove` ignores — the same split
  `vaelii.core/prove-opt-keys` makes for `prove`."
  #{:max-ms :max-results :max-depth :max-term-growth})

(def budget-keys
  "Every bound a budget may carry — the **union** of what `ask-within` and `prove-within`
  each read.  `resume` continues either, so it holds a partial to this union rather than to
  one entry point's half; `check-budget!` defaults to it, and the two entry points pass
  their own narrower key set instead.  Public for the reason `vaelii.core/assert-opt-keys`
  is: it is the answer to \"is this a real bound?\"."
  (into ask-budget-keys prove-budget-keys))

(defn check-budget!
  "Refuse a budget key nothing reads, a value outside a bound's domain, and a non-nil
  non-map budget (`:unknown-option` all three).  A budget is a map of *optional* bounds,
  so a misspelt key is not missing — the run is simply unbounded: `{:max-mss 100}`
  realizes the whole stream, which on an infinite source never returns, and is in any case
  the opposite of what was asked.  And a bound holding a value it cannot mean — a string
  `:max-ms`, a zero `:max-results` — reaches arithmetic and throws bare, where every
  sibling refusal is typed; `check-values!` catches it here (`opts/bound-domains`).
  (A `:max-cost` value outside the tiers is checked separately, `:unknown-option` at
  `vaelii.impl.provers/cost-capped-provers`, which `ask-capped` reads the registry
  through — it is not a numeric bound, so it has no row in `bound-domains`.)

  `opt-keys` defaults to the union `budget-keys` — what `resume`, `collect` and the two
  drivers hold a budget to, since a `resume` continues either entry point.  `ask-within`
  and `prove-within` pass their own narrower key set and subject, so a caller who names
  `:max-depth` at `ask-within` is told it is not a bound `ask` reads."
  ([budget] (check-budget! budget budget-keys "budget"))
  ([budget opt-keys subject]
   (opts/check! budget opt-keys subject
                "A bound nothing reads is an unbounded run in silence.")
   (opts/check-values! budget subject)
   budget))

(defn now
  "The `System/nanoTime` instant every deadline in this namespace is set and checked
  against.  A test hooks it to move a deadline past without sleeping."
  []
  (System/nanoTime))

(defn deadline
  "Absolute `now` instant `:max-ms` from now, or nil when unbounded."
  [budget]
  (when-let [ms (:max-ms budget)]
    (+ (long (now)) (long (* ms 1e6)))))

(def ^:dynamic *deadline*
  "The `now` instant a walk inside one step of a bounded read stops at: bound by `collect`
  around its pulls when the caller hands it a `restart`, by the two backward chainers
  around a leaf (`interruptible`), and by `metered` to its meter's deadline; nil otherwise.  A walk reads it
  through `check-deadline!`."
  nil)

(defn check-deadline!
  "Throw the signal `collect` catches when the instant `dl` has passed.  A nil `dl`
  never throws."
  [dl]
  (when (and dl (>= (long (now)) (long dl)))
    (throw (ex-info "the deadline passed inside a pull" {::deadline dl}))))

(defn interruptible
  "`(f)` with `*deadline*` bound to `dl` (nil: no deadline, whatever an enclosing frame
  bound), or `::interrupted` when a walk inside it threw `check-deadline!`'s signal.  `f`
  must be eager: a lazy seq handed back realizes after the binding has popped, and outside
  the catch."
  [dl f]
  (try (binding [*deadline* dl] (f))
       (catch clojure.lang.ExceptionInfo e
         (if (contains? (ex-data e) ::deadline) ::interrupted (throw e)))))

;; ---- one unit of a long write pass ---------------------------------------
;; A pass over many facts that writes as it goes gives each fact a budget, and a fact
;; past it is set aside whole rather than decided by the clock: the check below throws,
;; and the pass catches the throw at the fact and records the fact as owed.  Only the
;; read-only part of a unit binds the deadline, so the throw never lands inside a write.

(def ^:dynamic *unit-deadline*
  "The `now` instant past which `check-unit!` throws, or nil for none.  Bound by a pass
  around the read-only checks of one unit (`vaelii.core/record-arg-types!`), never around a
  write."
  nil)

(def ^:dynamic *unit-phase*
  "nil, or a volatile naming the part of a unit's checks running now (`unit-phase!`),
  which `check-unit!`'s signal carries."
  nil)

(defn unit-phase!
  "Name the part of the unit's checks that runs from here, when a pass is watching."
  [k]
  (when-let [p *unit-phase*] (vreset! p k))
  nil)

(defn check-unit!
  "Throw the signal `unit-over?` reads when the unit's deadline has passed.  Free when no
  pass bound one."
  []
  (when-let [dl *unit-deadline*]
    (when (>= (long (now)) (long dl))
      (throw (ex-info "the unit's budget passed inside its checks"
                      {::unit-over dl :phase (some-> *unit-phase* deref)})))))

(defn unit-over?
  "Was `t` thrown by `check-unit!`?"
  [t]
  (contains? (ex-data t) ::unit-over))

(defn- pull
  "`(seq xs)` under the `*deadline*` `collect` bound, or `::interrupted`."
  [xs]
  (interruptible *deadline* #(seq xs)))

(defn prove-bounds
  "A budget as the DFS prover's `bounds` map (`res/prove-from`) — the deadline the
  wall-clock bound resolves to, plus the caps it reads under their own names.

  One translation, and it lives beside `budget-keys` on purpose: the key set and the
  map that honours it are two halves of one claim, and a bound listed there but not
  built here is accepted and then ignored — precisely what `check-budget!` refuses a
  misspelt key to prevent.  `:max-cost` is absent because it bounds `ask`'s prover tiers
  rather than a search, and the node-engine arm of
  `prove-within` takes the budget itself rather than this map.

  A bound the caller did not name reads nil, which `prove-from` takes as unbounded —
  except `:max-term-growth`, whose absence is `res/default-max-term-growth` rather than
  no ceiling, since it is a termination guard and not a budget the caller may drop."
  [budget]
  {:deadline        (deadline budget)
   :max-results     (:max-results budget)
   :max-depth       (:max-depth budget)
   :max-term-growth (:max-term-growth budget)})

(defn ms-since
  "Milliseconds elapsed since a `now` instant, as a double."
  [start-nanos]
  (/ (double (- (long (now)) (long start-nanos))) 1e6))

(defn from-batch
  "Assemble the partial-result contract from a completed step.  `resume-fn` is a
  1-arg (budget -> partial result) continuation; it is dropped when `status` is
  `:complete` (nothing remains to continue).  Both engines — the lazy `collect`
  and the eager `prove-within` — build their answer through here, so the two
  return the identical shape."
  [results status start-nanos resume-fn]
  {:results    results
   :status     status
   :count      (count results)
   :elapsed-ms (ms-since start-nanos)
   :resume     (when (not= status :complete) resume-fn)})

(defn reporting-unenumerated
  "`partial` merged with `(report)`, a map holding `:unenumerated` (the transitive
  predicates whose closure the search did not enumerate), with a `:complete` status read
  as `:incomplete` when that vector is non-empty, and its continuation wrapped the same
  way, so the keys a later step carries are cumulative over every step before it."
  [partial report]
  (let [r (report)]
    (cond-> (merge partial r)
      (and (= :complete (:status partial)) (seq (:unenumerated r)))
      (assoc :status :incomplete)

      (:resume partial)
      (assoc :resume (fn [b] (reporting-unenumerated ((:resume partial) b) report))))))

(defn- collect*
  [xs budget restart delivered unbounded-first?]
  (check-budget! budget)
  (let [max-results (:max-results budget)
        dl          (deadline budget)
        start       (now)
        stop        (fn [acc status next-step]
                      (let [results (persistent! acc)]
                        (from-batch results status start
                                    (fn [b] (next-step b (cond-> delivered restart (into results)))))))]
    (binding [*deadline* (when restart dl)]
      (loop [xs xs, n 0, acc (transient []), unbounded? unbounded-first?]
        (if (and max-results (>= n max-results))
          (stop acc :capped (fn [b seen] (collect* xs b restart seen false)))
          (let [s (cond (and dl (>= (long (now)) (long dl))) ::passed
                        unbounded? (binding [*deadline* nil] (seq xs))
                        :else      (pull xs))]
            (cond
              (identical? ::passed s)
              (stop acc :timeout (fn [b seen] (collect* xs b restart seen false)))

              (identical? ::interrupted s)
              (stop acc :timeout (fn [b seen]
                                   (let [seen-set (set seen)]
                                     (collect* (remove seen-set (restart)) b restart seen true))))

              (nil? s) (from-batch (persistent! acc) :complete start nil)
              :else    (recur (rest s) (inc n) (conj! acc (first s)) false))))))))

(defn collect
  "Realize the lazy seq `xs` under `budget`, returning the partial-result contract.

  Both bounds are checked *before* pulling the next element, so `:max-results` n pulls
  the source n times and a passed deadline stops without over-reading; the element
  under the cursor is never lost — it stays the head of the captured tail, so
  `resume` re-pulls it.  A `nil` / `{}` budget realizes the whole seq (`:complete`).

  `restart`, a 0-arg fn building `xs` afresh, lets a walk inside one pull stop at the
  deadline too: the pulls run with `*deadline*` bound, and a pull a walk interrupts
  (`check-deadline!`) answers `:timeout`.  An interrupted lazy seq cannot be re-pulled (a
  `LazySeq` whose nested realization threw reads as empty afterwards), so the
  continuation rebuilds the stream with `restart`, drops the answers already returned,
  and runs its first pull without the deadline.  Each resume therefore gets past the
  interrupted walk, and a resume loop under a fixed budget terminates.

  `rest`, not `next`: `next` realizes one element *ahead* to decide whether a tail
  exists, so a cap of n would pull n+1 from the source.  `rest` defers that, and the
  cap check sits above the `empty?` that would force it — so an unbounded source is
  bounded without reading past the cap.

  **How many elements that realizes is the source's business, not this loop's.**  n pulls
  realize exactly n elements of an **unchunked** seq, which is what every seq the engine
  hands here is — a `lazy-seq`/`cons` chain out of the solvers and the index, asserted by
  `laziness_test/a-capped-ask-pays-for-the-cap-and-not-for-a-chunk`.  A *chunked* source —
  anything built by `map`/`filter` over a vector or a range — realizes its whole 32-element
  chunk on the first pull whatever the cap says, and no cap check above it can prevent
  that.  So the promise a caller may rely on is the one about the source: n pulls, and
  the tail resumable from where they stopped."
  ([xs budget] (collect* xs budget nil [] false))
  ([xs budget restart] (collect* xs budget restart [] false)))

(defn resume
  "Continue a `:timeout` / `:capped` partial result under a fresh `budget`.  A
  `:complete` result has no continuation, so `resume` returns it unchanged —
  making a `while (:resume …) (recur (resume …))` loop terminate cleanly."
  [partial budget]
  (if-let [f (:resume partial)]
    (f budget)
    partial))

;; ---- the work meter: a cooperative bound on a read that is not one answer stream ----

(def ^:private ^:dynamic *meter*
  "The meter atom of the `metered` read running on this thread, or nil."
  nil)

(defonce ^{:private true
           :tag java.util.concurrent.atomic.AtomicLong
           :doc "How many `metered` reads are running in the process.  `current-meter` reads
  `*meter*` only while this is positive: the first `binding` of `*meter*` marks the var
  thread-bound for the life of the process, after which every read of it, on every
  thread, looks up the thread-local frame."}
  running
  (java.util.concurrent.atomic.AtomicLong.))

(defn- current-meter []
  (when (pos? (.get running)) *meter*))

(defn meter
  "A new work meter for the bounds `opts` reads (`:max-work`, `:max-ms`), started now."
  [opts]
  (atom {:work 0 :max-work (:max-work opts) :start (now) :deadline (deadline opts)
         :found {}}))

(defn metered
  "`(f)` with `*meter*` bound to the meter `m` and `*deadline*` to its deadline, so a walk
  that reads `*deadline*` stops at it too.  A bound running out throws `spend!`'s or
  `check-deadline!`'s signal out of `f`; `exhausted` reads either."
  [m f]
  (.incrementAndGet running)
  (try (binding [*meter* m, *deadline* (:deadline @m)] (f))
       (finally (.decrementAndGet running))))

(defn exhausted
  "The bound that `e` reports running out, `:max-work` or `:max-ms`, when `e` is
  `spend!`'s signal or `check-deadline!`'s; else nil."
  [e]
  (let [data (ex-data e)]
    (or (::exhausted data) (when (contains? data ::deadline) :max-ms))))

(defn spend!
  "Charge one work unit to the running meter.  Throws before the unit when the meter's
  deadline has passed or its `:max-work` units are spent.  A no-op outside `metered`."
  []
  (when-let [m (current-meter)]
    (let [{:keys [work max-work deadline]} @m]
      (cond
        (and deadline (>= (long (now)) (long deadline)))
        (throw (ex-info "metered read: wall-clock budget exhausted" {::exhausted :max-ms}))

        (and max-work (>= (long work) (long max-work)))
        (throw (ex-info "metered read: work budget exhausted" {::exhausted :max-work}))

        :else
        (swap! m update :work inc)))))

(defn checked-call
  "`(f)` between two `spend!` checkpoints, so a deadline passed inside an opaque callback
  stops the read as soon as it returns.  Outside `metered` it is `(f)`."
  [f]
  (if (current-meter)
    (do (spend!)
        (let [result (f)]
          (spend!)
          result))
    (f)))

(defn- metered-seq [xs]
  (lazy-seq
   (spend!)
   (when-let [s (seq xs)]
     (let [x (first s)]
       (spend!)
       (cons x (metered-seq (rest s)))))))

(defn checked-seq
  "`xs` with a `spend!` before and after each pull, or `xs` itself outside `metered`.  A
  chunked source realizes its whole chunk in one pull, and the meter observes that only
  after the pull returns."
  [xs]
  (if (current-meter) (metered-seq xs) xs))

(defn record!
  "Add `x` to the running meter's findings under `k`, which `found` reads however the
  read stopped.  Returns `x`."
  [k x]
  (when-let [m (current-meter)]
    (swap! m update-in [:found k] (fnil conj []) x))
  x)

(defn found
  "The findings `record!` added to meter `m`, as `{k [x …]}` in arrival order."
  [m]
  (:found @m))

(defn snapshot
  "The work meter `m` charged and the milliseconds since it started."
  [m]
  {:work (:work @m) :elapsed-ms (ms-since (:start @m))})
