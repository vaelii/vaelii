;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.progress
  "Progress lines for a long loop, logged at `:info` through Trove.  A loop that ends
  within `first-line-ms` prints nothing; a longer one prints a line each time its elapsed
  time doubles while the doubled time stays within `max-gap-ms`, then one each
  `max-gap-ms`, and a closing line.  A line falls due on a
  tick or on a timer, so a step that ticks nothing for 15 s still prints one.  A reporter
  is a value the loop holds and ticks, opened with `with-open`; no dynamic var carries it.
  A caller follows the loops started under it through `*observer*`.  See
  docs/operations.md, \"Progress lines\"."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.logging :as logging])
  (:import (java.util.concurrent Future ScheduledExecutorService ScheduledThreadPoolExecutor
                                 ThreadFactory TimeUnit)
           (java.util.concurrent.atomic AtomicLong AtomicReference)))

(def first-line-ms
  "How long a loop runs before its first line."
  15000)

(def max-gap-ms
  "The longest wait between two lines of one loop, and the elapsed time past which
  lines stop doubling."
  300000)

(def ^:private max-stride
  "The most ticks between two clock reads."
  1024)

(def ^:private check-every-ns
  "The time the next clock read is aimed at, from the rate measured so far."
  100000000)

(def ^:dynamic *observer*
  "nil, or a function a caller binds to follow the loops started under it: called with
  `{:id :label :done :total}` from the thread that ticks, at most once each
  `observe-every-ms` of a loop's run, and once as it closes when it was called before.  A reporter reads the binding
  in force when it starts.  Beside the log lines, not in place of them."
  nil)

(def ^:private observe-every-ms
  "The least time between two calls of a reporter's `*observer*`."
  1000)

(def ^:private estimate-factor
  "How far, up or down, the projected total time (elapsed plus left) must move from the
  one last logged before a line logs it outside the schedule."
  2.0)

(defn- left-ns
  "The estimated time left after `elapsed` ns at `done` items of `total`, or nil while
  the loop has done less than 0.1% of its total, has no total, or has reached it.  A
  rate read off fewer items names hours or days for a loop that ends in minutes."
  [done total elapsed]
  (let [done (long done)]
    (when (and total (pos? (long total)) (pos? (long elapsed)) (pos? done)
               (>= done (max 1 (quot (long total) 1000))) (< done (long total)))
      (long (* (double elapsed) (/ (double (- (long total) done)) done))))))

(defn- minutes-text
  "`ns` as `12 s`, `4.1 min` or `2.3 h`."
  [ns]
  (let [s (/ (double ns) 1e9)]
    (cond (< s 59.5)   (format "%.0f s" s)
          (< s 3570.0) (format "%.1f min" (/ s 60))
          :else      (format "%.1f h" (/ s 3600)))))

(defn- count-text
  "`n` with thousands separators."
  [n]
  (format "%,d" (long n)))

(defn- line
  "The text of a progress line for `done` items of `total` (nil when unknown) after
  `elapsed` ns, or of the closing line when `done?`."
  [label done total elapsed done?]
  (let [done (long done)]
    (cond
      (and done? (nil? total) (zero? done))
      (str label ": done in " (minutes-text elapsed))

      done?
      (str label ": done, " (count-text done) " in " (minutes-text elapsed))

      (and total (pos? (long total)))
      (let [share (/ (double done) (double total))]
        (str label ": " (count-text done) " of " (count-text total)
             (format " (%.0f%%)" (* 100 share)) ", " (minutes-text elapsed) " in"
             (when-let [left (left-ns done total elapsed)]
               (str ", about " (minutes-text left) " left"))))

      (zero? done)
      (str label ": " (minutes-text elapsed) " in")

      :else
      (str label ": " (count-text done) " done, " (minutes-text elapsed) " in"
           (when (pos? elapsed)
             (format ", %,.0f/s" (/ done (/ (double elapsed) 1e9))))))))

(defn- emit!
  "Log one line of the reporter `r` at `elapsed` ns."
  [r done elapsed done?]
  (let [{:keys [id label total log-ns]} r]
    (trove/log! {:level :info :id id :ns log-ns
                 :msg  (line label done total elapsed done?)
                 :data {:done done :total total :elapsed-ms (quot (long elapsed) 1000000)}})))

(defn- emit-if-due!
  "Log a line of `r` at `done` items and `elapsed` ns when the schedule has one due, and
  move the due time on.  A line also falls due outside the schedule when the projected
  total time stands `estimate-factor` from the one the last line gave, at least
  `first-line-ms` after it.  The thread that moves `:next-ns` or `:shown` logs it; any
  other skips."
  [r done ^long elapsed]
  (let [^AtomicLong next-ns (:next-ns r)
        ^AtomicReference shown (:shown r)
        due (.get next-ns)
        [at est :as prev] (.get shown)
        whole (some-> (left-ns done (:total r) elapsed) (+ elapsed))
        max-gap (* (long max-gap-ms) 1000000)]
    (when (or (and (>= elapsed due)
                   (.compareAndSet next-ns due
                                   (+ elapsed (if (<= (* 2 elapsed) max-gap) (max elapsed 1) max-gap))))
              (and whole est
                   (>= (- elapsed (long at)) (* (long first-line-ms) 1000000))
                   (>= (max (/ (double whole) (long est)) (/ (double (long est)) whole))
                       (double estimate-factor))
                   (.compareAndSet shown prev [elapsed whole])))
      (.set shown [elapsed whole])
      (.incrementAndGet ^AtomicLong (:lines r))
      (emit! r done elapsed false))))

(defn- observe!
  "Call `r`'s observer (`*observer*`) with its count `done`, when it has one and
  `observe-every-ms` has passed since the last call at `elapsed` ns, or when `force?`.
  The thread that moves `:observed` calls it; any other skips."
  [r done ^long elapsed force?]
  (when-let [f (:observer r)]
    (let [^AtomicLong o (:observed r)
          prev (.get o)]
      (when (and (or force? (>= (- elapsed prev) (* (long observe-every-ms) 1000000)))
                 (.compareAndSet o prev elapsed))
        (f {:id (:id r) :label (:label r) :done done :total (:total r)})))))

(defn- check!
  "Read the clock for `r` at `done` items: log a line when the next one is due, call its
  observer when one is due (`observe!`), and set the count of the next clock read from
  the rate so far.  The thread that moves `:check-at` reads the clock; any other skips."
  [r ^long done]
  (let [^AtomicLong at (:check-at r)
        seen (.get at)]
    (when (and (>= done seen) (.compareAndSet at seen Long/MAX_VALUE))
      (let [elapsed (- (long ((:clock r))) (long (:t0 r)))]
        (emit-if-due! r done elapsed)
        (observe! r done elapsed false)
        (.set at (+ done (long (if (pos? elapsed)
                                 (max 1 (min (long max-stride)
                                             (long (/ (* (double done) check-every-ns) elapsed))))
                                 1))))))))

(defn tick!
  "Count `n` items (one by default) done in the loop `r` reports, and log a line when one
  is due.  Safe from several threads."
  ([r] (tick! r 1))
  ([r n]
   (let [done (.addAndGet ^AtomicLong (:done r) (long n))]
     (when (>= done (.get ^AtomicLong (:check-at r)))
       (check! r done))
     nil)))

(defn tick-to!
  "Count the loop `r` reports up to `n` items done, for a caller that reads a running
  total rather than counting each item.  A total at or below the count already reached
  counts nothing."
  [r n]
  (let [d (- (long n) (.get ^AtomicLong (:done r)))]
    (when (pos? d) (tick! r d))
    nil))

(defn on-progress
  "An `:on-progress` callback for a forward-chaining run (`chain/chain`) that counts the
  loop `r` reports up to the run's `:derived` total."
  [r]
  (fn [{:keys [derived]}] (tick-to! r (or derived 0))))

(defonce ^:private ^ScheduledExecutorService timer
  (doto (ScheduledThreadPoolExecutor.
         1 (reify ThreadFactory
             (newThread [_ runnable]
               (doto (Thread. ^Runnable runnable "vaelii-progress") (.setDaemon true)))))
    (.setRemoveOnCancelPolicy true)))

(defn- schedule!
  "Run `(task)` `delay-ns` from now unless the reporter `r` is closed."
  [r task ^long delay-ns]
  (let [^AtomicReference slot (:timer r)
        cur (.get slot)]
    (when-not (= ::closed cur)
      (let [f (.schedule timer ^Runnable task (max 1 delay-ns) TimeUnit/NANOSECONDS)]
        (when-not (.compareAndSet slot cur f)
          (.cancel f false))))))

(defn- on-timer!
  "The timer's check of `r`: log a line when one is due, at the count reached so far, and
  run again when the next one is.  While the log drops `:info` (`logging/drops?`), the
  check logs nothing and runs again `first-line-ms` later at the earliest."
  [r task]
  (let [elapsed (- (long ((:clock r))) (long (:t0 r)))
        quiet?  (logging/drops? :info)]
    (when-not quiet?
      (emit-if-due! r (.get ^AtomicLong (:done r)) elapsed))
    (schedule! r task (cond-> (- (.get ^AtomicLong (:next-ns r)) elapsed)
                        quiet? (max (* (long first-line-ms) 1000000))))))

(defn done!
  "Close the loop `r` reports: stop its timer, log the closing line when a progress line
  was logged, and call its observer with the count reached when it was called before."
  [r]
  (let [prev (.getAndSet ^AtomicReference (:timer r) ::closed)]
    (when (instance? Future prev) (.cancel ^Future prev false)))
  (let [done    (.get ^AtomicLong (:done r))
        elapsed (- (long ((:clock r))) (long (:t0 r)))]
    (when (pos? (.get ^AtomicLong (:lines r)))
      (emit! r done elapsed true))
    (when (pos? (.get ^AtomicLong (:observed r)))
      (observe! r done elapsed true)))
  nil)

(defn- timer-task
  "The task the timer runs for `r`: `on-timer!` under the thread bindings in force here.
  The task runs in a clone of this thread's binding frame, which shares the bindings rather
  than copying each one, as `future` conveys them, and restores the timer thread's own frame
  after it."
  [r]
  (let [frame (clojure.lang.Var/cloneThreadBindingFrame)
        task  (promise)]
    (deliver task (fn []
                    (let [own (clojure.lang.Var/getThreadBindingFrame)]
                      (clojure.lang.Var/resetThreadBindingFrame frame)
                      (try (on-timer! r @task)
                           (finally (clojure.lang.Var/resetThreadBindingFrame own))))))
    @task))

(defrecord Reporter [id label log-ns total clock t0 ^AtomicLong done ^AtomicLong check-at
                     ^AtomicLong next-ns ^AtomicReference shown ^AtomicLong lines
                     ^AtomicReference timer observer ^AtomicLong observed]
  java.io.Closeable
  (close [r] (done! r)))

(defn start
  "A reporter for a loop over `total` items (nil when unknown), its lines logged under
  the keyword `id` and opening with `label`.  The clock starts here.  Closing it
  (`with-open`) logs the closing line (`done!`), and a reporter left open logs on.
  `opts`: `:clock`, a zero-argument fn answering nanoseconds (`System/nanoTime` by
  default), and `:timer?`, whether a timer logs the lines no tick does (by default under
  the default clock and a `total` other than 0).  The timer logs under every binding in
  force here.  A level raised mid-loop prints its next timer line.  The `*observer*` in
  force here is the reporter's."
  (^java.io.Closeable [id label total] (start id label total nil))
  (^java.io.Closeable [id label total {:keys [clock] :as opts}]
   (let [timer? (get opts :timer? (and (nil? clock) (not= 0 total)))
         clock  (or clock #(System/nanoTime))
         r      (->Reporter id label (or (some-> id namespace) (str *ns*)) (some-> total long)
                            clock (long (clock))
                            (AtomicLong. 0) (AtomicLong. 1)
                            (AtomicLong. (* (long first-line-ms) 1000000))
                            (AtomicReference. [0 nil]) (AtomicLong. 0) (AtomicReference. nil)
                            *observer* (AtomicLong. 0))]
     (when timer?
       (schedule! r (timer-task r) (* (long first-line-ms) 1000000)))
     r)))

(defn each
  "`coll` as a lazy seq that ticks `r` once per element it hands out, for a loop written
  as a `doseq`, `run!` or `reduce` over `coll`.  Unchunked, so the count is the element
  the loop is on rather than the end of a 32-element chunk."
  [r coll]
  (lazy-seq
   (when-let [s (seq coll)]
     (tick! r)
     (cons (first s) (each r (rest s))))))
