;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.jobs
  "Long work, as jobs: one registry, one progress reading, one cancel.

  Three things this process does take minutes rather than milliseconds — filling a KB
  from a corpus, writing one back out, and joining every rule over everything stored.
  Each of them wants the same four capabilities, and they are the only four: run on a
  thread of its own so the pages keep answering, say where it has got to, stop when
  asked, and leave a report somebody can read afterwards.  That shape is here once.

  **A job** is `{:id :label :kind :status :progress :started :finished :error :summary
  :result-url}`, plus a cancel flag and the future, which no view carries.  `submit`
  returns the id; `job` reads one; `jobs` lists them, newest first.  The caller's `work`
  is handed a `progress!` fn and nothing else: what it records shows up under
  `:progress`, and what it *throws* is how cancellation lands, because a tight assert
  loop has no other point at which stopping is safe.

  **One status vocabulary**, whatever the job is doing:

      :running → :cancelling → :done | :cancelled | :failed

  `:cancelling` is the honest middle: `cancel!` sets the flag and returns, and the work
  keeps running until it reaches its next progress report — which, for a phase that
  reports none (opening a large store scans its whole record log before it says
  anything), can be a while.

  **The single writer stays single.**  `:writes` names the KB a job writes, or `true` for
  one it has not opened yet, and **one writing job runs at a time**: a second is refused
  with a message naming the job that holds the writer.  Two interleaved writers are not
  serializable (docs/storage.md, the single-writer contract), and a registry that let two
  through would be a way around the contract rather than a place to watch it from.
  `writes-kb?` is the other half of the same question, asked by identity, so a job filling
  one KB never blocks a write to another.

  **Cancellation is cooperative, and for a KB-writing job that is not negotiable.**  A
  thread interrupt landing mid-cascade on a durable store surfaces as
  `ClosedByInterruptException` and can leave a torn removal, so a job with `:writes` is
  flagged and never interrupted however long it takes to notice.  A job that writes
  nothing may say `:interruptible? true` and be cancelled the hard way as well; the
  registry checks both, so the two can never be confused for one another.  A job's thread
  is the *pool's* once its body has unwound, so the hard tier is fenced: the body
  publishes `:released` under the job's `:monitor` and `cancel!` re-reads it there, which
  is what stops an interrupt aimed at a job that has already finished from landing on
  whatever the pool runs next.

  **A finished job's report outlives the job**, for an hour — long enough to read what it
  did, since the page that would have shown it is usually the page you navigated away
  from.  Nothing *unsettled* is ever dropped, at any age: forgetting a job is releasing
  its writer claim, and a thread that is still running is still writing.  So a wedged job
  keeps its place and keeps counting towards the running badge, which is the truth about
  the process — better than a store two writers took turns on."
  (:require [taoensso.trove :as trove]))

(def fast-path-ms
  "How long a caller may wait for a job before answering with a progress page instead of
  its result.  A quarter of a second: the point is that a small operation does **not**
  acquire a spinner and a second round trip, since a tool where every action costs one
  feels slower than the thing it replaced."
  250)

(def ^:private finished-ttl-ms
  "How long a settled job's report stays in the registry.  There is deliberately no
  companion bound for an *unsettled* one — `sweep` says why."
  (* 60 60 1000))

(defonce ^:private state (atom {:jobs {} :order [] :next-id 0}))

;; `submit`'s writer claim is a read-test-write across `@state` — the test that no other
;; job holds the writer and the `swap!` that registers this one — which one `swap!` cannot
;; express, since it refuses rather than retries.  This makes the two one step.
(defonce ^:private claim-monitor (Object.))

(def ^:private cancelled
  "The `:type` a cancelled `progress!` throws, and the only thing that tells a cancelled
  job from a failed one."
  ::cancelled)

(defn cancelled?
  "Was `t` thrown by a **cancellation** rather than by a failure — the `progress!` throw
  `cancel!` arms, or the interrupt it sends a job that writes nothing?

  Public because a caller filing a status of its own beside the registry's — the catalog,
  onto the entry a load leaves behind — has to classify a throw exactly as `submit` does,
  and the alternative is this literal written in two places."
  [t]
  (or (= cancelled (:type (ex-data t)))
      (instance? InterruptedException t)))

(defn- now [] (System/currentTimeMillis))

(defn- settled? [j] (not (#{:running :cancelling} (:status j))))

(defn- view
  "A job as something safe to render or send: the cancel flag, the future, the thread and
  its release fence, and the KB it writes all dropped, elapsed time filled in.  `:writes?`
  survives the dropping because it is what decides the cancel tier and what a refusal is
  about; the KB itself is nobody's to hand out."
  [j]
  (when j
    (-> (dissoc j :cancel :future :thread :writes :monitor :released)
        (assoc :writes?    (some? (:writes j))
               :elapsed-ms (- (or (:finished j) (now)) (:started j))))))

(defn- sweep
  "Drop the reports nobody can still be reading.  Runs on `submit`, which is the only
  moment the registry grows.

  **Only a settled job is ever dropped**, and no age changes that.  Forgetting a job is
  releasing its writer claim — `writer` and `writes-kb?` are both reads of this map — so
  dropping one whose thread is still running admits a second writer to a KB the first is
  still writing, which is the single thing the claim exists to prevent (docs/storage.md,
  the single-writer contract).  A wedged job therefore keeps its place and keeps counting
  towards the running badge: a thread that will never return is a true thing to say about
  this process, and saying it is better than a store two writers took turns on."
  [s]
  (let [cutoff (- (now) finished-ttl-ms)
        live?  (fn [j] (or (not (settled? j))
                           (> (or (:finished j) (:started j)) cutoff)))
        kept   (into {} (filter (comp live? val)) (:jobs s))]
    (assoc s :jobs kept :order (vec (filter kept (:order s))))))

(defn- update-job!
  "Apply `f` to job `id` — **and only while the registry still holds it**.  Every write to
  a job goes through here, because a `swap!` reaching `[:jobs id]` for an id the sweep or
  `reset-registry!` has already dropped does not fail: it *recreates* the job as a
  fragment, a `:status` with no `:started` for `view` to subtract from, absent from
  `:order` and so invisible to every listing that would have shown it up."
  [id f]
  (swap! state (fn [s] (cond-> s (contains? (:jobs s) id) (update-in [:jobs id] f))))
  nil)

(defn job
  "Job `id`, as a view, or nil once it has been swept."
  [id]
  (view (get-in @state [:jobs id])))

(defn jobs
  "Every job the registry still holds, newest first — the order `/jobs` lists them in."
  []
  (let [{js :jobs :keys [order]} @state]
    (into [] (comp (map js) (keep view)) (reverse order))))

(defn running
  "The jobs that have not settled, newest first.  What a panel polls on, and what the
  running badge counts."
  []
  (into [] (remove settled?) (jobs)))

(defn latest
  "The newest job of `kind`, settled or not — the last export's report is what the export
  panel shows, and it is worth keeping visible until the next one replaces it."
  [kind]
  (first (filter #(= kind (:kind %)) (jobs))))

(defn writer
  "The running job that holds this process's writer, or nil.  What `submit` refuses a
  second writing job against, and what a refusal names."
  []
  (first (filter :writes? (running))))

(defn writes-kb?
  "Is a job writing **this** KB, by identity?  Reading beside a writer is sound and
  writing beside one is not, and the question is about the KB rather than about the
  process: a job filling one KB is no reason to refuse a write to another."
  [kb]
  (let [{:keys [jobs]} @state]
    (boolean (and kb
                  (some (fn [j] (and (not (settled? j)) (identical? kb (:writes j))))
                        (vals jobs))))))

(defn- progress-fn
  "The `:on-progress` callback a job's work is handed: record where it has got to, and
  throw when it has been asked to stop.  Throwing is the whole of cancellation — every
  long operation in this engine takes an `:on-progress` and none of them has another
  point at which stopping leaves a readable KB or a directory rather than a file
  half-written."
  [id cancel]
  (fn [p]
    ;; the message is what the card shows beside the status, so it says what stopping here
    ;; means rather than repeating the status word
    (when @cancel
      (throw (ex-info "stopped at a progress report, as asked — what had landed stays"
                      {:type cancelled})))
    (update-job! id #(update % :progress merge (assoc p :at (now))))))

(defn submit
  "Run `work` as a job and return its id.  `work` takes one argument, the `progress!` fn
  above, and its return value is filed as the job's `:summary` (a map may carry a
  `:result-url`, which then overrides the one submitted).

  `opts`:

  | key | |
  |---|---|
  | `:label` | what the job is called on screen |
  | `:kind` | `:load` / `:export` / `:chain` — what a panel filters on |
  | `:writes` | the KB this job writes, or `true` for one it will open |
  | `:interruptible?` | may its thread be interrupted on cancel?  Only for a job that writes nothing |
  | `:progress` | the first progress reading, before the work has said anything |
  | `:result-url` | where to send a reader when it finishes |

  Any other key is carried through onto the job, which is how the export's destination
  and the entry's name reach the panel that renders them.

  Throws `{:type :job-busy}` when `:writes` is asked for and another job already holds
  the writer.  The refusal names the holder rather than queueing behind it: two writers
  are not serializable, and a queue would make a load's wall-clock reading mean whatever
  was in front of it."
  [{:keys [label kind writes progress result-url] :as opts} work]
  (let [cancel (atom false)
        ;; the work's own thread, published by the work itself.  `cancel!` interrupts
        ;; *that* rather than calling `future-cancel`, so the body always reaches its own
        ;; catch and files its own status — a cancelled future's `deref` throws instead of
        ;; answering, which would have `wait` return before the job had settled.
        thread (promise)
        ;; the fence around that interrupt.  A `future` runs on a pooled thread, so the
        ;; thread stops being this job's the moment the body unwinds; `released` says so
        ;; and `monitor` is what makes the saying and the interrupting one step.
        released (atom false)
        monitor  (Object.)
        id     (locking claim-monitor
                 (when writes
                   (when-let [w (writer)]
                     (throw (ex-info (str "job " (:id w) " (" (:label w) ") is already"
                                          " running, and it is this process's one writer")
                                     {:type :job-busy :holder (:id w) :label (:label w)}))))
                 (let [id (str (:next-id (swap! state update :next-id inc)))]
                   (swap! state (fn [s]
                                  (-> (sweep s)
                                      (assoc-in [:jobs id]
                                                (merge (dissoc opts :progress)
                                                       {:id id :label label :kind kind
                                                        :status :running
                                                        :progress (or progress {:phase :starting :done 0})
                                                        :result-url result-url
                                                        :started (now)
                                                        :cancel cancel
                                                        ;; registered with the job rather
                                                        ;; than filed after it starts, so a
                                                        ;; cancel arriving in between reads
                                                        ;; a fence rather than a nil one
                                                        :thread thread
                                                        :monitor monitor
                                                        :released released}))
                                      (update :order conj id))))
                   id))
        f      (future
                 (deliver thread (Thread/currentThread))
                 (try
                   (let [summary (work (progress-fn id cancel))]
                     (update-job! id
                                  (fn [j]
                                    (-> (merge j (cond-> {:status :done :finished (now)}
                                                   (map? summary)        (assoc :summary summary)
                                                   (:result-url summary) (assoc :result-url (:result-url summary))))
                                        ;; the last reading a finished job took is the phase it
                                        ;; finished *in*, which gives the impression that it stopped there.
                                        ;; A failed or cancelled one keeps its last reading, since
                                        ;; where it got to is the whole of what it has to say
                                        (assoc-in [:progress :phase] :done))))
                     (trove/log! {:level :info :id ::done
                                  :msg (str "job " id " (" label ") finished")
                                  :data (when (map? summary) summary)}))
                   (catch Throwable t
                     ;; an interrupt is what `cancel!` does to a job that writes nothing,
                     ;; so it is indistinguishable from a cancellation and not as a failure
                     (let [c? (cancelled? t)]
                       (update-job! id #(merge % {:status (if c? :cancelled :failed)
                                                  :finished (now)
                                                  :error (or (.getMessage t) (str (class t)))}))
                       (when-not c?
                         (trove/log! {:level :error :id ::failed
                                      :msg (str "job " id " (" label ") failed: "
                                                (.getMessage t))}))))
                   (finally
                     ;; a `future` runs on a pooled thread, so an interrupt this job was
                     ;; sent and never blocked long enough to observe would otherwise be
                     ;; delivered to whatever ran next on it.  Reading the flag clears it —
                     ;; and saying `released` in the same breath, under the monitor
                     ;; `cancel!` re-reads it under, is what stops one being sent *after*
                     ;; this point, where no clearing of ours could reach it.
                     (locking monitor
                       (reset! released true)
                       (Thread/interrupted)))))]
    (update-job! id #(assoc % :future f))
    id))

(defn- interrupt-jobs-own-thread!
  "Interrupt the thread job `j`'s work is running on — and **only while that thread is
  still the job's**.  A `future` runs on a pooled thread, so the moment the body unwinds
  the thread goes back to the pool and an interrupt aimed at the job lands on whatever
  runs next: a task nobody cancelled, unwinding on somebody else's request.  `submit`'s
  `finally` publishes `:released` under `:monitor`, this takes the same monitor, and so
  the two orders are the only two — the interrupt is delivered while the thread is still
  the job's, or it is not sent at all.

  The wait for the thread to publish itself is bounded, because a thread that has not
  published one yet is a job the cooperative flag already covers, and waiting on it
  forever would hang the request that asked for the cancel."
  [j]
  (let [monitor  (:monitor j)
        released (:released j)]
    (try
      (locking monitor
        (when-not @released
          (when-let [published (:thread j)]
            (some-> ^Thread (deref published 1000 nil) .interrupt))))
      (catch InterruptedException _
        ;; that bounded wait is itself interruptible, and it clears *this* thread's flag on
        ;; the way out.  Put it back — a caller asking a job to stop is no reason for it to
        ;; lose an interrupt of its own, and the web handler above this would otherwise see
        ;; the exception instead of an answer — and read the job as one that never published
        ;; a thread, which the cooperative flag already covers.
        (.interrupt (Thread/currentThread)))))
  nil)

(defn cancel!
  "Ask job `id` to stop at its next progress report, and answer whether there was one to
  ask.  `!` because of what a stopped job leaves behind: a KB holding a prefix of a load
  or of a chaining run, or a directory holding part of a dump.

  **A job that has already settled answers false**, exactly as an id the registry never
  held does.  The registry keeps a settled job's report for an hour, so *is it still here*
  and *was there anything to stop* are different questions, and the second is the
  one a caller acts on: a caller that cannot tell them apart reports a cancellation over a
  load that finished or a dump already written.  There is nothing to undo either way —
  asking a finished job to stop changes nothing about it — so the answer is the whole of
  what this reports.

  A job that writes a KB is flagged and **never** interrupted, however long it takes to
  notice — an interrupt landing mid-cascade on a durable store tears the write it lands
  in.  A job that writes nothing and says `:interruptible? true` is flagged *and*
  interrupted, so it unwinds promptly rather than at a report it may not reach.  Both are
  checked, not one: a job that says it may be interrupted and writes a KB anyway is not
  interrupted, since the reason is about the store rather than about the promise.

  Every decision here is made from **one** read of the registry, which by the time it is
  acted on may name a job that has settled — so the interrupt is fenced rather than
  trusted to that read (`interrupt-jobs-own-thread!`), and this returns an answer rather
  than an `InterruptedException` when the caller's own thread is interrupted meanwhile."
  [id]
  (boolean
   (when-let [j (get-in @state [:jobs id])]
     (when-not (settled? j)
       (reset! (:cancel j) true)
       ;; guarded inside the swap: the job's own thread may file its terminal status
       ;; between the read above and this write, and :cancelling stamped over :done
       ;; is a job that never settles — the sweep keeps it, `writer` keeps naming it,
       ;; and every later writing job is refused against a job that already finished
       (update-job! id (fn [j] (cond-> j (not (settled? j)) (assoc :status :cancelling))))
       (when (and (:interruptible? j) (nil? (:writes j)))
         (interrupt-jobs-own-thread! j))
       true))))

(defn wait
  "Block up to `ms` for job `id` to settle, then answer its view — settled or not, so the
  caller decides what to do about a job that is still going.  This is what the fast path
  is: submit, wait `fast-path-ms`, and answer with the result if it is already there."
  [id ms]
  (when-let [f (:future (get-in @state [:jobs id]))]
    (deref f ms ::timeout))
  (job id))

(def ^:private reset-wait-ms
  "How long `reset-registry!` gives a cancelled job to settle before giving up on it —
  the same bound `unload!` gives a loader, for the same cooperative cancel."
  30000)

(defn reset-registry!
  "Cancel every job, **wait for each to settle**, and forget the ones that did.  For a
  process shutting down and for tests; nothing in the browser calls it.

  The wait is the point.  Forgetting a job releases its writer claim — `writer` and
  `writes-kb?` are reads of this map — so a running job dropped here is a writer nobody
  can see: the next writing job is admitted beside it, and a test fixture clears the KB
  its thread is still forward-chaining into.  That is exactly the drop `sweep` refuses,
  and this is held to the same rule.  Cancellation is cooperative, so every job gets up
  to `reset-wait-ms` to reach a progress report; one that does not is **kept**, logged,
  and goes on counting as the writer — a thread still running is still writing, and
  saying so is better than a store two writers took turns on.  The id counter restarts
  only when nothing is kept, so a kept job's id is never handed out twice.

  The bound is **per job**, not a budget shared across them: one wedged job would spend a
  shared deadline whole and leave every job behind it none, so a job that would have
  settled in a millisecond is kept, keeps the writer claim, and refuses every later write
  to that KB for the life of the process.  Cancel is issued to all of them first, so the
  waits overlap and the wall time is the slowest job's, not the sum — except where jobs
  genuinely do not settle, and there the reset is reporting a real leak per job."
  []
  (let [ids (:order @state)]
    (doseq [id ids] (cancel! id))
    (doseq [id ids] (wait id reset-wait-ms))
    (let [kept (:jobs (swap! state
                             (fn [s]
                               (let [kept (into {} (remove (comp settled? val)) (:jobs s))]
                                 (if (empty? kept)
                                   {:jobs {} :order [] :next-id 0}
                                   (assoc s :jobs kept :order (filterv kept (:order s))))))))]
      (doseq [j (vals kept)]
        (trove/log! {:level :warn :id ::not-settled
                     :msg (str "job " (:id j) " (" (:label j) ") did not stop within "
                               reset-wait-ms " ms and is kept — its thread still holds "
                               "whatever it holds")}))
      nil)))
