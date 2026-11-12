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
  :result-url}`, plus a cancel flag and the future, which no public job carries.  `submit`
  returns the id; `job` reads one; `jobs` lists them, newest first.  The caller's `work`
  is handed a `progress!` fn and nothing else: what it records shows up under
  `:progress`, and what it *throws* is how cancellation lands, because a tight assert
  loop has no other point at which stopping is safe.

  **One status vocabulary**, whatever the job is doing:

      :running → :cancelling → :done | :cancelled | :failed

  `:cancelling` is the state between the request and the stop: `cancel!` sets the flag and
  returns, and the work keeps running until it reaches its next progress report — which,
  for a phase that reports none (opening a large store scans its whole record log before
  it says anything), can be a while.

  **The single writer stays single.**  `:writes` names the KB a job writes, or `true` for
  one it has not opened yet, and **one writing job runs at a time**: a second is refused
  with a message naming the job that holds the writer.  Two interleaved writers are not
  serializable (docs/storage.md, the single-writer contract), and a registry that let two
  through would be a way around the contract rather than a place to watch it from.
  `writes-kb?` is the other half of the same question, asked by identity, so a job filling
  one KB is never a reason to refuse a write to another.  The browser's write monitor is
  a separate thing: it is process-wide, and a chaining job holds it for its whole run, so
  a write to any KB waits for the chain (docs/web.md).

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
  from.  The registry holds the newest `max-settled-jobs` settled reports at most, so a
  caller submitting no-op jobs holds a bounded number of them.  Nothing *unsettled* is ever dropped, at any age: forgetting a job is releasing
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

(def ^:private max-settled-jobs
  "How many settled reports the registry holds, newest by submission first; `sweep`
  drops the rest whatever their age.  Unsettled jobs are outside the count: one writing
  job runs at a time and one export, so their number is bounded already."
  100)

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
  "Was `t` thrown by a **cancellation** rather than by a failure: the `progress!` throw
  `cancel!` arms?  An interrupt is a cancellation only for a job that writes nothing and
  whose cancel flag is set, which `submit` reads beside this; a job that writes is never
  interrupted by `cancel!`, so for it this answer is the whole one.

  Public because a caller filing a status of its own beside the registry's — the catalog,
  onto the entry a load leaves behind — has to classify a throw exactly as `submit` does,
  and the alternative is this literal written in two places."
  [t]
  (= cancelled (:type (ex-data t))))

(defn- now [] (System/currentTimeMillis))

(defn- settled? [j] (not (#{:running :cancelling} (:status j))))

(defn- public-job
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
  "Drop the settled reports older than `finished-ttl-ms`, and those past the newest
  `max-settled-jobs`.  Runs on `submit` and on every listing read (`jobs`).

  **Only a settled job is ever dropped.**  Forgetting a job releases its writer claim
  (`writer` and `writes-kb?` read this map), so dropping a running one admits a second
  writer to a KB the first is still writing (docs/storage.md, the single-writer
  contract).  A wedged job keeps its place and keeps counting towards the running badge."
  [s]
  (let [cutoff  (- (now) finished-ttl-ms)
        js      (:jobs s)
        recent  (into #{}
                      (comp (filter #(let [j (js %)]
                                       (and j (settled? j)
                                            (> (or (:finished j) (:started j)) cutoff))))
                            (take max-settled-jobs))
                      (rseq (vec (:order s))))
        kept    (into {} (filter (fn [[id j]] (or (not (settled? j)) (recent id)))) js)]
    (assoc s :jobs kept :order (vec (filter kept (:order s))))))

(defn- update-job!
  "Apply `f` to job `id` — **and only while the registry still holds it**.  Every write to
  a job goes through here, because a `swap!` reaching `[:jobs id]` for an id the sweep or
  `reset-registry!` has already dropped does not fail: it *recreates* the job as a
  fragment, a `:status` with no `:started` for `public-job` to subtract from, absent from
  `:order` and so invisible to every listing that would have shown it up."
  [id f]
  (swap! state (fn [s] (cond-> s (contains? (:jobs s) id) (update-in [:jobs id] f))))
  nil)

(defn job
  "Job `id`, as a public job, or nil once it has been swept."
  [id]
  (public-job (get-in @state [:jobs id])))

(defn jobs
  "Every job the registry still holds, newest first — the order `/jobs` lists them in.
  Sweeps the registry first."
  []
  (let [{js :jobs :keys [order]} (swap! state sweep)]
    (into [] (comp (map js) (keep public-job)) (reverse order))))

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

(defn kb-writer
  "The unsettled job whose `:writes` is **this** KB, by identity, as a public job — or nil.
  What a refusal about `kb` names: the catalog's unload refuses `:still-writing` with it."
  [kb]
  (when kb
    (public-job (some (fn [j] (when (and (not (settled? j)) (identical? kb (:writes j))) j))
                      (vals (:jobs @state))))))

(defn writes-kb?
  "Is a job writing **this** KB, by identity?  Reading beside a writer is sound and
  writing beside one is not, and the question is about the KB rather than about the
  process: a job filling one KB is no reason to refuse a write to another."
  [kb]
  (some? (kb-writer kb)))

(defn- progress-fn
  "The `:on-progress` callback a job's work is handed: record where it has got to, and
  throw when it has been asked to stop.  Throwing is the whole of cancellation — every
  long operation in this engine takes an `:on-progress` and none of them has another
  point at which stopping leaves a readable KB or a directory rather than a file
  half-written."
  [id cancel]
  (fn [p]
    ;; filed before the cancel is honoured: the reading is what had landed by this report,
    ;; and the card's "reached" is the only account of it a cancelled job leaves
    (update-job! id #(update % :progress merge (assoc p :at (now))))
    ;; the message is what the card shows beside the status, so it says what stopping here
    ;; means rather than repeating the status word
    (when @cancel
      (throw (ex-info "stopped at a progress report, as asked — what had landed stays"
                      {:type cancelled})))))

(defn submit
  "Run `work` as a job and return its id.  `work` takes one argument, the `progress!` fn
  above, and its return value is filed as the job's `:summary` (a map may carry a
  `:result-url`, which then overrides the one submitted).

  `opts`:

  | key | |
  |---|---|
  | `:label` | what the job is called on screen |
  | `:kind` | `:load` / `:export` / `:chain` / `:sync` / `:edit` / `:backup` / `:list` / `:quality` / `:blocks` — what a panel filters on |
  | `:writes` | the KB this job writes, or `true` for one it will open |
  | `:interruptible?` | may its thread be interrupted on cancel?  Only for a job that writes nothing |
  | `:progress` | the first progress reading, before the work has said anything |
  | `:result-url` | where to send a reader when it finishes |

  Any other key is carried through onto the job (the export's destination, the entry's
  name).  Throws `{:type :job-busy}` when `:writes` is asked for and another job already
  holds the writer; the refusal names the holder and queues nothing."
  [{:keys [label kind writes progress result-url] :as opts} work]
  (let [cancel (atom false)
        ;; the work's own thread, published by the work itself.  `cancel!` interrupts
        ;; *that* rather than calling `future-cancel`: a cancelled future's `deref` throws,
        ;; which would have `wait` return before the job had settled.
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
                                        ;; finished *in*, which looks like a stop there.
                                        ;; A failed or cancelled one keeps its last reading,
                                        ;; which is where it got to
                                        (assoc-in [:progress :phase] :done))))
                     (trove/log! {:level :info :id ::done
                                  :msg (str "job " id " (" label ") finished")
                                  :data (when (map? summary) summary)}))
                   (catch Throwable t
                     ;; a cancellation only when `cancel!` set the flag: an interrupt is
                     ;; what `cancel!` sends a job that writes nothing, and an interrupt
                     ;; from anywhere else is a failure of the work
                     (let [c? (or (cancelled? t)
                                  (and @cancel (instance? InterruptedException t)))]
                       (update-job! id #(merge % {:status (if c? :cancelled :failed)
                                                  :finished (now)
                                                  :error (or (.getMessage t) (str (class t)))}))
                       (when-not c?
                         (trove/log! {:level :error :id ::failed
                                      :msg (str "job " id " (" label ") failed: "
                                                (.getMessage t))}))))
                   (finally
                     ;; The arm that files a status can itself throw (an
                     ;; `OutOfMemoryError` while it builds the status map).  A job left
                     ;; `:running` then holds the writer claim for the life of the
                     ;; process, so a job still unsettled here is filed `:failed`.
                     ;;
                     ;; An interrupt this job was sent and never observed would be
                     ;; delivered to whatever ran next on the pooled thread.  Reading the
                     ;; flag clears it, and `released` under the monitor `cancel!` re-reads
                     ;; stops one being sent after this point.
                     (locking monitor
                       (when (some-> (get-in @state [:jobs id]) settled? not)
                         (update-job! id #(cond-> % (not (settled? %))
                                                  (merge {:status :failed :finished (now)
                                                          :error "the job ended without filing a status"})))
                         (trove/log! {:level :error :id ::unfiled
                                      :msg (str "job " id " (" label ") ended without filing a"
                                                " status; filed :failed")}))
                       (reset! released true)
                       ;; a settled job keeps `:writes?` and no reference to the KB it
                       ;; wrote, which its report outlives by up to `finished-ttl-ms`
                       (update-job! id #(cond-> % (some? (:writes %)) (assoc :writes true)))
                       (Thread/interrupted)))))]
    (update-job! id #(assoc % :future f))
    id))

(defn- interrupt-jobs-own-thread!
  "Interrupt the thread job `j`'s work is running on, **only while that thread is still
  the job's**.  A `future` runs on a pooled thread, so once the body unwinds an interrupt
  aimed at the job would land on whatever runs next.  `submit`'s `finally` publishes
  `:released` under `:monitor` and this takes the same monitor, so the interrupt is
  delivered while the thread is still the job's, or not sent.  The wait for the thread to
  publish itself is bounded: a job with no thread yet is covered by the cooperative flag."
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
        ;; the way out.  Put it back, so a caller asking a job to stop keeps an interrupt of
        ;; its own and the web handler above this sees an answer, not the exception; then
        ;; read the job as one that never published a thread, which the cooperative flag
        ;; already covers.
        (.interrupt (Thread/currentThread)))))
  nil)

(defn cancel!
  "Ask job `id` to stop at its next progress report, and answer whether there was one to
  ask.  `!` because of what a stopped job leaves behind: a KB holding a prefix of a load
  or of a chaining run, or a directory holding part of a dump.

  **A job that has already settled answers false**, as an id the registry never held does:
  the registry keeps a settled job's report for an hour, and the caller acts on *was there
  anything to stop*, not *is it still here*.

  A job that writes a KB is flagged and **never** interrupted, since an interrupt landing
  mid-cascade on a durable store tears the write.  A job that writes nothing and says
  `:interruptible? true` is flagged *and* interrupted.  A job that says it may be
  interrupted and writes a KB anyway is not interrupted.

  Every decision is made from **one** read of the registry, so the interrupt is fenced
  (`interrupt-jobs-own-thread!`), and this returns an answer rather than an
  `InterruptedException` when the caller's own thread is interrupted meanwhile."
  [id]
  (boolean
   (when-let [j (get-in @state [:jobs id])]
     (when-not (settled? j)
       (reset! (:cancel j) true)
       ;; guarded inside the swap: the job's own thread may file its terminal status
       ;; between the read above and this write, and :cancelling written over :done
       ;; is a job that never settles (the sweep keeps it, `writer` keeps naming it, and
       ;; every later writing job is refused)
       (update-job! id (fn [j] (cond-> j (not (settled? j)) (assoc :status :cancelling))))
       (when (and (:interruptible? j) (nil? (:writes j)))
         (interrupt-jobs-own-thread! j))
       true))))

(defn wait
  "Block up to `ms` for job `id` to settle, then answer its public job — settled or not, so the
  caller decides what to do about a job that is still going.  This is what the fast path
  is: submit, wait `fast-path-ms`, and answer with the result if it is already there.
  Without `ms`, block until the job settles, however long its work takes.
  A job whose status arm threw ends its future with that throw; the status `submit`'s
  `finally` filed is the answer then, so the throw is not rethrown here."
  ([id] (wait id nil))
  ([id ms]
   (when-let [f (:future (get-in @state [:jobs id]))]
     (try (if ms (deref f ms ::timeout) (deref f))
          (catch java.util.concurrent.ExecutionException _ nil)))
   (job id)))

(def ^:private reset-wait-ms
  "How long `reset-registry!` gives a cancelled job to settle before giving up on it —
  the same bound `unload!` gives a loader, for the same cooperative cancel."
  30000)

(defn reset-registry!
  "Cancel every job, **wait for each to settle**, and forget the ones that did.  For a
  process shutting down and for tests; nothing in the browser calls it.

  Forgetting a job releases its writer claim, so a running job dropped here is a writer
  nobody can see (the rule `sweep` holds).  Cancellation is cooperative, so every job gets
  up to `reset-wait-ms` to reach a progress report; one that does not is **kept**, logged,
  and goes on counting as the writer.  The id counter restarts only when nothing is kept.

  The bound is **per job**, not a budget shared across them, so one wedged job cannot
  spend the deadline of the jobs behind it.  Cancel is issued to all of them first, so the
  waits overlap and the wall time is the slowest job's."
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
