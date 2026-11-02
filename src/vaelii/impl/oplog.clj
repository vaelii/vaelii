;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.oplog
  "The **operation log**: each public write a KB takes, recorded as the call that made it.
  A frame holds the operation's name, its arguments, and the inputs the call reads that
  its arguments do not carry — the clock `:created` is read from, the creator, and the
  dynamic bindings that change what a write stores.  `vaelii.core` names the operations
  and their classes in its `write-ops` table, routes each through `run-op`, and builds
  from it the dispatch `replay!` runs frames through (`wiring/replay-op`).

  ## One frame per outermost write

  A write the engine makes inside another write is part of the enclosing call: the
  asserts inside `assert-many`, the assert a skolem mint makes, the retraction
  `retract!` makes of an orphaned NAT.  `*in-op?*` is true for the extent of a recorded
  operation, and `run-op` appends no frame while it is; the nested write runs under the
  bindings the enclosing operation made.

  ## Classes

  - `:replay` — the call is recorded, and its arguments and inputs determine what it
    stores.
  - `:seal` — `import!`, `clear!`, `recover`, `reindex`, `load-text!`: the call's effect
    depends on something no frame carries (a directory's contents, the records as a
    whole).  It marks the log unusable and requests a seal, which runs when it returns.
  - `:config` — `set-solver`, `add-prover`, `add-evaluatable`, `add-reasoner`: the call
    registers code, which no frame can carry, so it marks the log unusable.

  ## Unusable

  A log is **unusable** from the first write it cannot reproduce until a seal starts it
  again (`rotate!`).  `mark-unusable!` appends an `{:unusable reason}` frame and fsyncs
  it, so the mark outlives the process, and a write after the mark runs only once the
  mark is on disk.  A `:seal` or `:config` operation marks it, and so do arguments nippy
  cannot freeze, a write a change-feed listener makes (a listener runs part-way
  through another operation's settle, where `vaelii.core/dispatch-feed!` binds
  `*listener?*`), a record write outside every operation (`LoggedRecords`), and a
  `VirtualMachineError` thrown by a write after its frame was appended (`[:vm-error op
  cls]`), since the public entry point rolls that write back.  A `VirtualMachineError`
  freezing a frame marks nothing: it propagates before the frame is written, and the write
  does not run.

  ## The logged record store

  `attach` wraps a KB's record store in `LoggedRecords`, with a **watermark**: one above
  every handle the store held when the log's generation began.  The page cache can write
  a record to disk before it writes the frame describing the operation that stored it,
  so a crash can leave a record no durable frame accounts for.  A replay finds every such
  record at a handle at or above its own allocations, except a write to a handle below
  the watermark — a deletion, a premise mark, a provenance change of a record the
  generation began with.  So before the first such write in an operation,
  `LoggedRecords` fsyncs the operation's frame.  An operation that only adds records
  pays no fsync.

  In **replay** mode (`attach-replaying`) the store allocates handles from the watermark
  and checks each write against the record already stored at its handle: an equal record
  is left as it is, a missing one is written, and a different one throws with
  `::diverged` in its ex-data.

  ## Generations and replay

  The file's first frame is a header naming the log's **generation**.  `rotate!` starts
  a generation: it truncates the file to a new header and clears the unusable mark.
  `replay!` runs each operation frame through `vaelii.core`'s dispatch with `*replaying?*`
  bound, so `run-op` appends nothing and binds the frame's inputs, and with the change
  feed off, since listeners belong to the process that made the writes.  An operation
  that refused when it was made refuses again, and replay goes on to the next frame.
  `vaelii.impl.seal` decides which generation a restore replays and what a seal writes.

  ## Durability

  One file, `<dir>/oplog/ops.log`, of length-prefixed nippy frames in
  `vaelii.impl.disk.files`' format.  An open truncates a torn trailing frame, as the
  record logs' opens do.  The log's `:fsync` mode decides when a frame reaches the disk:
  `:each` fsyncs each operation's frame before the operation runs, and `:tick` leaves it
  to the durability daemon's tick.  The daemon closes the log on shutdown.

  A failed append, fsync or truncation latches the log's fault (`files/latch-fault!`),
  as it does a record store's: every later operation is refused with `:store-unusable`
  before it runs, so no write lands that the log does not describe."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.store :as store-types]
            [vaelii.impl.wiring :as wiring])
  (:import [java.io RandomAccessFile]))

(def format-version
  "The frame layout's number, written into the log's header.  A log of any other number
  is unusable."
  1)

(def ^:dynamic *in-op?*
  "True for the extent of a recorded operation, so a write nested inside it appends no
  frame of its own."
  false)

(def ^:dynamic *listener?*
  "True while a change-feed listener runs.  A write made then marks the log unusable."
  false)

(def ^:dynamic *replaying?*
  "True while `replay!` runs frames: `run-op` appends nothing and binds
  `*replay-inputs*`."
  false)

(def ^:dynamic *replay-inputs*
  "The inputs map of the frame `replay!` is running."
  nil)

(def ^:dynamic *replay-batch*
  "A volatile `replay!` binds for its extent, holding `[id m]`: the `:batch` id of the last
  replayed `with-deferred-settle` frame, and `m`, a `java.util.HashMap` of the
  re-joins that batch's frames owe its `:settle` frame, which `vaelii.core` binds as
  `chain/*batch-rejoins*`."
  nil)

(defn- log-path ^String [dir] (str dir "/oplog/ops.log"))

(defn- fresh-state [generation fsync]
  {:ops 0 :synced 0 :guard-checks 0 :unusable nil :generation generation :seal-due? false
   :fsync fsync})

(defn- force-guarded!
  "fsync `log`'s file, latching its fault and throwing `:store-unusable` when the fsync
  fails.  Caller holds the lock."
  [{:keys [raf fault path]}]
  (f/with-io-guard fault path :fsync (f/force! raf false)))

(defn- header [generation] {:oplog format-version :generation generation})

(defn- scan
  "Every frame of `raf` in order, the offset past the last whole one, and the offset of a
  frame inside the log that does not thaw (nil when none does).  The frames returned stop
  before that frame, and so does the offset."
  [^RandomAccessFile raf path]
  (let [acc (transient [])
        [end damaged-at]
        (try [(f/scan-log raf path (fn [_ v] (conj! acc v))) nil]
             (catch clojure.lang.ExceptionInfo e
               (if (= :damaged-frame (:type (ex-data e)))
                 [(:offset (ex-data e)) (:offset (ex-data e))]
                 (throw e))))]
    [(persistent! acc) end damaged-at]))

(defn- unusable-reason
  "Why `frames` cannot be replayed, or nil: a header of another format, or the first
  `:unusable` mark."
  [frames]
  (let [h (first frames)]
    (if (not= format-version (:oplog h))
      [:format (:oplog h)]
      (some :unusable frames))))

(defn open-log
  "Open the operation log under `dir` and register it with the durability daemon.  A torn
  trailing frame is truncated.  A log with no header — a new one, or one a crash emptied
  — starts at `generation`.  `opts` takes `:fsync`: `:each` fsyncs each operation's frame
  before the operation runs, `:tick` (the default) leaves it to the durability daemon.

  A frame inside the log that does not thaw (`f/scan-log`'s `:damaged-frame`) ends what
  can be replayed: the log is truncated at it, and a `{:unusable [:damaged-frame
  offset]}` frame is appended unless an earlier mark already holds.  A replay of the
  frames before it would miss the writes after it, and the watermark check catches a
  missed write only when it allocated a handle — a deletion below the watermark leaves
  nothing to find."
  ([dir generation] (open-log dir generation nil))
  ([dir generation {:keys [fsync] :or {fsync :tick}}]
   (let [path (log-path dir)
         raf  (f/open-log path)
         [frames end damaged-at] (scan raf path)
         _    (f/truncate-log! raf end)
         lock (Object.)
         log  (store-types/->Oplog path raf lock (atom nil) (atom nil) (atom nil) (atom nil))]
     (if (empty? frames)
       (do (locking lock (f/append-record! raf (header generation)))
           (reset! (:state log) (fresh-state generation fsync)))
       (let [ops (count (filter :op (rest frames)))]
         (reset! (:state log) (assoc (fresh-state (:generation (first frames)) fsync)
                                     :ops ops :synced ops
                                     :unusable (unusable-reason frames)))))
     (when (and damaged-at (nil? (:unusable @(:state log))))
       (let [reason [:damaged-frame damaged-at]]
         (locking lock (f/append-record! raf {:unusable reason}))
         (swap! (:state log) assoc :unusable reason)
         (trove/log! {:level :warn :id ::damaged-frame
                      :msg  (str "operation log " path " holds a frame at byte offset "
                                 damaged-at " that does not decode, with frames after it —"
                                 " truncated there and marked unusable")
                      :data {:reason reason}})))
     (reset! (:reg log)
             (dur/register! {:label (str "oplog " path)
                             ;; a failed tick latches the fault, which logs it once, and
                             ;; a latched log's tick does nothing
                             :fsync (fn [_]
                                      (locking lock
                                        (when-not @(:fault log)
                                          (let [n (:ops @(:state log))]
                                            (try (force-guarded! log)
                                                 (swap! (:state log) assoc :synced n)
                                                 (catch clojure.lang.ExceptionInfo _ nil))))))
                             :close (fn [] (locking lock (.close raf)))}))
     log)))

(defn close-log!
  "Fsync and close `log`, withdraw its durability registration, and latch it `:closed`.
  A failed fsync still closes and latches it, and throws."
  [{:keys [^RandomAccessFile raf lock reg fault path]}]
  (dur/deregister! @reg)
  (locking lock
    (try (when (.. raf getChannel isOpen)
           (try (when-not @fault (f/force! raf false))
                (finally (.close raf))))
         (finally (f/latch-closed! fault path)))))

(defn read-frames
  "The frames of `log` after its header, in append order, `:unusable` marks included."
  [{:keys [^RandomAccessFile raf lock path]}]
  (locking lock (vec (rest (first (scan raf path))))))

(defn generation
  "The generation `log` holds."
  [log]
  (:generation @(:state log)))

(defn unusable
  "Why `log` cannot be replayed, or nil."
  [log]
  (:unusable @(:state log)))

(defn fsync-mode
  "When `log` fsyncs an operation's frame, `:each` or `:tick` (`open-log`)."
  [log]
  (:fsync @(:state log)))

(defn note-opened!
  "Record `report`, what the open that attached `log` did (`vaelii.impl.seal/open!`)."
  [log report]
  (swap! (:state log) assoc :opened report))

(defn opened
  "What the open that attached `log` did, or nil when no `open-kb` attached it."
  [log]
  (:opened @(:state log)))

(defn mark-unusable!
  "Record that `log` cannot be replayed, for `reason`, and fsync the mark before
  returning.  The first reason is the one kept.  A log whose fault is latched appends
  nothing."
  [{:keys [raf lock state path fault] :as log} reason]
  (when-not (:unusable @state)
    (when-not @fault
      (locking lock
        (f/with-io-guard fault path true (f/append-record! raf {:unusable reason}))
        (force-guarded! log)
        (swap! state assoc :synced (:ops @state))))
    (swap! state assoc :unusable reason)
    (trove/log! {:level :info :id ::unusable
                 :msg  (str "operation log " path " is unusable from here: " (pr-str reason))
                 :data {:reason reason}})))

(defn rotate!
  "Start `log` again at generation `gen`: truncate the file to a header naming `gen`,
  fsync it, and reset the state, the unusable mark included.  The fsync mode and the open's
  report carry over."
  [{:keys [^RandomAccessFile raf lock state fault path]} gen]
  (locking lock
    (f/check-fault! fault)
    (f/with-io-guard fault path true
      (f/truncate-log! raf 0)
      (f/append-record! raf (header gen)))
    (f/with-io-guard fault path :fsync (f/force! raf true))
    (swap! state (fn [{:keys [fsync opened]}]
                   (assoc (fresh-state gen fsync) :opened opened)))))

(defn request-seal!
  "Ask for a seal when the running operation returns."
  [log]
  (swap! (:state log) assoc :seal-due? true))

(defn set-seal-fn!
  "Install `f`, a function of the logged KB, as what `run-op` calls when a seal is due."
  [log f]
  (reset! (:seal-fn log) f))

(defn- append-op!
  "Append the frame for one operation, and under `:each` fsync it.  A frame nippy cannot
  freeze marks the log unusable instead, and the write it describes still runs.  A failed
  append or fsync latches the log's fault and throws `:store-unusable`, and a
  `VirtualMachineError` freezing the frame (`safe/vm-error`) propagates as itself; in
  both cases no frame is written and the write does not run."
  [{:keys [raf lock state fault path] :as log} op args inputs]
  (when (try
          (locking lock
            (f/with-io-guard fault path true (f/append-record! raf {:op op :args args :in inputs})))
          true
          (catch clojure.lang.ExceptionInfo e
            (when (= :store-unusable (:type (ex-data e))) (throw e))
            (when-let [vm (safe/vm-error e)] (throw vm))
            (mark-unusable! log [:unfreezable op (.getName (class e))])
            false)
          (catch Throwable t
            (when-let [vm (safe/vm-error t)] (throw vm))
            (mark-unusable! log [:unfreezable op (.getName (class t))])
            false))
    (locking lock
      (let [n (:ops (swap! state update :ops inc))]
        (when (= :each (:fsync @state))
          (force-guarded! log)
          (swap! state assoc :synced n))))))

(defn- seal-if-due!
  "Run the installed seal function on `kb` when a seal was requested.  A seal declined
  because a settle is pending (`vaelii.impl.seal/busy`) stays requested."
  [kb]
  (let [{:keys [state seal-fn] :as log} (:oplog kb)]
    (when (:seal-due? @state)
      (swap! state assoc :seal-due? false)
      (when-let [sf @seal-fn]
        (when (:busy (sf kb)) (request-seal! log))))))

(defn run-op
  "Run `f` as write operation `op` of class `class` on `kb` over `args`.

  `inputs-fn` returns the inputs map a frame carries; `f` takes an inputs map and runs
  the write with those inputs bound, or under the bindings in force when handed nil.
  On a KB with no log, and nested inside a recorded operation, `f` runs on nil and
  nothing is appended; a nested write made while `*listener?*` is true marks the log
  unusable.  Under `replay!`, `f` runs on the frame's inputs.  When a top-level
  operation returns, a requested seal runs; when `f` throws a `VirtualMachineError`, the
  log is marked `[:vm-error op cls]` and the throw propagates."
  [kb op class args inputs-fn f]
  (let [log (:oplog kb)]
    (cond
      (nil? log) (f nil)

      *in-op?*
      (do (when *listener?* (mark-unusable! log [:listener-write op]))
          (f nil))

      *replaying?*
      (binding [*in-op?* true, *listener?* false]
        (f *replay-inputs*))

      :else
      (let [_      (f/check-fault! (:fault log))
            inputs (inputs-fn)]
        (case class
          :replay         (append-op! log op args inputs)
          (:seal :config) (mark-unusable! log [class op]))
        (let [r (try (binding [*in-op?* true, *listener?* false] (f inputs))
                     (catch Throwable t
                       (when-let [vm (safe/vm-error t)]
                         (try (mark-unusable! log [:vm-error op (.getName (.getClass vm))])
                              (catch Throwable m (.addSuppressed t m))))
                       (throw t)))]
          (when (= :seal class) (request-seal! log))
          (seal-if-due! kb)
          r)))))

;; ---- replay ---------------------------------------------------------------

(defn- diverged! [kind id]
  (throw (ex-info (str "replaying the operation log wrote " (name kind) " " id
                       " differently from the record the store holds there")
                  {::diverged true :kind kind :handle id})))

(defn replay!
  "Run each operation frame of `frames` against `kb` (the namespace docstring,
  \"Generations and replay\").  Throws with `::diverged` in its ex-data when a replayed
  write differs from the stored record, or a frame names an operation nothing installed.

  Only an `ex-info` is a refusal to skip.  Anything else a frame throws — an `Error`, an
  I/O failure — propagates, so the restore declines rather than answering for a KB that
  is missing the write."
  [kb frames]
  (binding [*replaying?* true, feed/*enabled?* false, *replay-batch* (volatile! [nil (java.util.HashMap.)])]
    (with-open [r (progress/start ::replay "replay: run the logged operations" (count frames))]
      (doseq [{:keys [op args in]} frames]
        (progress/tick! r)
        (when op
          (let [g (or (wiring/replay-op op) (diverged! :operation op))]
            (binding [*replay-inputs* in]
              (try (apply g kb args)
                   (catch clojure.lang.ExceptionInfo t
                     (when (::diverged (ex-data t)) (throw t)))))))))))

;; ---- the logged record store --------------------------------------------

(defn- sync-frame!
  "Fsync `log` when it holds a frame no fsync has covered yet."
  [{:keys [lock state] :as log}]
  (locking lock
    (let [n (:ops @state)]
      (when (> (long n) (long (:synced @state)))
        (force-guarded! log)
        (swap! state assoc :synced n)))))

(defn- before-write!
  "What a normal-mode record write owes `log`, called before the write with the handle
  it names — nil for a record the store has not numbered yet."
  [log watermark id kind]
  (cond
    (unusable log) nil

    (not *in-op?*)
    (mark-unusable! log [:unlogged-write kind])

    (and (some? id) (< (long id) (long @watermark)))
    (do (swap! (:state log) update :guard-checks inc)
        (sync-frame! log))))

(defn- replay-id
  "The handle a replayed write lands at: its own `:id`, or the next one `counter` issues.
  The counter stays above an explicit handle, as a store's does."
  [counter rec]
  (let [id (long (or (:id rec) (dec (long (swap! counter inc)))))]
    (swap! counter max (inc id))
    id))

(defn- replay-put!
  "A replayed record write: nothing when the store holds an equal record at its handle,
  the write when it holds none, and `diverged!` when it holds another."
  [inner get-fn put-fn kind rec]
  (let [id       (:id rec)
        existing (get-fn inner id)]
    (cond
      (nil? existing)  (put-fn inner rec)
      (= existing rec) id
      :else            (diverged! kind id))))

(defn- guarded-sink
  "`sink`, with `before-write!` ahead of each record it takes."
  [log watermark sink]
  (reify
    p/RecordSink
    (write-record! [_ rec]
      (before-write! log watermark (:id rec) :write-record)
      (p/write-record! sink rec))
    java.io.Closeable
    (close [_] (.close ^java.io.Closeable sink))))

;; `watermark` and `counter` are atoms because a seal moves the watermark under a KB value
;; every caller already holds, and `mode` because a restore switches it from `:replay` to
;; `:normal` once the frames are run.
(defrecord LoggedRecords [inner log watermark mode counter]
  p/RecordStore
  (get-sentex        [_ id] (p/get-sentex inner id))
  (get-justification [_ id] (p/get-justification inner id))
  (get-provenance    [_ id] (p/get-provenance inner id))
  (sentex-ids        [_]    (p/sentex-ids inner))
  (justification-ids [_]    (p/justification-ids inner))
  (premise-ids       [_]    (p/premise-ids inner))
  (premise-strength  [_ id] (p/premise-strength inner id))

  (next-id [_]
    (if (identical? :replay @mode)
      (dec (long (swap! counter inc)))
      (do (when-not (or *in-op?* (unusable log))
            (mark-unusable! log [:unlogged-write :next-id]))
          (p/next-id inner))))
  (put-sentex [_ s]
    (if (identical? :replay @mode)
      (replay-put! inner p/get-sentex p/put-sentex :sentex (assoc s :id (replay-id counter s)))
      (do (before-write! log watermark (:id s) :put-sentex)
          (p/put-sentex inner s))))
  (put-justification [_ j]
    (if (identical? :replay @mode)
      (replay-put! inner p/get-justification p/put-justification :justification
                   (assoc j :id (replay-id counter j)))
      (do (before-write! log watermark (:id j) :put-justification)
          (p/put-justification inner j))))
  (delete-sentex! [_ id]
    (if (identical? :replay @mode)
      (when (p/get-sentex inner id) (p/delete-sentex! inner id))
      (do (before-write! log watermark id :delete-sentex)
          (p/delete-sentex! inner id))))
  (delete-justification! [_ id]
    (if (identical? :replay @mode)
      (when (p/get-justification inner id) (p/delete-justification! inner id))
      (do (before-write! log watermark id :delete-justification)
          (p/delete-justification! inner id))))
  (put-provenance [_ id prov]
    (if (identical? :replay @mode)
      (do (when-not (= prov (p/get-provenance inner id)) (p/put-provenance inner id prov))
          prov)
      (do (before-write! log watermark id :put-provenance)
          (p/put-provenance inner id prov))))
  (delete-provenance! [_ id]
    (if (identical? :replay @mode)
      (when (p/get-provenance inner id) (p/delete-provenance! inner id))
      (do (before-write! log watermark id :delete-provenance)
          (p/delete-provenance! inner id))))
  (mark-premise [_ id strength]
    (if (identical? :replay @mode)
      (when-not (= strength (p/premise-strength inner id)) (p/mark-premise inner id strength))
      (do (before-write! log watermark id :mark-premise)
          (p/mark-premise inner id strength))))
  (unmark-premise! [_ id]
    (if (identical? :replay @mode)
      (when (p/premise-strength inner id) (p/unmark-premise! inner id))
      (do (before-write! log watermark id :unmark-premise)
          (p/unmark-premise! inner id))))
  (clear-records! [_]
    (before-write! log watermark 0 :clear-records)
    (p/clear-records! inner))

  ;; the optional capabilities, answered through the helpers so an inner store without
  ;; one reads exactly as it would unwrapped
  p/Tallying
  (sentex-tally        [_] (cap/count-sentexes inner))
  (justification-tally [_] (cap/count-justifications inner))
  (a-sentex-id         [_] (cap/some-sentex-id inner))
  (a-justification-id  [_] (cap/some-justification-id inner))
  (a-premise-id        [_] (cap/some-premise-id inner))

  p/Prefetching
  (prefetch-sentexes! [_ ids]
    (when (satisfies? p/Prefetching inner) (p/prefetch-sentexes! inner ids))
    nil)
  (prefetch-justifications! [_ ids]
    (when (satisfies? p/Prefetching inner) (p/prefetch-justifications! inner ids))
    nil)

  p/BulkLoading
  (open-sentex-sink [this opts]
    (if (identical? :replay @mode)
      (cap/loop-sink this p/put-sentex (:premises? opts true))
      (guarded-sink log watermark (cap/sentex-sink inner opts))))
  (open-justification-sink [this opts]
    (if (identical? :replay @mode)
      (cap/loop-sink this p/put-justification false)
      (guarded-sink log watermark (cap/justification-sink inner opts))))

  p/BulkAnnotating
  (mark-premise-batch [this id->strength]
    (if (identical? :replay @mode)
      (doseq [[id s] id->strength] (p/mark-premise this id s))
      (do (doseq [id (keys id->strength)] (before-write! log watermark id :mark-premise))
          (cap/mark-premises inner id->strength)))
    nil)
  (put-provenance-batch [this entries]
    (if (identical? :replay @mode)
      (doseq [[id prov] entries] (p/put-provenance this id prov))
      (do (doseq [[id _] entries] (before-write! log watermark id :put-provenance))
          (cap/put-all-provenance inner entries)))
    nil))

(defn attach
  "`kb` recording its public writes into `log`: `:oplog` set, and the record store
  wrapped in `LoggedRecords` whose watermark is one above a handle `next-id` allocates
  now, so every record the store already held sits below it."
  [kb log]
  (let [inner (:records kb)]
    (assoc kb :oplog log
           :records (->LoggedRecords inner log (atom (inc (long (p/next-id inner))))
                                     (atom :normal) (atom nil)))))

(defn attach-replaying
  "`kb` attached to `log` in replay mode, allocating handles from `watermark`."
  [kb log watermark]
  (assoc kb :oplog log
         :records (->LoggedRecords (:records kb) log (atom watermark)
                                   (atom :replay) (atom watermark))))

(defn finish-replay!
  "Switch `kb`'s logged record store from replay mode to normal mode."
  [kb]
  (reset! (:mode (:records kb)) :normal))

(defn replay-next
  "The next handle a replay-mode `LoggedRecords` would issue."
  [store]
  @(:counter store))

(defn set-watermark!
  "Move a `LoggedRecords`' watermark to `w`."
  [store w]
  (reset! (:watermark store) w))

(defn inner-records
  "The record store under a `LoggedRecords`, or `store` itself."
  [store]
  (if (instance? LoggedRecords store) (:inner store) store))
