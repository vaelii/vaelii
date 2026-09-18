;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.oplog
  "The **operation log**: each public write a KB takes, recorded as the call that made it.
  A frame holds the operation's name, its arguments, and the inputs the call reads that
  its arguments do not carry — the clock `:created` is stamped from, the creator, and the
  dynamic bindings that change what a write stores.  `vaelii.core` names the operations
  and their classes in its `write-ops` table, routes each through `run-op`, and installs
  the table as the dispatch `replay!` runs frames through.

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
  again (`rotate!`).  `mark-unusable!` appends an `{:unusable reason}` frame, so the mark
  outlives the process.  A `:seal` or `:config` operation marks it, and so do arguments
  nippy cannot freeze, a write a change-feed listener makes (a listener runs part-way
  through another operation's settle, where `vaelii.core/dispatch-feed!` binds
  `*listener?*`), and a record write outside every operation (`LoggedRecords`).

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
  `replay!` runs each operation frame through the installed dispatch with `*replaying?*`
  bound, so `run-op` appends nothing and binds the frame's inputs, and with the change
  feed off, since listeners belong to the process that made the writes.  An operation
  that refused when it was made refuses again, and replay goes on to the next frame.
  `vaelii.impl.seal` decides which generation a restore replays and what a seal writes.

  ## Durability

  One file, `<dir>/oplog/ops.log`, of length-prefixed nippy frames in
  `vaelii.impl.disk.files`' format.  The durability daemon fsyncs it on its tick and
  closes it on shutdown.  An open truncates a torn trailing frame, as the record logs'
  opens do."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.store :as store-types])
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

(defn- log-path ^String [dir] (str dir "/oplog/ops.log"))

(defn- fresh-state [generation]
  {:ops 0 :synced 0 :guard-checks 0 :unusable nil :generation generation :seal-due? false})

(defn- header [generation] {:oplog format-version :generation generation})

(defn- scan
  "Every frame of `raf` in order, and the offset past the last whole one."
  [^RandomAccessFile raf]
  (let [acc (transient [])
        end (f/scan-log raf (fn [_ v] (conj! acc v)))]
    [(persistent! acc) end]))

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
  — starts at `generation`."
  [dir generation]
  (let [path (log-path dir)
        raf  (f/open-log path)
        [frames end] (scan raf)
        _    (f/truncate-log! raf end)
        lock (Object.)
        log  (store-types/->Oplog path raf lock (atom nil) (atom nil) (atom nil))]
    (if (empty? frames)
      (do (locking lock (f/append-record! raf (header generation)))
          (reset! (:state log) (fresh-state generation)))
      (let [ops (count (filter :op (rest frames)))]
        (reset! (:state log) (assoc (fresh-state (:generation (first frames)))
                                    :ops ops :synced ops
                                    :unusable (unusable-reason frames)))))
    (reset! (:reg log)
            (dur/register! {:label (str "oplog " path)
                            :fsync (fn [_]
                                     (locking lock
                                       (let [n (:ops @(:state log))]
                                         (f/force! raf false)
                                         (swap! (:state log) assoc :synced n))))
                            :close (fn [] (locking lock (.close raf)))}))
    log))

(defn close-log!
  "Fsync and close `log`, and withdraw its durability registration."
  [{:keys [^RandomAccessFile raf lock reg]}]
  (dur/deregister! @reg)
  (locking lock
    (when (.. raf getChannel isOpen)
      (f/force! raf false)
      (.close raf))))

(defn read-frames
  "The frames of `log` after its header, in append order, `:unusable` marks included."
  [{:keys [^RandomAccessFile raf lock]}]
  (locking lock (vec (rest (first (scan raf))))))

(defn generation
  "The generation `log` holds."
  [log]
  (:generation @(:state log)))

(defn unusable
  "Why `log` cannot be replayed, or nil."
  [log]
  (:unusable @(:state log)))

(defn mark-unusable!
  "Record that `log` cannot be replayed, for `reason`.  The first reason is the one kept."
  [{:keys [raf lock state path]} reason]
  (when-not (:unusable @state)
    (locking lock (f/append-record! raf {:unusable reason}))
    (swap! state assoc :unusable reason)
    (trove/log! {:level :info :id ::unusable
                 :msg  (str "operation log " path " is unusable from here: " (pr-str reason))
                 :data {:reason reason}})))

(defn rotate!
  "Start `log` again at generation `gen`: truncate the file to a header naming `gen`,
  fsync it, and reset the state, the unusable mark included."
  [{:keys [^RandomAccessFile raf lock state]} gen]
  (locking lock
    (f/truncate-log! raf 0)
    (f/append-record! raf (header gen))
    (f/force! raf true)
    (reset! state (fresh-state gen))))

(defn request-seal!
  "Ask for a seal when the running operation returns."
  [log]
  (swap! (:state log) assoc :seal-due? true))

(defn set-seal-fn!
  "Install `f`, a function of the logged KB, as what `run-op` calls when a seal is due."
  [log f]
  (reset! (:seal-fn log) f))

(defn- append-op!
  "Append the frame for one operation.  A frame nippy cannot freeze marks the log
  unusable instead, and the write it describes still runs."
  [{:keys [raf lock state] :as log} op args inputs]
  (try
    (locking lock (f/append-record! raf {:op op :args args :in inputs}))
    (swap! state update :ops inc)
    (catch Throwable t
      (mark-unusable! log [:unfreezable op (.getName (class t))]))))

(defn- seal-if-due!
  "Run the installed seal function on `kb` when a seal was requested."
  [kb]
  (let [{:keys [state seal-fn]} (:oplog kb)]
    (when (:seal-due? @state)
      (swap! state assoc :seal-due? false)
      (when-let [sf @seal-fn] (sf kb)))))

(defn run-op
  "Run `f` as write operation `op` of class `class` on `kb` over `args`.

  `inputs-fn` returns the inputs map a frame carries; `f` takes an inputs map and runs
  the write with those inputs bound, or under the bindings in force when handed nil.
  On a KB with no log, and nested inside a recorded operation, `f` runs on nil and
  nothing is appended; a nested write made while `*listener?*` is true marks the log
  unusable.  Under `replay!`, `f` runs on the frame's inputs.  When a top-level
  operation returns, a requested seal runs."
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
      (let [inputs (inputs-fn)]
        (case class
          :replay         (append-op! log op args inputs)
          (:seal :config) (mark-unusable! log [class op]))
        (let [r (binding [*in-op?* true, *listener?* false] (f inputs))]
          (when (= :seal class) (request-seal! log))
          (seal-if-due! kb)
          r)))))

;; ---- replay ---------------------------------------------------------------

(defonce ^{:private true
           :doc "Operation name -> the function a frame of it runs through.  Installed by `vaelii.core`
  at load, with the write entry points of its `write-ops` table."}
  dispatch
  (atom {}))

(defn install-dispatch!
  "Install `m`, operation name -> function of the KB and the frame's arguments."
  [m]
  (reset! dispatch m))

(defn- diverged! [kind id]
  (throw (ex-info (str "replaying the operation log wrote " (name kind) " " id
                       " differently from the record the store holds there")
                  {::diverged true :kind kind :handle id})))

(defn replay!
  "Run each operation frame of `frames` against `kb` (the namespace docstring,
  \"Generations and replay\").  Throws with `::diverged` in its ex-data when a replayed
  write differs from the stored record, or a frame names an operation nothing installed."
  [kb frames]
  (binding [*replaying?* true, feed/*enabled?* false]
    (doseq [{:keys [op args in]} frames
            :when op]
      (let [g (or (get @dispatch op) (diverged! :operation op))]
        (binding [*replay-inputs* in]
          (try (apply g kb args)
               (catch Throwable t
                 (when (::diverged (ex-data t)) (throw t)))))))))

;; ---- the logged record store --------------------------------------------

(defn- sync-frame!
  "Fsync `log` when it holds a frame no fsync has covered yet."
  [{:keys [^RandomAccessFile raf lock state]}]
  (locking lock
    (let [n (:ops @state)]
      (when (> (long n) (long (:synced @state)))
        (f/force! raf false)
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

(defn- replay-sink
  "A sink writing each record through `store`'s own replayed put, and marking a premise
  when `premises?` and the record carries a strength."
  [store put-fn premises?]
  (reify
    p/RecordSink
    (write-record! [_ rec]
      (let [id (put-fn store rec)]
        (when (and premises? (:strength rec)) (p/mark-premise store id (:strength rec)))
        id))
    java.io.Closeable
    (close [_] nil)))

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
      (replay-sink this p/put-sentex (:premises? opts true))
      (guarded-sink log watermark (cap/sentex-sink inner opts))))
  (open-justification-sink [this opts]
    (if (identical? :replay @mode)
      (replay-sink this p/put-justification false)
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
