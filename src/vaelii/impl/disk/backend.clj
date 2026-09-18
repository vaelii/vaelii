;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.backend
  "The durable-store entry point: open (once per directory) a `DiskRecordStore` and/or a
  `KvIndexStore` over a `DiskKvBackend`, take the single-writer lock, and wire what was
  opened to the durability daemon.

  **The two halves open independently.**  A KB's records and its index are chosen on
  separate axes (`vaelii.impl.kb`), and only one of the combinations that reach here
  wants both: `:disk-log` is durable records *and* a durable index, while `:disk-memory` /
  `:disk-dense` / `:disk-columnar` keep the derived index in RAM and want the record store
  alone — no index log, no index WAL, nothing written to the directory but the records.  So each
  component is opened on first use rather than as a pair, and the registry records which
  ones a directory actually has.  A directory opened both ways in one JVM therefore
  shares its record store across both KBs and hands the RAM-index one no durable index
  at all.

  A process-global registry keyed by canonical directory mirrors the memory backend's
  space registry: two KBs constructed over the same directory share one set of
  stores — so a KB \"restarted\" over the same directory in one JVM (the recovery
  tests) sees the durable records the first wrote, with its own fresh taxonomy/TMS, and
  the file handles + durability registration + lock are taken once rather than leaking
  across the suite's hundreds of KB constructions.  A true cross-JVM restart opens the
  directory fresh and rebuilds the RAM state from the durable logs."
  (:require [clojure.java.io :as io]
            [taoensso.trove :as trove]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.index-snapshot :as snap]
            [vaelii.impl.disk.kv :as dkv]
            [vaelii.impl.disk.lock :as lock]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.kv :as kv]))

;; canonical dir -> {:dir d :records <RecordStore>? :index <KvIndexStore>? :dur-ids {kind id}}
;; — the component keys are present only for what was actually opened.
(defonce ^:private stores (atom {}))

(defn canonical-dir
  "`dir`'s canonical path — the identity a directory's stores are keyed by, and what
  anything else keying state off a disk KB's directory (the derived index's shared
  state, `vaelii.impl.kb`) must key on too, so two spellings of one directory are one
  KB rather than two."
  [dir]
  (.getCanonicalPath (io/file dir)))

(defn store-backend
  "The `open-kb` backend the store in `dir` was written by, read off the files beside its
  records, or nil when `dir` holds no store (no `records/format.edn`):

    * `index/trie.csr`, a mapped index image → `:disk-snapshot`;
    * `index/kv.log`, a write-ahead-logged index → `:disk-log`;
    * no `index/` file of either kind → `:disk-columnar`, which rebuilds the index from the
      records on open.  `:disk-memory` and `:disk-dense` write the same files and read back
      correctly as `:disk-columnar`.

  An open under the wrong backend returns an empty KB and throws nothing: a
  `:disk-snapshot` or `:disk-columnar` store opened as `:disk-log` finds no index log, so
  every read answers nothing although every record is on disk."
  [dir]
  (let [f (fn [& parts] (.exists ^java.io.File (apply io/file dir parts)))]
    (when (f "records" "format.edn")
      (cond
        (f "index" "trie.csr") :disk-snapshot
        (f "index" "kv.log")   :disk-log
        :else                  :disk-columnar))))

(defn- register-or-close!
  "Register `entry` with the durability daemon and return `[store id]` — closing the
  store through `entry`'s own `:close` if the registration throws.

  A component opened and not registered is one nothing will fsync and nothing will
  close: `store-for` puts no store in the registry when this throws, and releases the
  directory's lock on its way out, so the handles would outlive the lock that made them
  safe to hold."
  [store entry]
  (try [store (dur/register! entry)]
       (catch Throwable t
         (try ((:close entry))
              (catch Throwable c
                (trove/log! {:level :error
                             :msg (str "disk backend: closing " (:label entry)
                                       " after a failed registration failed: "
                                       (.getMessage c))})))
         (throw t))))

(defn- open-component!
  "Open one durable component of `dir` and register it with the durability daemon.
  Returns `[store dur-id]`."
  [dir kind]
  (case kind
    :records (let [rec (drs/open-record-store dir)]
               (register-or-close!
                rec {:fsync      (fn [_] (drs/fsync rec))
                     :close      (fn [] (drs/close! rec))
                     :compact    (fn [] (drs/compact! rec))
                     :dead-ratio (fn [] (drs/dead-ratio rec))
                     :label      (str "disk-records " dir)}))
    :index   (let [kvb (dkv/open-kv-backend dir)]
               (register-or-close!
                (kv/->KvIndexStore kvb)
                {:fsync      (fn [_] (dkv/fsync kvb))
                 :close      (fn [] (dkv/close! kvb))
                 :compact    (fn [] (dkv/compact! kvb))
                 :dead-ratio (fn [] (dkv/dead-ratio kvb))
                 :label      (str "disk-index " dir)}))
    ;; A fork's record-level bookkeeping (`vaelii.impl.overlay.store`): tombstones and
    ;; released premise marks, which are the overlay's own state and so must be exactly as
    ;; durable as its records.  Its own WAL in a subdirectory, so a directory holding a
    ;; fork is still an ordinary disk KB plus one extra log — and a directory that has
    ;; never been forked never grows one.
    :overlay-meta (let [kvb (dkv/open-kv-backend (str dir "/overlay-meta"))]
                    (register-or-close!
                     kvb {:fsync      (fn [_] (dkv/fsync kvb))
                          :close      (fn [] (dkv/close! kvb))
                          :compact    (fn [] (dkv/compact! kvb))
                          :dead-ratio (fn [] (dkv/dead-ratio kvb))
                          :label      (str "overlay-meta " dir)}))))

(defn- store-for
  "The `kind` (`:records` / `:index`) store for `dir`, opened once per canonical
  directory.  The directory's single-writer lock is taken by whichever component opens
  first and released once, by `close-dir!`.

  Opening is serialized on the registry rather than done inside a `swap!`: a retried
  `swap!` would open a second set of file handles for the same logs and leak the first."
  [dir kind]
  (let [cdir (canonical-dir dir)]
    (or (get-in @stores [cdir kind])
        (locking stores
          (or (get-in @stores [cdir kind])
              ;; "first" is *does this JVM already hold the lock*, not *is the registry
              ;; entry empty*.  A directory's entry can exist without a store behind it —
              ;; `register-index-snapshot!` makes one — and reading the entry instead
              ;; would leave such a directory unlocked, with nothing to say so.
              (let [first? (not (lock/held? cdir))]
                (when first? (lock/acquire! cdir))
                (try
                  (let [[store dur-id] (open-component! cdir kind)]
                    (swap! stores update cdir
                           #(-> (or % {:dir cdir :dur-ids {}})
                                (assoc kind store)
                                (assoc-in [:dur-ids kind] dur-id)))
                    store)
                  (catch Throwable t
                    ;; the lock this call took is nobody else's, and nothing is
                    ;; registered to release it later — drop it rather than hold the
                    ;; directory for the JVM's life over a failed open
                    (when first? (lock/release! cdir))
                    (throw t)))))))))

(defn records-for
  "The durable `RecordStore` for `dir`.  Opens no index — the record half alone is what
  a RAM-index mode (`:disk-memory`, `:disk-dense`, `:disk-columnar`) wants durable."
  [dir]
  (store-for dir :records))

(defn index-for
  "The `:disk-log` `IndexStore` for `dir` — the `KvIndexStore` over a write-ahead-logged
  `DiskKvBackend`, whose map is in RAM and whose log buys the restart
  (`vaelii.impl.disk.kv`)."
  [dir]
  (store-for dir :index))

(defn overlay-meta-for
  "The durable `KvBackend` holding a fork's record-level bookkeeping for `dir`
  (`vaelii.impl.overlay.mount`).  Opened only for a directory that actually hosts a
  fork's overlay."
  [dir]
  (store-for dir :overlay-meta))

(defn register-index-snapshot!
  "Register `save-fn` (a thunk) as `dir`'s derived-index snapshot writer.

  A derived index is not one of the components above — nothing here opens it, and it has
  no file handle to close — but the *image* of it is written to this directory and has to
  be written by whoever last held it, while the records it is stamped against are still
  open.  So it hangs off the directory's registry entry and runs at the front of
  `close-dir!`, and on JVM shutdown through the durability daemon.

  Idempotent per directory: `open-kb` runs for every KB constructed over a directory and
  they all share one index, so the first registration is the one that stands."
  [dir save-fn]
  (let [cdir (canonical-dir dir)]
    (locking stores
      (when-not (get-in @stores [cdir :snapshot])
        (let [id (dur/register! {:fsync (fn [_] nil)      ; an image is not a WAL — no tick
                                 :close save-fn
                                 ;; the image is stamped against this directory's
                                 ;; records, so on the JVM-shutdown path it has to be
                                 ;; written before they close (`dur/close-phases`)
                                 :phase :image
                                 :label (str "index-snapshot " cdir)})]
          (swap! stores update cdir
                 #(-> (or % {:dir cdir :dur-ids {}})
                      (assoc :snapshot save-fn)
                      (assoc-in [:dur-ids :snapshot] id))))))))

(defn replace-index-snapshot!
  "Make `save-fn` `dir`'s derived-index snapshot writer, replacing the one
  `register-index-snapshot!` kept.  A KB recording an operation log writes its images only
  as a seal (`vaelii.impl.seal`), so it takes over the writer `open-kb` registered — the
  one `close-dir!`, the JVM-shutdown path and `maybe-refresh-index-snapshot!` all run."
  [dir save-fn]
  (let [cdir (canonical-dir dir)]
    (locking stores
      (when-let [old (get-in @stores [cdir :dur-ids :snapshot])]
        (dur/deregister! old))
      (let [id (dur/register! {:fsync (fn [_] nil)
                               :close save-fn
                               :phase :image
                               :label (str "index-snapshot " cdir)})]
        (swap! stores update cdir
               #(-> (or % {:dir cdir :dur-ids {}})
                    (assoc :snapshot save-fn)
                    (assoc-in [:dur-ids :snapshot] id)))))))

(defn register-reasoning-image!
  "Register `save-fn` (a thunk) as `dir`'s reasoning image writer, run at the front of
  `close-dir!` beside the index image's and on JVM shutdown in the same `:image` phase —
  the reasoning image is stamped against these records too, so it is written while they are
  open.

  **The latest registration replaces the one before it**, where the index image's first
  registration stands.  The index is shared by every KB over a directory, and belief is
  not: it lives in the KB that recovered it, and a second KB opened over a directory is
  the one that has the current belief — the first one's writes are invisible to it
  (docs/storage.md, the single-writer contract)."
  [dir save-fn]
  (let [cdir (canonical-dir dir)]
    (locking stores
      (when-let [old (get-in @stores [cdir :dur-ids :reasoning-image])]
        (dur/deregister! old))
      (let [id (dur/register! {:fsync (fn [_] nil)
                               :close save-fn
                               :phase :image
                               :label (str "reasoning-image " cdir)})]
        (swap! stores update cdir
               #(-> (or % {:dir cdir :dur-ids {}})
                    (assoc :reasoning-image save-fn)
                    (assoc-in [:dur-ids :reasoning-image] id)))))))

(defn maybe-refresh-index-snapshot!
  "Rewrite `cdir`'s index image if the live index has drifted past the threshold.

  **`cdir` is already canonical** — the KB carries the resolved path (`kb`'s
  `:snapshot-dir`), so nothing here calls `getCanonicalPath` and the write entry point pays no
  `realpath` per assert.  A caller holding a directory as its user spelled it canonicalizes
  it once and keeps the answer; this is the wrong place to do it per call.

  **Called on the writer's thread, from the write entry point** (`kb/create-sentex`), because
  that is the only thread allowed to touch the columnar index (`disk/index_snapshot.clj`,
  \"the cadence\").  So the gate is asked per write, and what it costs matters
  rather than guessing at: one read of the registry here, which is where a directory with
  no image writer registered stops — and then, for one that has, `due?`'s two property
  reads, the canonical path its state is keyed by, one map read and a clock.  The caller
  reaches this at all only when its KB carries a `:snapshot-dir`, which is what keeps the
  whole of it off every other backend's write path.

  **A refresh that throws must not fail the write.**  By the time this runs the sentex is
  durably stored and indexed; the image is a cache of the derived half, and `save!` is
  full of steps that can throw for reasons that say nothing about the record — a full
  disk, a section that will not map.  Letting one out would take down the assert *after*
  it succeeded, and skip the observation call sites that come after this call, leaving an
  incremental matcher's alpha memories permanently behind the store.  So the failure is
  logged and swallowed, the same posture `close-dir!` above takes for the close-path save,
  and the image simply stays as stale as it was — which the next open catches and rebuilds
  from.

  `roots-now` is passed in rather than read here — the caller has the index and this
  namespace does not depend on it."
  [cdir roots-now]
  (when-let [save-fn (get-in @stores [cdir :snapshot])]
    (when (snap/due? cdir roots-now)
      ;; the clock is restarted *before* the attempt, not after a success.  A directory
      ;; that cannot be written to is still drifted when this returns, so a cadence
      ;; stamped only by `note-image!` would find the refresh due again on the very next
      ;; assert: an image-sized write per write, each one failing.  Stamping the attempt
      ;; puts a broken directory back on the ordinary interval — it retries, once a floor,
      ;; and a fixed disk resumes without an open.  It adds no work on the happy path,
      ;; where `save!` overwrites this with the real baseline a moment later.
      (snap/note-attempt! cdir)
      (try (save-fn)
           (catch Throwable t
             (trove/log! {:level :warn
                          :msg (str "disk backend: the index snapshot for " cdir
                                    " was not refreshed (" (.getMessage t)
                                    ") — the image on disk stays as it was, and the next"
                                    " open rebuilds from the records if it no longer"
                                    " describes them")}))))))

(def ^:private components [:records :index :overlay-meta])

(defn- close-component!
  "Attempt one component close, returning nil on success or the Throwable it threw.
  A component close fsyncs and can compact, so it can fail (a full disk), and a
  failure must not stop `close-dir!`: every component still gets its close attempt,
  and the lock release + registry removal run regardless.  The failure is logged here
  with its component named, and the first one is rethrown once the directory is
  genuinely released."
  [label thunk]
  (try (thunk) nil
       (catch Throwable t
         (trove/log! {:level :error
                      :msg (str "disk backend: close of " label " failed: "
                                (.getMessage t))})
         t)))

(defn opened
  "What is currently open for `dir`: the subset of `#{:records :index :overlay-meta}` this
  JVM holds stores for.  Empty when the directory has never been opened (or has been
  closed)."
  [dir]
  (let [e (@stores (canonical-dir dir))]
    (set (filter #(some? (get e %)) components))))

(defn close-dir!
  "Close and forget the stores for `dir`: fsync + close whichever components are open,
  deregister them from the durability daemon, and release the lock.  For explicit
  shutdown and test teardown — ordinary operation leaves the stores open for the JVM's
  life (the shutdown hook closes them).

  This is what `vaelii.core/close!` exists for — handing the directory to another
  process without exiting the JVM — so an unclean close must not defeat it: every
  component gets its close attempt, the lock release and the registry removal run even
  when one throws, and the first component failure is rethrown *after* that cleanup.
  The caller learns the close did not complete cleanly, and the directory is still
  released either way.

  **The order is the contract**, because handing a directory over is the point:
  deregister → abort any rewrite → join the compactor → write the image → close the
  components → release the lock.  Releasing the OS lock is the last thing that happens,
  because it is the thing the other process is waiting on, and everything above it is a
  file of this directory's still being written."
  [dir]
  (let [cdir (canonical-dir dir)]
    (locking stores
      (when-let [{:keys [records index overlay-meta snapshot reasoning-image dur-ids]} (@stores cdir)]
        ;; Deregister first: it is the signal a task the compaction executor has queued
        ;; but not started reads, so it turns every waiting rewrite of this directory
        ;; into a skip rather than something to wait out.  It also stops the next daemon
        ;; tick queueing a fresh one behind our backs, which is what makes the join below
        ;; terminate.
        (doseq [id (vals dur-ids)] (dur/deregister! id))
        ;; Then stop the rewrite that is already running, and wait for it.  The record
        ;; store's rewrite phase holds no lock on purpose (`record-store/compact-kind!`),
        ;; so nothing a close does to the store blocks it: it reads through a private
        ;; handle and appends to `sentexes.log.compact` *by name*, which is a path the
        ;; next process to own this directory will compact over.  Releasing the OS lock
        ;; with that rewrite still running is two processes appending to one temp log and
        ;; a replay installing frames from both — the exact tearing the directory lock
        ;; exists to prevent, under a setting (`vaelii.disk.auto-compact`) that is on by
        ;; default.  The abort makes the wait short; the wait makes the release honest.
        (when records (drs/abort-compaction! records))
        (dur/await-compaction-quiescent! (vals dur-ids))
        ;; The image after the join and before the closes: it is stamped against the
        ;; records, so it has to be written while they are still open *and* while nothing
        ;; is rewriting the offsets underneath it — and a failure to write one must not
        ;; stop the close.
        (when snapshot
          (try (snapshot)
               (catch Throwable t
                 (trove/log! {:level :warn
                              :msg (str "disk backend: the index snapshot for " cdir
                                        " was not written (" (.getMessage t)
                                        ") — the next open rebuilds from the records")}))))
        ;; the reasoning image under the same two conditions, and `save!` logs and swallows
        ;; its own failure
        (when reasoning-image (reasoning-image))
        (let [failures (into []
                             (keep identity)
                             [(when records
                                (close-component! (str "disk-records " cdir)
                                                  #(drs/close! records)))
                              (when index
                                (close-component! (str "disk-index " cdir)
                                                  #(dkv/close! (:backend index))))
                              (when overlay-meta
                                (close-component! (str "overlay-meta " cdir)
                                                  #(dkv/close! overlay-meta)))])]
          (lock/release! cdir)
          (swap! stores dissoc cdir)
          ;; after the close wrote one, so the next open measures its drift against the
          ;; image it actually finds rather than against one this process left behind
          (snap/forget-image! cdir)
          (when-first [t failures] (throw t)))))))

(defn disk-dir
  "The directory a disk KB lives in.  `:dir` names it explicitly; otherwise it derives
  from the space number under a base (`vaelii.disk.dir`, else `<tmpdir>/vaelii-disk`), so
  the space the other backends key on still names a distinct store."
  [{:keys [dir space] :or {space 0}}]
  (or dir
      (let [base (or (System/getProperty "vaelii.disk.dir")
                     (str (System/getProperty "java.io.tmpdir") "/vaelii-disk"))]
        (str base "/space-" space))))
