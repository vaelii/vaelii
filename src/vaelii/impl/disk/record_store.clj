;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.record-store
  "The record store on disk — an implementation of `RecordStore` over per-kind
  log/idx pairs (`vaelii.impl.disk.files`).

  Three int-keyed kinds — sentexes, justifications, provenance — each a `.log` of
  length-prefixed nippy frames plus a `.idx` of fixed 24-byte slots mapping handle →
  log offset.  A frame holds its record's fields **positionally**
  (`vaelii.impl.disk.codec`), so the type tag and field names are not rewritten into
  every one of them; a frame written before that codec still reads, as its own shape.  A record is **paged** from disk on `get`: read the slot, read the frame
  it points at, thaw it — two positional reads, no seek, and the records do not sit in
  RAM.  What does sit in RAM per kind is the set of live handles (so enumeration is
  O(1)), rebuilt from the idx on open, and a **bounded LRU of hot records** in front
  of the read (`vaelii.disk.cache`, 0 to disable).

  That live set is a **compressed bitmap** (`vaelii.impl.handle-set`'s `LiveHandleSet`), not a
  `PersistentHashSet<Long>`.  Handles are minted in assertion order, so a live set is a
  strided run of longs with holes where records were deleted, and the boxed set retains
  48–75 bytes a handle for it — 9.47 GB at 100M records, the second-largest resident row
  in the engine (`docs/density.md`).  A bitmap answers all four things the
  set is asked (membership, iteration, cardinality, a first handle) at about a bit a
  handle.  What it costs is a monitor: the bitmap is mutated in place and is not
  thread-safe, so a read of the live set takes the kind lock, exactly as a write does —
  see the two-monitors section below.

  `next-id` is a monotonic counter recovered as `max(the counters blob, 1 + the
  highest slot id across the record kinds)` — the highest slot id is stable across
  deletes (a tombstone keeps its slot) and across compaction (slot ids are preserved),
  so a handle is never reused even if the counters blob is stale after a crash.  Within
  a session every write holds the same bound (`clear-counter!`), because a record can
  arrive carrying its own `:id` and nothing re-reads the slots until the next open.

  A premise is exactly a sentex whose `:strength` is non-nil (the strength lives on
  the record, as on every backend), so the premise set is derived from the durable
  records — rebuilt on open, maintained in lockstep by mark/unmark — rather than
  stored separately.  Rebuilding it does not mean *reading* them: every write records
  the answer in its idx slot's flags, so the open reads the set off the slot walk it
  already makes.  A slot that does not carry the bit sends that one handle to its
  record, and the record is authoritative wherever both speak (`rebuild-premises!`).

  The premise's **strength rank** rides the same slot flags (bits 2..3), so
  `premise-strength` — read once per premise on every `recover` — answers off the 24-byte
  slot instead of paging the whole record for one keyword.  A slot carrying no rank (a
  non-premise, or one older than the bits) falls back to the record, the same
  no-format-bump story as the premise bit itself (`f/slot-strength`).

  Recovery on open: finish any interrupted compaction, truncate a torn log tail, then
  tombstone any slot whose frame now extends past the log (`validate-idx-tail!`).
  Crash-safety rests on the write ordering (append the frame, then point the slot at it)
  and on `files`' crash-safe compaction.  Where it stops is the slot itself: 24 bytes do
  not divide a page, so a crash can leave one spliced from two writes, and a splice still
  pointing inside the log is reported as a thaw failure on that handle rather than caught
  here (`f/validate-idx-tail!` says what it does and does not cover).

  The tail is located from the frame *lengths*
  (`files/log-tail-offset`) and nothing is decoded to find it — and a clean `close!`
  records each log's length, so an open whose log is still that long skips even the walk.
  The marker is consumed here, so it never describes a store in use; every disagreement
  falls back to the walk.

  Every RAF touch holds the owning kind's lock.  A write or `force!` must, because the
  file pointer is shared (see `files`' shared-pointer invariant); a read is positional
  and need not, but still does, because that is what serializes it against a concurrent
  append and its slot write.

  **Two monitors, and which resident field sits under which.**  Three threads touch this
  store — the writer, the durability daemon (`fsync`, every few seconds) and the
  compaction executor — so the resident state is not the writer's alone and a field
  mutated outside a monitor is one a reader can catch mid-pair.

  - The **kind lock** covers that kind's log, its idx, and the resident state derived
    from them: `live-ids`, `live-bytes`, the hot-record cache, `compacting` and
    `failed`.  A store, a kill, a batch and the compactor's reconcile each take it once
    and do both halves inside it, so an id is never live to a reader while its slot says
    tombstone, and the compaction delta set is never cleared under a writer folding an id
    into it.

    It covers `live-ids` on the **read** side too, which the other three do not need: the
    live set is a bitmap mutated in place, so a tally or an enumeration taken beside a
    concurrent `addLong` reads a structure mid-edit.  A read that hands the set onward
    takes a `hs/live-snapshot` inside the lock and lets go of it — the copy costs the
    bitmap's size, not the corpus's, which is what makes holding the writer's monitor for
    an enumeration affordable at all.
  - **`counters-lock`** covers the three that move together and belong to no kind: the
    handle `counter`, the `counters.nippy` blob, and `synced-seq` — read and written by
    `fsync` on the daemon's thread and by `clear-records!` on the writer's.  Its own
    monitor rather than a kind's, because a whole-file blob rewrite held inside a kind
    lock would put a record append behind it every tick that minted a handle.

  `premises` is a `LiveHandleSet` too, and sits under the **sentexes** kind lock for reads
  and writes alike, because a premise is a sentex handle.  It is not folded into
  `store!`'s acquisition: a premise joins the premise set after its record lands, in a second
  acquisition, so a failed write leaves no handle in `premise-ids` whose `get-sentex` is
  nil.  The compactor's `drop-lost!` removes from it only when compacting the sentexes
  kind, under the lock it already holds."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.codec :as codec]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.handle-set :as hs]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.store :as store-types]))

(def ^:private kind-names ["sentexes" "justifications" "provenance"])

;; `vaelii.disk.tokens` and `vaelii.disk.cache` are read at the store's **open**
;; (`open-record-store`), not here.  A `def` reading a property is a read at namespace
;; load, and a load-time refusal of `vaelii.disk.cache=64k` reports as a namespace that
;; will not load — the typo delivered as a broken build.  `config` owns both domains.

;; ---- the hot-record cache ----------------------------------------------
;; A bounded LRU in front of a record fetch (two positional reads plus a nippy thaw, ~3 µs
;; warm) serves 64% of a zipfian stream at 1k entries and 79% at 10k (`lein bench-records`).
;; A record is an immutable value: `store!` replaces the cached value, `kill!` drops it,
;; `clear-records!` empties the cache, and compaction preserves every id's content.  A bulk
;; sweep (`export!`, `reindex`, a fork's `recover`) promotes like any read; refilling costs at
;; most `cap` misses, 22 ms against a 2.6 s sweep of 800k records (docs/storage.md, "A bulk
;; sweep claims recency").

(defn- lru
  "A bounded access-ordered LRU map, synchronized: an access-ordered `LinkedHashMap`
  reorders itself on `get`, so a read is a structural modification and readers must
  synchronize with each other as well as with writers."
  ^java.util.Map [^long cap]
  (java.util.Collections/synchronizedMap
   (proxy [java.util.LinkedHashMap] [16 0.75 true]
     (removeEldestEntry [_] (> (.size ^java.util.LinkedHashMap this) cap)))))

;; The kind lock is a `ReentrantReadWriteLock`, not a bare monitor.  It serializes a read
;; against a concurrent append + slot rewrite (`store!`/`kill!`/compaction), which is what
;; a positional read needs protection from — but two positional reads are safe against
;; each other, so `fetch` takes the **read** lock and a bulk sweep (`export!`, `reindex`,
;; `recover`) fans its per-record fetch+decode across cores instead of funnelling every
;; one through a single monitor.  Every mutating site takes the **write** lock, which
;; excludes readers and writers alike — identical exclusion to the old monitor.  Read
;; while holding write is fine (a writer may fetch); write while holding read is an
;; upgrade and deadlocks, so `fetch`'s body never takes the write lock.  Its one write, the
;; hot-cache put, goes to a synchronized map under that map's own monitor.
(defmacro ^:private with-write [lockexpr & body]
  `(let [^java.util.concurrent.locks.ReentrantReadWriteLock l# ~lockexpr
         ^java.util.concurrent.locks.Lock w# (.writeLock l#)]
     (.lock w#)
     (try ~@body (finally (.unlock w#)))))

(defmacro ^:private with-read [lockexpr & body]
  `(let [^java.util.concurrent.locks.ReentrantReadWriteLock l# ~lockexpr
         ^java.util.concurrent.locks.Lock r# (.readLock l#)]
     (.lock r#)
     (try ~@body (finally (.unlock r#)))))

(defn- track-touched
  "Record `id` in an in-flight compaction's touched set (a no-op when none is running).
  Called under the kind lock, so it races nothing."
  [k id]
  (swap! (:compacting k) (fn [c] (if c (update c :touched conj id) c))))

(defn- usable!
  "Refuse an access to kind `k` once a compaction has failed past its commit point
  (`compact-kind!`): the live log and idx may be half-copied.  `failed` holds the failure; the
  next open finishes the install off the commit marker.

  The store's fault latch is read first and has no exemptions: a closed channel, a failed
  write (`files/with-io-guard`), a failed fsync or a `close!` latches `:fault`, and every later
  call refuses with `:store-unusable`.  Consulted by every access to the files (`store!`,
  `fetch`, `kill!`, `premise-strength`'s slot read) and by `slot-fingerprint`,
  `kind-dead-ratio` and `compact-kind!`, which decide from the files.  Not consulted by
  `sentex-ids` / `justification-ids` / `premise-ids` (they answer from the in-memory live-id
  sets), by `fsync` (it forces written bytes), or by `clear-records!`, which supersedes the
  pending install.  See docs/storage.md."
  [k]
  (f/check-fault! (:fault k))
  (when-let [t @(:failed k)]
    (throw (ex-info (str "disk record store: a compaction of " (:log-path k)
                         " failed after its commit point — the live files are unusable"
                         " until the store is reopened, which finishes the install off"
                         " the commit marker")
                    {:type :compaction-failed :log (:log-path k)}
                    t))))

;; ---- live frame bytes ---------------------------------------------------
;; `dead-ratio` is `1 - live-bytes / log-length` per kind, and `live-bytes` is the sum of
;; `frame-bytes` over the slots `f/scan-idx!` yields.  The open seeds it from the walk it
;; already makes, and every write to a live idx moves it by what it adds and what it
;; supersedes, under the kind lock, so the probe reads a counter and a file length.

(defn- frame-bytes
  "The log bytes a frame of `length` payload bytes occupies: the 4-byte prefix and the
  payload."
  ^long [^long length]
  (+ 4 length))

(defn- idx-live-bytes
  "`live-bytes` for `idx`, summed over a walk of every slot.  Only a compaction install
  calls it, since the install replaces the whole idx."
  ^long [idx]
  (let [n (volatile! 0)]
    (f/scan-idx! idx (fn [_ _ length _] (vswap! n + (frame-bytes length))))
    @n))

(defn- superseded-bytes
  "The frame bytes a write to slot `id` of kind `k` takes out of `live-bytes`: its
  current frame's when the id is live, else 0.  A write to an id not in the live set reads
  no slot.  Caller holds the kind write lock and the io guard."
  ^long [k id]
  (if (hs/live-has? (:live-ids k) id)
    (let [slot (f/read-slot (:idx k) id)]
      (if (and slot (not (:tombstone? slot))) (frame-bytes (:length slot)) 0))
    0))

(defn- open-kind
  "Open (recovering) the log/idx pair `dir/<name>.{log,idx}` and build its live-id set.

  `clean-length` is what the last clean close recorded for this log, if anything; a log
  still that length has no torn tail and skips the walk.  `validate-idx-tail!` runs
  either way — a skipped scan is not a skipped validation.

  `slot-tap` (optional) is called with `[id flags]` for every live slot, so a caller
  that wants what the slots say rides this walk rather than making a second one."
  [dir name cache-cap codecs clean-length slot-tap fault]
  (let [log-path (str dir "/" name ".log")
        idx-path (str dir "/" name ".idx")]
    (f/recover-compaction! log-path idx-path)
    (let [log (f/open-log log-path)
          ;; from here to the return every step can throw — a torn tail, a truncation on
          ;; a full disk, an unreadable slot — and a `Kind` that never gets built is one
          ;; nothing will ever close.  So the recovery runs under a guard that gives the
          ;; two handles back before the failure travels.
          idx (try (f/open-idx idx-path)
                   (catch Throwable t (f/close! log) (throw t)))]
      (try
        (f/truncate-log! log (first (f/log-tail-offset-from log clean-length)))
        (f/validate-idx-tail! idx log)                        ; tombstone slots past EOF
        ;; the live set is filled straight off the scan, which walks slots by position and
        ;; so hands ids up in ascending order — the one order Roaring's run containers
        ;; want, and `live-optimize!` folds the runs once the walk is done.  Nothing
        ;; intermediate is built, so an open's peak is the live set itself.
        (let [live  (hs/live-handle-set)
              bytes (volatile! 0)
              {:keys [enc dec]} (codecs name)]
          (with-open [r (progress/start ::read-slots (str "open: read the " name " slots")
                                        (f/slot-count idx))]
            (f/scan-idx! idx (fn [id _ length flags]
                               (hs/live-add! live id)
                               (vswap! bytes + (frame-bytes length))
                               (when slot-tap (slot-tap id flags)))
                         r))
          (hs/live-optimize! live)
          (store-types/->Kind log idx (java.util.concurrent.locks.ReentrantReadWriteLock.) live log-path idx-path (atom nil) (atom nil)
                              (when (pos? cache-cap) (lru cache-cap)) enc dec fault
                              (atom @bytes)))
        (catch Throwable t
          (f/close! log)
          (f/close! idx)
          (throw t))))))

(defn- counters-path [dir] (str dir "/counters.nippy"))

(defn- counters-blob
  "The `counters.nippy` blob for handle counter `n` and clear epoch `epoch`, which is
  omitted while nil."
  [n epoch]
  (cond-> {:seq n} epoch (assoc :epoch epoch)))

(defn- store!
  "Append `rec` to kind `k`, point slot `id` at the new frame, and mark `id` live.  Returns
  `id`.  Holds the kind lock.  `premise?` is written into the slot's flags so the next open
  reads the premise set off the idx walk (`f/premise-flags`); only the sentexes kind has
  premises.  The resident half (live set, record cache) is updated inside the same lock
  acquisition as the file half, so a reader on another thread never sees them disagree."
  ([k id rec] (store! k id rec false))
  ([k id rec premise?]
   (with-write (:lock k)
     (usable! k)
     (f/with-io-guard (:fault k) (:log-path k) true
       (let [was        (superseded-bytes k id)
             [off plen] (f/append-record-sized! (:log k) ((:enc k) rec))]
         ;; the premise's strength rides the slot too (bits 2..3), so `premise-strength`
         ;; reads it off the idx the open walk already makes rather than paging the record
         (f/write-slot! (:idx k) id off plen
                        (f/premise-flags premise? (strength/rank-of (:strength rec))) 0)
         (swap! (:live-bytes k) + (- (frame-bytes plen) was))))
     (track-touched k id)
     (hs/live-add! (:live-ids k) id)
     ;; a just-written record is hot, and this is also what keeps the cache current when a
     ;; re-store (mark-premise) replaces an id's record with a different value
     (when-let [^java.util.Map c (:cache k)] (.put c id rec)))
   id))

(defn- store-batch!
  "Append every record of `batch` to kind `k` and point its slot at the frame, with one log
  write and one idx write per run of consecutive handles.  `batch` is `[id rec premise?]`
  triples; the lock is taken once.  The written records are evicted from the hot cache and not
  installed, so a bulk load does not fill the LRU and a re-store cannot serve a stale record.
  All-or-nothing on the log (`f/append-records-sized!`); not a transaction across the two
  files, and the write order is `store!`'s (frames, then slots), so a crash leaves frames no
  slot names."
  [k batch]
  (when (seq batch)
    (with-write (:lock k)
      (usable! k)
      (f/with-io-guard (:fault k) (:log-path k) true
        (let [offs (f/append-records-sized! (:log k) (map (fn [[_ rec _]] ((:enc k) rec)) batch))
              ;; id → the frame bytes its slot will point at; a later entry for the same
              ;; id replaces an earlier one, as its slot write does in `write-slots!`
              now  (java.util.HashMap.)
              _    (doseq [[[id] [_ plen]] (map vector batch offs)]
                     (.put now id (frame-bytes plen)))
              was  (reduce (fn [^long acc id] (+ acc (superseded-bytes k id))) 0 (.keySet now))]
          (f/write-slots! (:idx k)
                          (map (fn [[id rec premise?] [off plen]]
                                 [id off plen
                                  (f/premise-flags premise? (strength/rank-of (:strength rec)))
                                  0])
                               batch offs))
          (swap! (:live-bytes k) + (- (reduce + 0 (.values now)) was))))
      (doseq [[id] batch] (track-touched k id))
      ;; the resident half under the same acquisition, for `store!`'s reason
      (hs/live-add-all! (:live-ids k) (map first batch))
      (when-let [^java.util.Map c (:cache k)]
        (doseq [[id] batch] (.remove c id)))))
  nil)

(defn- page
  "Thaw the record `slot` points at in kind `k`.  Caller holds the kind's read lock and
  the io guard."
  [k slot]
  (some-> (f/read-record-sized (:log k) (:offset slot) (:length slot)) ((:dec k))))

(defn- fetch
  "The record at handle `id` in kind `k`, or nil — from the hot cache, else paged from
  disk (one positional slot read, one positional frame read).  Anything that is not a
  handle this store could have issued reads as nil: a non-integer (callers pass an
  informant keyword/symbol to `get-sentex`) and a negative one (which would otherwise
  reach `read-slot` as a negative file position and throw).  Both are the nil the memory
  store returns for a key it does not hold — a lookup must not depend on the backend.

  Refused outright — cache hit or not — once the kind is `failed`: a cached value would
  still be right, but a store half of whose reads answer and half refuse is harder to
  reason about than one that says so on every call."
  [k id]
  (when (and (integer? id) (not (neg? (long id))))
    (usable! k)
    (let [^java.util.Map c (:cache k)]
      (or (when c (.get c id))
          ;; The read lock is kept although both reads are positional: it serializes a read
          ;; against a concurrent append + slot rewrite, and concurrent fetches run in
          ;; parallel while `store!`/`kill!`/compaction hold the write lock.  The cache put is
          ;; inside the read lock too: after the unlock it could reinstate a record a writer
          ;; just tombstoned or replaced.
          (with-read (:lock k)
            (let [rec (f/with-io-guard (:fault k) (:log-path k) false
                        (when-let [slot (f/read-slot (:idx k) id)]
                          (when-not (:tombstone? slot) (page k slot))))]
              (when (and c rec) (.put c id rec))
              rec))))))

(defn- premise-mark-read
  "One handle of a bulk premise mark at strength rank `rank`, decided from its slot:
  nil when kind `k` holds no record at `id` (unwritten or tombstoned), `::marked` when
  the slot already records a premise at `rank`, else the record.  The record is paged
  without `fetch`'s hot-cache put, so a sweep of the premise set leaves the LRU as it
  found it.  The slot's rank is a cache over the record that a dirty open reconciles
  (`f/reconcile-slot-flags!`), the same trust `premise-strength` places in it."
  [k ^long id ^long rank]
  (usable! k)
  (with-read (:lock k)
    (f/with-io-guard (:fault k) (:log-path k) false
      (when-let [slot (f/read-slot (:idx k) id)]
        (when-not (:tombstone? slot)
          (let [flags (long (:flags slot))]
            (if (and (pos? rank) (f/slot-premise flags) (= rank (f/slot-strength flags)))
              ::marked
              (page k slot))))))))

(defn- handle-order
  "The keys of `id->strength` that this store could have issued as handles, ascending.
  A non-integer or negative key is dropped: `fetch` reads it as no record."
  ^longs [id->strength]
  (let [ids (long-array (filter #(and (integer? %) (not (neg? (long %))))
                                (keys id->strength)))]
    (java.util.Arrays/sort ids)
    ids))

(defn- kill!
  "Tombstone handle `id` in kind `k` and drop it from the live set (a no-op when it
  was never live).  The tombstone and the two resident drops are one acquisition, for
  `store!`'s reason: an id that is live to a reader and tombstoned on disk is a handle
  `sentex-ids` names and `get-sentex` answers nothing for.

  The liveness test is **inside** the lock with the drop it guards, because the live set it
  reads is a bitmap mutated in place: a test outside would read one beside a concurrent
  append.  It is the same acquisition either way — the test only ever decided whether to
  take one."
  [k id]
  (with-write (:lock k)
    (when (hs/live-has? (:live-ids k) id)
      (usable! k)
      (f/with-io-guard (:fault k) (:log-path k) true
        (let [was (superseded-bytes k id)]
          (f/tombstone-slot! (:idx k) id)
          (swap! (:live-bytes k) - was)))
      (track-touched k id)
      (hs/live-remove! (:live-ids k) id)
      (when-let [^java.util.Map c (:cache k)] (.remove c id)))))

(defn- clear-counter!
  "Keep `counter` — the next handle to issue — above `id`, and return `id`.  Called on
  every record write, because `put-sentex` / `put-justification` both honour an explicit
  `:id` (an import lands records at the handles its dump gave them) and a counter left
  behind one would reissue it, overwriting a record silently.  Recovery derives the same
  bound from the idx slots on open; this is what holds it *within* a session, where
  nothing re-reads them.  A no-op when the id came from `next-id`."
  [counter id]
  (swap! counter max (inc (long id)))
  id)

(def ^:private default-batch
  "Records buffered before one log write and one idx write.  The unit is a packed byte
  buffer, so it trades peak heap against syscalls and neither end is delicate."
  10000)

(defn- disk-sink
  "A `RecordSink` over kind `kind-key` of `store`, landing `batch` records per pair of
  writes.

  **`:premises? false` is not honoured here.**  This store's `put-sentex`
  adds a premise to the premise set from the record's own `:strength` whatever a caller does next — the
  strength rides the idx slot's flags so the next open reads the premise set off the slot
  walk — so a sink that dropped the mark would leave a store the loop it replaces would
  not have left, and a sink must be equal to that loop or it is not a sink.  The option is
  about what a sink *adds*; on this store the put already did it."
  [store kind-key batch]
  (when-not (pos? (long batch))
    (throw (ex-info (str "a bulk :batch must be a positive number of records, got "
                         (pr-str batch))
                    {:type :bad-batch :batch batch})))
  (let [k        (get (:kinds store) kind-key)
        counter  (:counter store)
        premises (:premises store)
        sentexes? (= kind-key :sentexes)
        pending  (java.util.ArrayList.)
        ;; The premise set is joined **after** the write, which is the order
        ;; `put-sentex` takes and therefore the order a sink standing in for it owes: a
        ;; `store-batch!` that throws (a full disk) must not leave up to `batch` handles
        ;; in `premise-ids` whose `get-sentex` is nil for the rest of the session.  The
        ;; flag rides `pending`'s triple, so nothing extra is held to do it.
        flush!   (fn []
                   (when-not (.isEmpty pending)
                     (let [recs (vec pending)]
                       (store-batch! k recs)
                       (when sentexes?
                         (let [ps (into [] (comp (filter (fn [[_ _ p?]] p?)) (map first))
                                        recs)]
                           (when (seq ps)
                             (with-write (:lock k) (hs/live-add-all! premises ps)))))
                       (.clear pending))))]
    (reify
      p/RecordSink
      (write-record! [_ rec]
        (let [id  (clear-counter! counter (or (:id rec) (p/next-id store)))
              rec (assoc rec :id id)]
          (.add pending [id rec (and sentexes? (some? (:strength rec)))])
          (when (>= (.size pending) (long batch)) (flush!))
          id))

      java.io.Closeable
      (close [_] (flush!) nil))))

;; `synced-seq` is what the `counters.nippy` blob was last left holding, so `fsync` can tell
;; an idle tick from one with a handle to persist.  nil until the first tick writes it.
;;
;; `counters-lock` is the monitor over the counter, the blob and `synced-seq`.  It is not a
;; kind lock, because holding one across a whole-file blob rewrite would put a record append
;; behind it; the pair it serializes is `fsync` (durability daemon thread) and
;; `clear-records!` (writer thread).
;;
;; `epoch` is nil for a store no `clear-records!` has emptied, else the random long the latest
;; wipe minted.  The counters blob carries it and both slot fingerprints fold it in
;; (`slot-fingerprint`, `reasoning-fingerprint`).
(defrecord DiskRecordStore [dir kinds counter synced-seq premises dict counters-lock epoch fault
                            reserved]
  p/RecordStore
  (next-id [_]
    (if-let [r @reserved]
      (long (dec (swap! counter #(inc (cap/skip-reserved r (long %))))))
      (long (dec (swap! counter inc)))))

  (put-sentex [this sentex]
    (let [id  (clear-counter! counter (or (:id sentex) (p/next-id this)))
          rec (assoc sentex :id id)]
      (observe/keep-before! this [:sentex id] #(fetch (:sentexes kinds) id))
      (store! (:sentexes kinds) id rec (some? (:strength rec)))
      (when (:strength rec)
        (with-write (:lock (:sentexes kinds)) (hs/live-add! premises id)))
      id))
  ;; Tallied by kind (`vaelii.impl.profile`), the same call sites the RAM store carries, and
  ;; this is the store the number is *about*: a miss here is a positional slot read, a
  ;; positional frame read and a nippy thaw, where an index read is a map lookup.  On the
  ;; protocol method rather than inside `fetch`, so the two stores count the same events —
  ;; `mark-premise` below re-fetches where the RAM store reaches into its state map.
  (get-sentex [_ id] (prof/record-fetch :sentex id) (fetch (:sentexes kinds) id))
  (delete-sentex! [this id]
    (observe/keep-before! this [:sentex id] #(fetch (:sentexes kinds) id))
    (kill! (:sentexes kinds) id)
    (with-write (:lock (:sentexes kinds)) (hs/live-remove! premises id))
    (kill! (:provenance kinds) id)          ; provenance dies with its record
    nil)

  (put-justification [this justification]
    (let [id (clear-counter! counter (or (:id justification) (p/next-id this)))]
      (observe/keep-before! this [:justification id] #(fetch (:justifications kinds) id))
      (store! (:justifications kinds) id (assoc justification :id id))
      id))
  (get-justification [_ id] (prof/record-fetch :justification) (fetch (:justifications kinds) id))
  (delete-justification! [this id]
    (observe/keep-before! this [:justification id] #(fetch (:justifications kinds) id))
    (kill! (:justifications kinds) id)
    (kill! (:provenance kinds) id)
    nil)

  (put-provenance    [_ id prov] (store! (:provenance kinds) id prov) prov)
  (get-provenance    [_ id]      (prof/record-fetch :provenance) (fetch (:provenance kinds) id))
  (delete-provenance! [_ id]     (kill! (:provenance kinds) id) nil)

  ;; Each enumeration answers the snapshot itself, an immutable `HandleSet` taken under
  ;; the lock.  The snapshot is a bitmap copy and costs the handle set's size, not the extent.
  ;; The protocol promises a `java.util.Set` answering membership, iteration, cardinality
  ;; and ordering, which the handle set answers; a caller wanting `conj` converts with `set`.
  (sentex-ids [_]
    (prof/record-fetch :sentex-ids)
    (f/check-fault! fault)
    (with-write (:lock (:sentexes kinds))
      (hs/live-snapshot (:live-ids (:sentexes kinds)))))
  (justification-ids [_]
    (prof/record-fetch :justification-ids)
    (f/check-fault! fault)
    (with-write (:lock (:justifications kinds))
      (hs/live-snapshot (:live-ids (:justifications kinds)))))

  (mark-premise [_ id strength]
    ;; the strength lives on the sentex record: re-store it with :strength set (a new
    ;; frame; the old one becomes dead and compaction reclaims it), and track the
    ;; premise in the derived set.  Guard on existence — a handle with no sentex must
    ;; not be marked.
    ;;
    ;; A record already carrying this strength is left alone, which is the ordinary
    ;; assert: `kb/create-sentex` writes the strength into the first frame, and a
    ;; re-assert of a stored premise asks for the strength it already has.  Storing it
    ;; again would append a whole second frame and kill the first — half the log dead on
    ;; arrival, and the compaction threshold tripped by the writer's own bookkeeping.
    (let [k    (:sentexes kinds)
          want (or strength :default)]
      (when-let [sx (fetch k id)]
        (when-not (= want (:strength sx))
          (store! k id (assoc sx :strength want) true))
        (with-write (:lock k) (hs/live-add! premises id))))
    nil)
  (unmark-premise! [_ id]
    ;; the same guard as mark-premise, pointing the other way: a derived record's
    ;; :strength is already nil, and re-storing it would append a frame whose only
    ;; fate is the tombstone the retraction writes right after
    (let [k (:sentexes kinds)]
      (when-let [sx (fetch k id)]
        (when (some? (:strength sx))
          (store! k id (assoc sx :strength nil) false)))
      (with-write (:lock k) (hs/live-remove! premises id)))
    nil)
  ;; the snapshot under the lock, answered as it is, as `sentex-ids` does
  (premise-ids [_]
    (prof/record-fetch :premise-ids)
    (f/check-fault! fault)
    (with-write (:lock (:sentexes kinds))
      (hs/live-snapshot premises)))
  (premise-strength [_ id]
    ;; The rank is read off the slot (bits 2..3): one positional 24-byte read, no frame and
    ;; no thaw.  A rank-0 slot (a non-premise, or older than the strength bits) falls back to
    ;; the record, as the premise bit does, and any write upgrades the slot.  The rank is a
    ;; cache over the record with the premise bit's flags-word residual (`rebuild-premises!`).
    ;; The id is guarded as `fetch` guards it, so a non-integer or negative id is the nil the
    ;; memory store answers.
    (prof/record-fetch :premise-strength)
    (let [k (:sentexes kinds)]
      (if (and (integer? id) (not (neg? (long id))))
        (if-let [slot (with-write (:lock k)
                        (usable! k)
                        (f/with-io-guard (:fault k) (:log-path k) false (f/read-slot (:idx k) id)))]
          (let [rank (f/slot-strength (:flags slot))]
            (if (pos? rank)
              (strength/class-of-rank rank)
              (or (:strength (fetch k id)) :default)))
          :default)
        :default)))

  (clear-records! [_]
    ;; The counter, the blob, `synced-seq` and the epoch change as one step, under the
    ;; monitor `fsync` takes for the first three, so a daemon tick cannot write a pre-wipe
    ;; high-water mark after the wipe.  The wipe truncates every log, so a new record can
    ;; reproduce a removed record's slot exactly; a new epoch separates the two record sets in
    ;; a slot fingerprint.  The blob carrying it is written before the truncation, so a crash
    ;; between the two declines an image and never accepts one over new records.  A counter of
    ;; 1 beside the old records reissues no handle, since `recover-next-id` starts past the
    ;; highest slot.
    (f/check-fault! fault)
    (let [e (.nextLong (java.util.concurrent.ThreadLocalRandom/current))]
      (locking counters-lock
        (reset! epoch e)
        (reset! counter 1)
        (f/write-nippy-atomic! (counters-path dir) (counters-blob 1 e))
        (reset! synced-seq 1)))
    (doseq [k (vals kinds)]
      (with-write (:lock k)
        (f/truncate! (:log k))
        (f/truncate! (:idx k))
        (hs/live-clear! (:live-ids k))
        (reset! (:live-bytes k) 0)
        (when-let [^java.util.Map c (:cache k)] (.clear c))
        ;; an in-flight compaction snapshotted the pre-wipe state — tell it to abort
        ;; (discard its temps) rather than replay them over the now-empty files.
        (swap! (:compacting k) (fn [c] (when c (assoc c :aborted true))))
        ;; A compaction that failed past its commit point left the marker and both temps
        ;; on disk for the next open to finish the install off — so a wipe that leaves
        ;; them is undone by that open, which replays the pre-wipe records over the
        ;; truncated files.  The wipe supersedes the install: drop the marker and the
        ;; temps under the same lock, and the kind is usable again.
        (let [{:keys [temps marker]} (f/compact-temp-paths (:log-path k) (:idx-path k))]
          (f/delete-compact-temps! marker temps))
        (reset! (:failed k) nil)))
    (with-write (:lock (:sentexes kinds)) (hs/live-clear! premises))
    ;; the dictionary goes with them: no frame survives to hold an id, and keeping the
    ;; ids would leave a wiped store carrying its predecessor's whole vocabulary
    (when dict (dtok/clear! dict))
    nil)

  ;; Both live-id sets and the premise set are resident already (the namespace
  ;; docstring says why), so a tally is a read of one of them rather than the `set` copy
  ;; the enumeration takes.  On a bitmap it is the cardinality it already tracks and the
  ;; lowest set bit — neither walks the set, so all four are O(1) under a lock the
  ;; writer holds only for two file writes.
  p/Tallying
  (sentex-tally [_]
    (f/check-fault! fault)
    (with-write (:lock (:sentexes kinds))
      (hs/live-tally (:live-ids (:sentexes kinds)))))
  (justification-tally [_]
    (f/check-fault! fault)
    (with-write (:lock (:justifications kinds))
      (hs/live-tally (:live-ids (:justifications kinds)))))
  (a-sentex-id [_]
    (f/check-fault! fault)
    (with-write (:lock (:sentexes kinds))
      (hs/live-least (:live-ids (:sentexes kinds)))))
  (a-justification-id [_]
    (f/check-fault! fault)
    (with-write (:lock (:justifications kinds))
      (hs/live-least (:live-ids (:justifications kinds)))))
  (a-premise-id [_]
    (f/check-fault! fault)
    (with-write (:lock (:sentexes kinds))
      (hs/live-least premises)))

  p/HandleReserving
  (reserve-handles! [_ ranges] (swap! reserved cap/reserve-ranges ranges) nil)

  ;; A record at a time here is two syscalls on an unbuffered `RandomAccessFile` — the log
  ;; append and the 24-byte slot write — plus a lock, and a bulk load pays both per record
  ;; for nothing: the frames are known before any of them is written, and handles arrive in
  ;; the consecutive run `next-id` mints, which the idx holds as one contiguous range.
  p/BulkLoading
  (open-sentex-sink [this {:keys [batch] :or {batch default-batch}}]
    (disk-sink this :sentexes batch))
  (open-justification-sink [this {:keys [batch] :or {batch default-batch}}]
    (disk-sink this :justifications batch))

  ;; **Both are chunked here, not by the caller.**  `store-batch!` materializes what it is
  ;; handed — a frozen frame per record and one contiguous `byte-array` over the lot — so
  ;; the bound is a property of the write path and belongs where the write path is.  A
  ;; corpus import calls each of these once with every handle it loaded, and an unchunked
  ;; call would hold a record, a frame and a copy of the packed buffer for all of them at
  ;; once, failing outright past two gigabytes of frames.  `disk-sink` bounds itself at
  ;; `default-batch` for the same reason, and these are the same write underneath it.
  p/BulkAnnotating
  (mark-premise-batch [_ id->strength]
    ;; Each handle is decided from its slot, in handle order, so the slot reads walk the
    ;; idx forward and the record reads that remain walk the log forward.  A slot that
    ;; already records a premise at the wanted rank is a mark already on disk: the handle
    ;; joins the premise set and no record is paged.  That is every mark on an import, whose sink
    ;; wrote each record carrying its strength.  Otherwise the record is paged
    ;; (`premise-mark-read`), and a record whose `:strength` differs is re-stored; those
    ;; re-stores are one log write and one idx range per chunk.  A handle with no slot or
    ;; a tombstone neither joins the premise set nor is stored, which is the guard against a phantom
    ;; premise.
    (let [k (:sentexes kinds)]
      (doseq [chunk (partition-all default-batch (handle-order id->strength))]
        (let [have (into [] (keep (fn [id]
                                    (let [want (or (get id->strength id) :default)]
                                      (when-let [r (premise-mark-read k id (strength/rank-of want))]
                                        [id r want]))))
                         chunk)]
          (store-batch! k (into [] (keep (fn [[id r want]]
                                           (when-not (or (= ::marked r) (= want (:strength r)))
                                             [id (assoc r :strength want) true])))
                                have))
          (with-write (:lock k) (hs/live-add-all! premises (map first have))))))
    nil)
  (put-provenance-batch [_ entries]
    (doseq [chunk (partition-all default-batch entries)]
      (store-batch! (:provenance kinds) (mapv (fn [[id prov]] [id prov false]) chunk)))
    nil))

(defn- kind-fingerprint
  "The slot fingerprint of one kind `k`, as `{:count :max-handle :digest}`, plus `:epoch`
  when a wipe has minted one.  One sequential pass over its idx under the kind's lock,
  decoding nothing."
  [k epoch]
  (let [acc (fp/slot-accumulator)]
    (with-write (:lock k)
      (usable! k)
      (f/with-io-guard (:fault k) (:log-path k) false
        (f/scan-idx! (:idx k) (fn [id offset length _flags] (acc id offset length)))))
    (cond-> (acc) epoch (assoc :epoch epoch))))

(defn slot-fingerprint
  "What the sentexes idx currently says, as `{:count :max-handle :digest}`: the fingerprint a
  derived-index snapshot is validated against (`vaelii.impl.disk.index-snapshot`).  It is read
  off the slots in one sequential pass over a 24-byte-per-record file and decodes nothing.  It
  detects a record added, deleted or re-stored, and a wipe by the `:epoch` `clear-records!`
  mints.  It consults `usable!`, since a half-copied idx would describe no version of the
  records."
  [{:keys [kinds epoch]}]
  (kind-fingerprint (:sentexes kinds) @epoch))

(defn reasoning-fingerprint
  "The fingerprint a reasoning image is validated against, as
  `{:sentexes fp :justifications fp}`, each a `kind-fingerprint`.  Belief reads both kinds
  — the sentexes, whose slots also move when a premise mark re-stores one, and the
  justifications — so a change to either moves the fingerprint, where `slot-fingerprint`
  alone misses a justification stored over sentexes that did not change."
  [{:keys [kinds epoch]}]
  (let [e @epoch]
    {:sentexes       (kind-fingerprint (:sentexes kinds) e)
     :justifications (kind-fingerprint (:justifications kinds) e)}))

(extend-type DiskRecordStore
  p/ImageFingerprinting
  (index-fingerprint [store] (slot-fingerprint store))
  (belief-fingerprint [store] (reasoning-fingerprint store)))

(defn fsync
  "fsync every kind's log + idx, and rewrite the counters blob when the handle counter has
  moved since the last tick.

  The token dictionary is fsynced first, under the sentexes kind lock, so every record durable
  after the tick has durable tokens.  The counters blob is a whole-file rewrite and is written
  only when `synced-seq` differs from the counter; a skip costs no handle
  (`recover-next-id` takes the max of the blob and one past the highest slot).  This runs on
  the durability daemon's thread: the counter, the blob and `synced-seq` move together under
  `counters-lock`, which `clear-records!` also takes, and the counter is read inside it.  A
  failed fsync latches the fault (`:fsync-failed`, `files/with-io-guard`), because a retry may
  succeed over pages the kernel dropped.  A faulted store's tick is a no-op."
  [{:keys [dir kinds counter synced-seq dict counters-lock epoch fault]}]
  (when-not @fault
    (with-write (:lock (:sentexes kinds))
      (f/with-io-guard fault dir :fsync
        (when dict (dtok/fsync dict))
        (f/force! (:log (:sentexes kinds)) false)
        (f/force! (:idx (:sentexes kinds)) true)))
    (doseq [[kind k] kinds :when (not= kind :sentexes)]
      (with-write (:lock k)
        (f/with-io-guard fault (:log-path k) :fsync
          (f/force! (:log k) false)
          (f/force! (:idx k) true))))
    (locking counters-lock
      (let [want @counter]
        (when-not (= want @synced-seq)
          (f/with-io-guard fault dir :fsync
            (f/write-nippy-atomic! (counters-path dir) (counters-blob want @epoch)))
          (reset! synced-seq want)))))
  nil)

(defn- close-quietly!
  "Run one close step, logging rather than throwing.  A single file that will not close
  must not leave the rest of the store's handles open: `backend/close-dir!` releases
  the directory's OS lock whether this store closed cleanly or not, so a handle still
  open here is open for the life of the JVM over a directory another process may
  already have taken."
  [what thunk]
  (try (thunk)
       (catch Throwable t
         (trove/log! {:level :error
                      :msg (str "disk record store: closing " what " failed: "
                                (.getMessage t))}))))

(defn- release-handles!
  "Close every kind's log and idx and the token dictionary, each under its own guard
  (`close-quietly!`), so one handle that will not close leaves none of the others open."
  [kinds dict]
  (doseq [[kind k] kinds]
    (with-write (:lock k)
      (close-quietly! (str (clojure.core/name kind) ".log") #(f/close! (:log k)))
      (close-quietly! (str (clojure.core/name kind) ".idx") #(f/close! (:idx k)))))
  (when dict (close-quietly! "the token dictionary" #(dtok/close! dict))))

(defn close!
  "Flush durably, record the log lengths this session closed at, close every RAF, then remove
  the dirty marker (a clean shutdown).  The lengths are read after the fsync and written before
  anything closes, so the marker names what is durable and the next open skips a log's tail
  walk while its length agrees ([`f/log-tail-offset-from`](files.clj)).

  Every handle is released whatever the flush did, and only the dirty-marker removal is
  conditional.  A store whose fault latch is already set closes without throwing: it writes no
  clean marker, leaves the dirty one, releases every handle and logs at `:warn`.  A flush that
  fails here throws.  Afterwards the latch is `:closed` or faulted, so a later call is refused
  by name."
  [{:keys [dir kinds dict fault] :as store}]
  (if-let [prior @fault]
    (do (trove/log! {:level :warn :id ::closed-faulted
                     :msg (str "disk record store: closing " dir " after it stopped ("
                               (name (:reason prior)) ") — no clean marker, so the next"
                               " open walks it as an unclean shutdown")})
        (release-handles! kinds dict))
    (do
      (try
        (fsync store)
        (f/write-clean-marker! dir (into {} (map (fn [[kind k]]
                                                   [(clojure.core/name kind)
                                                    (with-write (:lock k)
                                                      (f/with-io-guard fault (:log-path k) false
                                                        (f/log-length (:log k))))]))
                                         kinds))
        (finally
          (f/latch-closed! fault dir)
          (release-handles! kinds dict)))
      (f/remove-dirty-marker! dir))))

(defn- recover-next-id
  "The counter to start `next-id` from: the max of the persisted `counters` blob and one
  past the highest slot id across the sentex + justification kinds (provenance shares
  their ids)."
  [counters kinds]
  (let [blob (long (:seq counters))
        hi   (long (max (f/max-slot-id (:idx (:sentexes kinds)))
                        (f/max-slot-id (:idx (:justifications kinds)))))]
    (max blob (inc hi) 1)))

(defn- rebuild-premises!
  "The premise set on open: the ids whose slot says premise, plus whatever the records say for
  the ids that have to be read.  A slot written before the premise bit existed is read once.  A
  tokenized store reads every live record, because that walk is the token-damage check: a
  frame naming a token the dictionary lacks is tombstoned, as `validate-idx-tail!` does for the
  idx.  The record wins wherever both speak.

  On a dirty open the walk covers every live record and the slot flags are reconciled against
  them (`f/reconcile-slot-flags!`), since the flags word is not crash-atomic; a disagreeing
  slot is rewritten once."
  [k root dict marked unsaid dirty?]
  (let [prem    marked
        n-said  (with-write (:lock k) (hs/live-tally marked))
        ;; A snapshot rather than the live set itself: the walk below tombstones a damaged
        ;; record through `kill!`, which drops that handle from the live set — an
        ;; iteration over the live bitmap would be walking a structure it is editing.
        ;; Under the lock like every other read of it, though this one runs on the opening
        ;; thread before the store is published: an invariant with an exception in it is
        ;; one nobody can check.
        walk    (if (or dict dirty?)
                  (with-write (:lock k) (hs/live-snapshot (:live-ids k)))
                  unsaid)
        damaged (volatile! {})
        fixed   (volatile! 0)]
    (with-open [r (progress/start ::read-premises "open: read the premise marks off the records"
                                  (count walk))]
      (doseq [id walk]
        (progress/tick! r)
        ;; only crash damage is repaired by tombstoning: a token the dictionary does not
        ;; hold or a body the codec cannot parse is the log's tail having outrun its
        ;; neighbours.  `:unknown-frame` is the opposite case — a build that cannot
        ;; decode a *valid* record — and rethrows, because a build that cannot read a
        ;; log must not delete it.
        (let [sx (try (fetch k id)
                      (catch clojure.lang.ExceptionInfo t
                        (let [why (:type (ex-data t))]
                          (when-not (#{:damaged-dictionary :malformed-record} why)
                            (throw t))
                          (vswap! damaged update why (fnil inc 0)))
                        (kill! k id)
                        nil))]
          (with-write (:lock k)
            (if (:strength sx) (hs/live-add! prem id) (hs/live-remove! prem id)))
          ;; a torn flags page across a crash may have left this slot's bit or rank stale;
          ;; the record is the truth, so rewrite the slot to it wherever they disagree
          (when (and dirty? sx)
            (let [premise? (some? (:strength sx))
                  rank     (if premise? (strength/rank-of (:strength sx)) 0)]
              (when (f/reconcile-slot-flags! (:idx k) id premise? rank)
                (vswap! fixed inc)))))))
    (when-let [n (:damaged-dictionary @damaged)]
      (trove/log! {:level :warn :id ::damaged-dictionary
                   :msg (str "disk records: " n " record(s) at " root " cite tokens the"
                             " dictionary does not hold — tombstoned")}))
    (when-let [n (:malformed-record @damaged)]
      (trove/log! {:level :warn :id ::malformed-record
                   :msg (str "disk records: " n " record(s) at " root " hold a tokenized"
                             " body the codec cannot parse — tombstoned")}))
    (when (pos? @fixed)
      (trove/log! {:level :warn :id ::flags-reconciled
                   :msg (str "disk records: reconciled " @fixed " slot flag(s) at " root
                             " against their records after an unclean shutdown"
                             " (torn flags page)")}))
    (trove/log! {:level :debug :id ::premise-set
                 :msg (str "disk records: premise set from " n-said
                           " annotated slot(s), " (count walk) " record(s) decoded")})
    (with-write (:lock k) (hs/live-optimize! prem))
    prem))

(defn open-record-store
  "Open a `DiskRecordStore` rooted at `dir/records`.  Recovers each kind, rebuilds the
  live-id sets, the premise set (sentexes with a non-nil :strength), and the id
  counter, and drops a dirty marker (removed on a clean `close!`).

  `:cache-capacity` sizes the per-kind hot-record LRU, defaulting to the
  `vaelii.disk.cache` property; 0 runs with no cache (what the fetch benchmark measures
  against, and the per-fetch cost with no cache hits).  `:tokenize?` writes sentex bodies
  as ids from a durable token dictionary rather than in full, defaulting to the
  `vaelii.disk.tokens` property; it is a *write* choice only — frames written either way
  always read."
  ([dir] (open-record-store dir nil))
  ([dir {:keys [cache-capacity tokenize?]
         :or   {cache-capacity (config/disk-cache-capacity)
                tokenize?      (config/disk-tokens?)}}]
   (let [root (str dir "/records")]
     (f/ensure-dir! root)
     (f/assert-format! root)
     ;; the dictionary is opened whenever the store *has* one, even with tokenized
     ;; writes off, because frames already written need it to decode
     (let [;; the marker says the last close was unclean; capture it once — it decides the
           ;; flags-word reconcile in `rebuild-premises!`, and is consumed (removed) below
           ;; before the open writes anything
           dirty?  (f/dirty-marker-present? root)
           _       (when dirty?
                     (trove/log! {:level :warn
                                  :msg (str "disk records: unclean shutdown at " root
                                            " — verifying on open")}))
           ;; read before the open writes anything, and drop it: the marker describes a
           ;; store nobody holds, so it can never survive into a session that grows a log
           clean   (when-not dirty? (f/read-clean-marker root))
           _       (f/remove-clean-marker! root)
           ;; Every open below takes file handles, and a throw part-way leaves the ones
           ;; already taken with nothing to close them: the caller gets an exception
           ;; rather than a store, so there is no value to close it *through*, and
           ;; `backend/store-for` releases the directory's lock on its way out — which
           ;; would hand the directory to another process with these logs still held.
           ;; So each open registers its own undo, and a failure runs them.
           closers (java.util.ArrayList.)
           ;; the store's one fault latch, shared by the three kinds (`usable!`)
           fault   (atom nil)]
       (try
         (let [dict   (when (or tokenize? (f/token-log-present? root))
                        (let [d (dtok/open-token-log root)]
                          (.add closers #(dtok/close! d))
                          d))
               codecs (codec/by-kind dict tokenize?)
               ;; a premise is a sentex whose :strength is non-nil, and its slot says so —
               ;; so the set rides the idx walk `open-kind` is already making, and only a
               ;; slot that does not say costs a record read (`rebuild-premises!`)
               marked (hs/live-handle-set)
               unsaid (java.util.ArrayList.)
               ;; runs inside `open-kind`'s idx walk, on the opening thread before the
               ;; store is published, so the premise set takes no lock here
               tap    (fn [id flags]
                        (if-some [premise? (f/slot-premise flags)]
                          (when premise? (hs/live-add! marked id))
                          (.add unsaid id)))
               kinds  (into {} (map (fn [n]
                                      (let [k (open-kind root n cache-capacity codecs
                                                         (get clean n)
                                                         (when (= n "sentexes") tap)
                                                         fault)]
                                        (.add closers #(f/close! (:log k)))
                                        (.add closers #(f/close! (:idx k)))
                                        [(keyword n) k])))
                            kind-names)
               counters (f/read-nippy-file (counters-path root) {:seq 1})
               counter  (atom (recover-next-id counters kinds))
               prem     (rebuild-premises! (:sentexes kinds) root dict marked unsaid dirty?)]
           (f/create-dirty-marker! root)
           (->DiskRecordStore root kinds counter (atom nil) prem dict (Object.)
                              (atom (:epoch counters)) fault (atom nil)))
         (catch Throwable t
           (doseq [c closers] (close-quietly! "a half-opened record store" c))
           (throw t)))))))

;; ---- compaction ---------------------------------------------------------

(defn- kind-dead-ratio
  "Dead-byte fraction of kind `k`: `1 - live-bytes / log-length`.  Reads the maintained
  counter and the log's length under the kind read lock, and no idx byte."
  ^double [k]
  (with-read (:lock k)
    (usable! k)
    (let [total (f/log-length (:log k))
          live  (long @(:live-bytes k))]
      (if (pos? total) (- 1.0 (/ (double live) (double total))) 0.0))))

(defn dead-ratio
  "Max dead-byte ratio across the kinds — the durability daemon's compaction trigger.
  O(kinds): each kind answers off its maintained `live-bytes` and its log's length."
  ^double [{:keys [kinds]}]
  (reduce max 0.0 (map kind-dead-ratio (vals kinds))))

(defn- open-compaction-handles!
  "The three handles a rewrite needs, or none of them.  Opened in a `let` the three
  throws would escape, a failure from the second or third leaks the ones already taken
  — a compaction that fails on a full disk is exactly when the process keeps running."
  [log-path log-tmp idx-tmp]
  (let [rlog (f/open-log-read log-path)]
    (try
      (let [tlog (f/open-log log-tmp)]
        (try
          [rlog tlog (f/open-idx idx-tmp)]
          (catch Throwable t (f/close! tlog) (throw t))))
      (catch Throwable t (f/close! rlog) (throw t)))))

(def ^:private abort-check-frames
  "How often the lock-free rewrite re-reads the abort flag: every Nth frame.  One atom
  deref against a read + thaw + re-freeze + write would be lost in the noise at every
  frame, but the loop is the one place in the store that runs to gigabytes and the
  stride adds no work to have.  Small enough that an abort is honoured in milliseconds,
  which is what a close waiting on it is entitled to."
  256)

(defonce ^{:doc "A thunk run once inside `compact-kind!`'s rewrite phase — after the
  snapshot, before the first frame is copied — with the kind map as its argument.  Nil
  in ordinary operation, and nothing in the engine ever sets it.

  It exists because the race window this store's lifecycle turns on is *between* the snapshot
  and the reconcile, and it is a race window a test cannot reach by sleeping: a rewrite of a
  test-sized log is over in microseconds, so \"close the directory while a rewrite is
  open\" reproduces by luck or not at all.  A barrier here holds the rewrite at exactly
  that point, so the handshake can be asserted rather than hoped for."}
  rewrite-barrier
  (atom nil))

(defn abort-compaction!
  "Tell an auto-compaction of `store` to abandon its rewrite: set `:aborted` on every kind,
  under the kind lock every other write of that atom takes.  Idempotent.  Called by
  `backend/close-dir!`.

  A rewrite still copying frames stops at its next check (`abort-check-frames`); one at the
  reconcile discards its temps.  A rewrite past its commit marker is not reachable: the
  reconcile holds the kind lock until the install is done, so an abort lands before the read
  or after the install, and the next open would finish it anyway (`recover-compaction!`).  The
  flag is written whether or not a rewrite is running, so an abort that lands between the
  executor's registry check and the compaction's snapshot sticks, and the snapshot carries an
  existing flag across.  `clear-records!` keeps the `when c` form, since its store goes on
  being used.  It does not wait; `durability/await-compaction-quiescent!` does."
  [{:keys [kinds]}]
  (doseq [k (vals kinds)]
    (with-write (:lock k)
      (swap! (:compacting k) #(assoc (or % {:touched #{}}) :aborted true))))
  nil)

(defn- compact-kind!
  "Rewrite kind `k`'s log with only its live frames, preserving slot ids, crash-safely and
  copy-on-write: the O(live) rewrite runs without the kind lock, reading the log's immutable
  region through a private read handle, and the lock is held for two brackets.

  - snapshot (front): capture the live slots and `cutoff` (log length) and arm delta tracking
    (`:compacting`), so appends past `cutoff` and slot mutations are recorded.
  - reconcile + swap (end): fold the touched ids into the temp, preserve the high-water mark,
    fsync, write the commit marker, replay the temps over the originals, drop them.

  The marker is written only after every read the reconcile needs has succeeded, so a crash
  before it leaves the originals authoritative and one after it replays the fsynced temps.  A
  `clear-records!` or `close-dir!` mid-rewrite sets `:aborted` (`abort-compaction!`).  A slot
  whose frame the log cannot give back is tombstoned in the temp and removed from the live
  set, premise set and record cache once the install lands, with a `:warn` per handle."
  [k premises]
  (let [{:keys [temps marker]} (f/compact-temp-paths (:log-path k) (:idx-path k))
        [[_ log-tmp] [_ idx-tmp]] temps
        ;; snapshot (brief lock) — the live slots as of now; everything so far sits at
        ;; offset < cutoff (immutable), so the rewrite can read it lock-free.
        snapshot (with-write (:lock k)
                   (usable! k)
                   (let [live (java.util.ArrayList.)]
                     (f/scan-idx! (:idx k)
                                  (fn [id off len flags] (.add live [id off len flags])))
                     ;; `swap!`, not a `reset!` to false: an `abort-compaction!` that
                     ;; got the kind lock before this did found nothing to mark and
                     ;; left the flag standing for whoever started next — which is this
                     ;; rewrite.  Clearing it here would spend a close's whole join on
                     ;; a rewrite that was told not to bother.
                     (swap! (:compacting k)
                            (fn [c] {:touched #{} :aborted (boolean (:aborted c))}))
                     (vec live)))
        [rlog tlog tidx] (open-compaction-handles! (:log-path k) log-tmp idx-tmp)
        ;; the commit point, read by the failure path — see its comment
        committed? (volatile! false)
        ;; Slots whose frame the log could not give back — a tail a recovery truncated
        ;; under a slot that survived it.  They are tombstoned in the temp rather than
        ;; carried across: re-freezing the nil would put the handle back as a *live*
        ;; record whose fetch is nil, an id `sentex-ids` names and `get-sentex` answers
        ;; nothing for, and every walk over the ids trips on that one.
        lost       (volatile! #{})
        drop-lost! (fn []
                     ;; only where the install landed, since only then is the tombstoned
                     ;; idx the one the store is reading; the resident sets follow it.
                     ;;
                     ;; Under the kind lock, which the reconcile below already holds
                     ;; where it calls this and the retry path does not: this runs on the
                     ;; compaction executor's thread beside the writer, so it is the
                     ;; resident half of an idx write that was itself locked.  Reentrant,
                     ;; so the call from inside the reconcile costs a recursion count.
                     (when (seq @lost)
                       (with-write (:lock k)
                         (hs/live-remove-all! (:live-ids k) @lost)
                         (when premises (hs/live-remove-all! premises @lost))
                         (when-let [^java.util.Map c (:cache k)]
                           (doseq [id @lost] (.remove c id))))))
        drop-slot! (fn [tidx id]
                     (vswap! lost conj id)
                     (trove/log! {:level :warn :id ::unreadable-frame
                                  :msg (str "disk record store: compacting "
                                            (:log-path k) " found no frame for handle "
                                            id " — dropping the handle rather than "
                                            "storing it empty")})
                     (f/tombstone-slot! tidx id))]
    (try
      ;; the expensive rewrite — no lock held; reads the immutable region via `rlog`.
      ;; The flags are carried across from the source slot rather than re-derived: a
      ;; frame moves here without being decoded, so the slot is the only thing that
      ;; knows whether its record is a premise.  Losing them would not lose a premise
      ;; — an unannotated slot is answered from its record — but it would quietly put
      ;; every later open back to decoding the whole store.
      ;; `read-record-sized`, because the snapshot tuple already carries the payload
      ;; length: `read-record` would read the 4-byte header back off the log to learn a
      ;; number the slot recorded, doubling the positional reads of a walk that is
      ;; O(live records) by construction.
      (when-let [barrier @rewrite-barrier] (barrier k))
      ;; A `loop` rather than the `doseq` this was, for the abort check: a close of the
      ;; directory (`abort-compaction!`) has to be able to stop an O(bytes) copy without
      ;; waiting it out, and the reconcile below reads the same flag and discards the
      ;; temps — so stopping here needs no unwinding of its own, and no sentinel throw
      ;; the caller would have to tell apart from a real failure.
      (with-open [r (progress/start ::copy-records "compact: copy the live records"
                                    (count snapshot))]
        (loop [todo (seq snapshot) n 0]
          (when (and todo
                     (or (pos? (rem n abort-check-frames))
                         (not (:aborted @(:compacting k)))))
            (let [[id off len flags] (first todo)]
              (if-let [rec (f/read-record-sized rlog off len)]
                (let [[noff plen] (f/append-record-sized! tlog rec)]
                  (f/write-slot! tidx id noff plen flags 0))
                (drop-slot! tidx id))
              (progress/tick! r)
              (recur (next todo) (inc n))))))
      (f/close! rlog)
      ;; reconcile + swap (brief lock)
      (with-write (:lock k)
        (let [{:keys [touched aborted]} @(:compacting k)]
          (if aborted
            (do (f/close! tlog) (f/close! tidx)
                (f/delete-compact-temps! marker temps)
                ;; said out loud, because from the outside an abandoned rewrite and a
                ;; rewrite that found nothing to reclaim look identical — the log is
                ;; the same size either way
                (trove/log! {:level :info :id ::compaction-aborted
                             :msg (str "disk record store: the compaction of "
                                       (:log-path k) " was abandoned (the store was"
                                       " wiped or closed under it) — the originals"
                                       " stand and the temps are gone")}))
            (do
              ;; fold in everything stored/killed during the rewrite: copy the current
              ;; frame of a still-live id, tombstone one that is gone.
              (doseq [id touched]
                (let [slot (f/read-slot (:idx k) id)]
                  (if (and slot (not (:tombstone? slot)))
                    ;; the slot is in hand, so its length is too — one read, not two
                    (if-let [rec (f/read-record-sized (:log k) (:offset slot)
                                                      (:length slot))]
                      (let [[noff plen] (f/append-record-sized! tlog rec)]
                        (f/write-slot! tidx id noff plen (:flags slot) 0))
                      (drop-slot! tidx id))
                    (f/tombstone-slot! tidx id))))
              ;; preserve the high-water mark so `next-id` (1 + max-slot) never reissues
              ;; a handle: if the highest live-idx slot (a deleted id keeps its slot) is
              ;; not addressable in the temp, tombstone it there.
              (let [final-max (f/max-slot-id (:idx k))]
                (when (> final-max (f/max-slot-id tidx))
                  (f/tombstone-slot! tidx final-max)))
              (f/force! tlog false) (f/force! tidx true)
              (f/close! tlog) (f/close! tidx)
              (f/write-commit-marker! marker {:log (:log-path k)})
              (vreset! committed? true)
              (f/replay-temp-onto-raf! (:log k) log-tmp)
              (f/replay-temp-onto-raf! (:idx k) idx-tmp)
              (reset! (:live-bytes k) (idx-live-bytes (:idx k)))
              (f/delete-compact-temps! marker temps)
              (drop-lost!)))
          (reset! (:compacting k) nil)))
      (catch Throwable t
        ;; A failure **before the marker** takes the temps with it.  No marker was
        ;; written, so the originals stay authoritative and a *later open* would drop
        ;; them via `recover-compaction!` — but the next compaction **in this
        ;; session** never goes through recovery, and `f/open-log` seeks to `.length`
        ;; while `f/open-idx` does not truncate.  It would open these and append, and the
        ;; reconcile would replay a temp holding this run's slots over the live index,
        ;; resurrecting records deleted in between.
        ;; quietly: the two temps have to be shut before the branch below deletes or
        ;; replays them, and a close that threw here would replace `t` — the cause a
        ;; caller needs — with an IOException about a temp file, and skip the recovery
        ;; the branch exists to make.
        (close-quietly! "the compaction temp log" #(f/close! tlog))
        (close-quietly! "the compaction temp idx" #(f/close! tidx))
        (if-not @committed?
          (do (f/delete-compact-temps! marker temps)
              (throw t))
          ;; A failure **after** the marker leaves the temps: it is the commit point,
          ;; the fsynced temps are the truth, and `replay-temp-onto-raf!` truncates
          ;; before copying — so the live files may now be half-copied while the
          ;; session keeps running over them.  Retry the install once, the same replay
          ;; an open would make off the marker.  If that fails too, the kind is flipped
          ;; into `failed`: every read and write refuses with `:compaction-failed`
          ;; rather than answering off a torn log, and the next open finishes the
          ;; install.
          (let [again (try (with-write (:lock k)
                             (f/replay-temp-onto-raf! (:log k) log-tmp)
                             (f/replay-temp-onto-raf! (:idx k) idx-tmp)
                             (reset! (:live-bytes k) (idx-live-bytes (:idx k)))
                             (f/delete-compact-temps! marker temps))
                           nil
                           (catch Throwable t2 (.addSuppressed t2 t) t2))]
            (if again
              ;; the flag under the lock every reader of it takes (`usable!`), so a read
              ;; already inside the monitor cannot be answered off half-copied files by
              ;; a flag this thread was in the middle of setting
              (do (with-write (:lock k) (reset! (:failed k) again))
                  (trove/log! {:level :error :id ::compaction-failed
                               :msg (str "disk record store: compaction of " (:log-path k)
                                         " failed after its commit point and the retry"
                                         " failed too — the store refuses reads and writes"
                                         " until it is reopened")
                               :error again})
                  (throw again))
              (do (drop-lost!)
                  (trove/log! {:level :warn :id ::compaction-retried
                               :msg (str "disk record store: installing the compacted "
                                         (:log-path k) " failed after its commit point"
                                         " and succeeded on retry")
                               :error t}))))))
      (finally
        ;; Stop delta tracking even if the rewrite threw — under the kind lock, which is
        ;; where every other write of this atom happens (`track-touched` from a store or
        ;; a kill, `clear-records!`'s abort flag, the reconcile's own reset).  Cleared
        ;; outside it, a writer's `track-touched` can read a live compaction and fold an
        ;; id into a `:touched` set this thread is discarding, and the id is one the
        ;; reconcile never copied into the temp.
        (with-write (:lock k) (reset! (:compacting k) nil))
        ;; and give the three handles back one at a time, quietly: a close that threw
        ;; here would take the handles after it with it — leaving RAFs open over a
        ;; directory `close-dir!` unlocks regardless — and would mask whatever the body
        ;; was throwing, which is the thing the caller has to read.  Each is already
        ;; closed on the paths that got that far; `RandomAccessFile.close` is idempotent.
        (close-quietly! "the compaction read handle" #(f/close! rlog))
        (close-quietly! "the compaction temp log"    #(f/close! tlog))
        (close-quietly! "the compaction temp idx"    #(f/close! tidx))))))

(defn compact!
  "Compact every kind's log (reclaim the dead frames left by deletes and premise
  re-stores).  Preserves every live record and its handle — except a handle whose frame
  the log cannot give back, which is dropped rather than re-stored empty
  (`compact-kind!`)."
  [{:keys [kinds premises]}]
  ;; A lost frame drops its handle from the premise set only in the sentexes kind.  A
  ;; provenance handle is its sentex's handle, so a lost provenance frame must leave that
  ;; sentex's premise mark standing.
  (doseq [[n k] kinds] (compact-kind! k (when (= n :sentexes) premises))))

;; ---- what a paged store holds, declared ---------------------------------
;;
;; The one cache here an operator sizes rather than inherits (`vaelii.disk.cache`), and
;; the only one whose entries are a KB's own records rather than something derived from
;; them.  Cleared with the store, never by hand: dropping it costs the next read a
;; positional read and a thaw apiece, and the record it holds is the same value the log
;; holds — so there is no derivation to re-measure, only latency to re-pay.

(caches/register-cache
 {:cache    :hot-records
  :label    "Hot records"
  :scope    :kb
  :unit     "records"
  :limit    nil
  :counters nil
  :note     (str "Records already fetched off disk, held per kind in an LRU sized by "
                 "vaelii.disk.cache — so the limit is per kind and the count is across "
                 "them. Blank for a KB whose records are in memory: there is nothing to "
                 "page, and so nothing to hold.")
  :read     (fn [kb]
              (when-let [kinds (:kinds (:records kb))]
                {:entries (reduce + 0 (keep (fn [k]
                                              (some-> ^java.util.Map (:cache k) .size))
                                            (vals kinds)))}))})

(caches/register-derived
 {:id :R10 :label "Hot records" :cache :hot-records :kind :cache :keyed-by :handle
  :holds-content? false
  :reads [:records]
  :retired-by {:stored :K :removed :K :respelled :K :cleared :W}
  :computed :read :imaged? false
  :value (fn [kb] (when-let [ks (:kinds (:records kb))]
                    (into {} (keep (fn [[kind k]]
                                     (when-let [^java.util.Map c (:cache k)]
                                       [kind (locking c (into {} c))])))
                          ks)))
  :note "per kind, an access-ordered LRU of decoded records; disk stores only"})
