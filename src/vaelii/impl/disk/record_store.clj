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

  That live set is a **compressed bitmap** (`vaelii.impl.roster`'s `LiveRoster`), not a
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
  pointing inside the log is indistinguishable from a thaw failure on that handle rather than being caught
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
    from them: `live-ids`, the hot-record cache, `compacting` and `failed`.  A store, a
    kill, a batch and the compactor's reconcile each take it once and do both halves
    inside it, so an id is never live to a reader while its slot says tombstone, and the
    compaction delta set is never cleared under a writer folding an id into it.

    It covers `live-ids` on the **read** side too, which the other three do not need: the
    roster is a bitmap mutated in place, so a tally or an enumeration taken beside a
    concurrent `addLong` reads a structure mid-edit.  A read that hands the set onward
    takes a `roster/live-snapshot` inside the lock and lets go of it — the copy costs the
    bitmap's size, not the corpus's, which is what makes holding the writer's monitor for
    an enumeration affordable at all.
  - **`counters-lock`** covers the three that move together and belong to no kind: the
    handle `counter`, the `counters.nippy` blob, and `synced-seq` — read and written by
    `fsync` on the daemon's thread and by `clear-records!` on the writer's.  Its own
    monitor rather than a kind's, because a whole-file blob rewrite held inside a kind
    lock would put a record append behind it every tick that minted a handle.

  `premises` is a `LiveRoster` too, and sits under the **sentexes** kind lock for reads
  and writes alike, because a premise is a sentex handle.  It is not folded into
  `store!`'s acquisition: a premise joins the roster after its record lands, in a second
  acquisition, so a failed write leaves no handle in `premise-ids` whose `get-sentex` is
  nil.  The compactor's `drop-lost!` removes from it only when compacting the sentexes
  kind, under the lock it already holds."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.codec :as codec]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.roster :as roster]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.store :as store-types]))

(def ^:private kind-names ["sentexes" "justifications" "provenance"])

;; `vaelii.disk.tokens` and `vaelii.disk.cache` are read at the store's **open**
;; (`open-record-store`), not here.  A `def` reading a property is a read at namespace
;; load, and a load-time refusal of `vaelii.disk.cache=64k` reports as a namespace that
;; will not load — the typo delivered as a broken build.  `config` owns both domains.

;; ---- the hot-record cache ----------------------------------------------
;; A record fetch is two positional reads plus a nippy thaw (~3 µs warm), and a real
;; query stream is skewed — the same predicates and individuals are fetched over and
;; over.  A bounded LRU in front of the read serves 64% of a zipfian stream at 1k
;; entries and 79% at 10k (`lein bench-records`), and a hit costs a map lookup.
;;
;; Correct because a record is an immutable value: the only ways the record at an id can
;; change are `store!` (which replaces the cached value), `kill!` (which drops it), and
;; `clear-records!` (which empties the cache).  Compaction rewrites frames but preserves
;; every id's content, so it needs no invalidation.
;;
;; A bulk sweep — `export!`, `reindex`, the `recover` a fork runs over a live base —
;; fetches every record through here and so rewrites the recency order.  It promotes like
;; any other read, because what that costs is bounded by the capacity: refilling the
;; working set is capped at `cap` misses while the sweep pays one read per record, so the
;; next queries lose at most `cap / records` of the sweep's own cost.  Measured at 22 ms
;; against a 2.6 s sweep of 800k records (`docs/storage.md`, "A bulk sweep claims
;; recency").

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
;; upgrade and deadlocks, so `fetch`'s body never writes.
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
  "Refuse an access to kind `k` once a compaction has failed **past its commit point**
  (`compact-kind!`): the live log and idx may be half-copied, so a read off them is
  garbage and a write into them is lost.  `failed` holds the failure; the next open
  finishes the install off the commit marker, and until then the store says so rather
  than answering.

  **Who consults it, and who deliberately does not.**  Every access to the *files* does —
  `store!`, `fetch`, `kill!`, `premise-strength`'s slot read — and so do the two that
  read the idx and act on what it says: `slot-fingerprint`, whose answer is a claim about
  the record set that a derived image is then validated against, and `kind-dead-ratio` /
  `compact-kind!`, which would otherwise rewrite a log from a half-copied idx and lose
  every record the copy had not reached.  A refusal from the dead-ratio read is what the
  durability daemon already treats as *do not compact* (it scores a throwing read 0.0).

  The rest do not, and each is fail-safe for its own reason rather than by oversight:

  - `sentex-ids` / `justification-ids` / `premise-ids` answer from the in-memory live-id
    sets, which the file state cannot corrupt.  A caller that then fetches one of those
    handles is refused there, which is where the refusal belongs — the enumeration is
    honest about what the store holds, and only the bytes are in doubt.
  - `fsync` forces bytes already written.  Nothing is read and nothing decided, the
    commit marker and the fsynced temps are what the next open repairs from either way,
    and `close!` runs it — so refusing would leave file handles open on the directory
    `backend/close-dir!` is trying to release, trading a harmless flush for a leak.
  - `clear-records!` is the one path that must proceed *because* the kind failed: a wipe
    supersedes the pending install, drops the marker and the temps under the same lock,
    and clears `failed`.  Consulting this would leave a store no call could repair."
  [k]
  (when-let [t @(:failed k)]
    (throw (ex-info (str "disk record store: a compaction of " (:log-path k)
                         " failed after its commit point — the live files are unusable"
                         " until the store is reopened, which finishes the install off"
                         " the commit marker")
                    {:type :compaction-failed :log (:log-path k)}
                    t))))

(defn- open-kind
  "Open (recovering) the log/idx pair `dir/<name>.{log,idx}` and build its live-id set.

  `clean-length` is what the last clean close recorded for this log, if anything; a log
  still that length has no torn tail and skips the walk.  `validate-idx-tail!` runs
  either way — a skipped scan is not a skipped validation.

  `slot-tap` (optional) is called with `[id flags]` for every live slot, so a caller
  that wants what the slots say rides this walk rather than making a second one."
  [dir name cache-cap codecs clean-length slot-tap]
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
        ;; the roster is filled straight off the scan, which walks slots by position and
        ;; so hands ids up in ascending order — the one order Roaring's run containers
        ;; want, and `live-optimize!` folds the runs once the walk is done.  Nothing
        ;; intermediate is built, so an open's peak is the roster itself.
        (let [live  (roster/live-roster)
              {:keys [enc dec]} (codecs name)]
          (f/scan-idx! idx (fn [id _ _ flags]
                             (roster/live-add! live id)
                             (when slot-tap (slot-tap id flags))))
          (roster/live-optimize! live)
          (store-types/->Kind log idx (java.util.concurrent.locks.ReentrantReadWriteLock.) live log-path idx-path (atom nil) (atom nil)
                              (when (pos? cache-cap) (lru cache-cap)) enc dec))
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
  "Append `rec` to kind `k`, point slot `id` at the new frame, and mark `id` live.
  Returns `id`.  Holds the kind lock.

  `premise?` is written into the slot's flags so the next open can read the premise set
  off the idx walk instead of decoding every record (`f/premise-flags`).  Only the
  sentexes kind has premises; the other two say so, which is true of them.

  **The resident half is inside the lock with the file half**, and it is the same
  acquisition rather than a second one: the live set and the record cache are claims
  about what the idx says, and a reader on another thread — the durability daemon, a
  compaction, a query beside the writer — that lands between the two reads a store
  whose files and whose resident state disagree.  What that costs is a `conj` and a map
  put inside a monitor that was already held for two file writes."
  ([k id rec] (store! k id rec false))
  ([k id rec premise?]
   (with-write (:lock k)
     (usable! k)
     (let [[off plen] (f/append-record-sized! (:log k) ((:enc k) rec))]
       ;; the premise's strength rides the slot too (bits 2..3), so `premise-strength`
       ;; reads it off the idx the open walk already makes rather than paging the record
       (f/write-slot! (:idx k) id off plen
                      (f/premise-flags premise? (strength/rank-of (:strength rec))) 0))
     (track-touched k id)
     (roster/live-add! (:live-ids k) id)
     ;; a just-written record is hot, and this is also what keeps the cache honest when a
     ;; re-store (mark-premise) replaces an id's record with a different value
     (when-let [^java.util.Map c (:cache k)] (.put c id rec)))
   id))

(defn- store-batch!
  "Append every record of `batch` to kind `k` and point its slot at the frame — **one log
  write and one idx write per run of consecutive handles**, where `store!` is two
  syscalls per record on an unbuffered `RandomAccessFile`.  `batch` is `[id rec
  premise?]` triples; the lock is taken once for the whole batch.

  The written records are **evicted** from the hot cache rather than installed in it.
  A bulk load is a stream nobody is reading back, so filling the LRU with its tail
  evicts what a later query wants; and the eviction is what keeps a re-store honest,
  which is the half of `store!`'s cache put that is about correctness rather than speed.

  All-or-nothing on the log (`f/append-records-sized!`), so a batch is never half a frame
  on disk.  It is **not** a transaction across the two files: the write ordering is the
  same one a single `store!` relies on — the frames land, then the slots point at them —
  so a crash between them leaves frames no slot names, which is what the log already
  tolerates."
  [k batch]
  (when (seq batch)
    (with-write (:lock k)
      (usable! k)
      (let [offs (f/append-records-sized! (:log k) (map (fn [[_ rec _]] ((:enc k) rec)) batch))]
        (f/write-slots! (:idx k)
                        (map (fn [[id rec premise?] [off plen]]
                               [id off plen
                                (f/premise-flags premise? (strength/rank-of (:strength rec)))
                                0])
                             batch offs)))
      (doseq [[id] batch] (track-touched k id))
      ;; the resident half under the same acquisition, for `store!`'s reason
      (roster/live-add-all! (:live-ids k) (map first batch))
      (when-let [^java.util.Map c (:cache k)]
        (doseq [[id] batch] (.remove c id)))))
  nil)

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
          ;; the **read** lock is kept even though both reads are positional (they neither
          ;; use nor move the shared pointer): it is what serializes a read against a
          ;; concurrent append + slot rewrite.  Two positional reads are safe against each
          ;; other, so this is the read lock rather than the write one — concurrent fetches
          ;; (a bulk `export!`/`reindex`/`recover` sweep across cores) run in parallel, and
          ;; only a writer (`store!`/`kill!`/compaction, all on the write lock) excludes them.
          (let [rec (with-read (:lock k)
                      (when-let [slot (f/read-slot (:idx k) id)]
                        (when-not (:tombstone? slot)
                          (some-> (f/read-record-sized (:log k) (:offset slot) (:length slot))
                                  ((:dec k))))))]
            (when (and c rec) (.put c id rec))
            rec)))))

(defn- kill!
  "Tombstone handle `id` in kind `k` and drop it from the live set (a no-op when it
  was never live).  The tombstone and the two resident drops are one acquisition, for
  `store!`'s reason: an id that is live to a reader and tombstoned on disk is a handle
  `sentex-ids` names and `get-sentex` answers nothing for.

  The liveness test is **inside** the lock with the drop it guards, because the roster it
  reads is a bitmap mutated in place: a test outside would read one beside a concurrent
  append.  It is the same acquisition either way — the test only ever decided whether to
  take one."
  [k id]
  (with-write (:lock k)
    (when (roster/live-has? (:live-ids k) id)
      (usable! k)
      (f/tombstone-slot! (:idx k) id)
      (track-touched k id)
      (roster/live-remove! (:live-ids k) id)
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
  rosters a premise from the record's own `:strength` whatever a caller does next — the
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
        ;; The premise roster is joined **after** the write, which is the order
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
                             (with-write (:lock k) (roster/live-add-all! premises ps)))))
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

;; `synced-seq` is what the `counters.nippy` blob was last left holding, so `fsync` can
;; tell an idle tick from one with a handle to persist (its docstring says why that
;; matters).  nil until the first tick writes it, which is what makes that first tick
;; unconditional: the blob on disk is whatever the previous session left, and only a write
;; establishes what it says now.
;;
;; `counters-lock` is the monitor over the three that move together — the counter, the
;; `counters.nippy` blob and `synced-seq`.  A monitor of its own rather than a kind's,
;; because none of the three is a claim about a kind's *files*, and holding a kind lock
;; across a whole-file blob rewrite would put a record append behind it: `fsync` runs on
;; the durability daemon's thread and `clear-records!` on the writer's, so the pair that
;; needs serializing is those two and nothing else on the store's hot path.
;;
;; `epoch` holds the store's clear epoch: nil for a store no `clear-records!` has emptied,
;; else the random long the latest wipe minted.  The counters blob carries it, and both
;; slot fingerprints fold it in (`slot-fingerprint`, `reasoning-fingerprint`).
(defrecord DiskRecordStore [dir kinds counter synced-seq premises dict counters-lock epoch]
  p/RecordStore
  (next-id [_] (long (dec (swap! counter inc))))

  (put-sentex [this sentex]
    (let [id  (clear-counter! counter (or (:id sentex) (p/next-id this)))
          rec (assoc sentex :id id)]
      (store! (:sentexes kinds) id rec (some? (:strength rec)))
      (when (:strength rec)
        (with-write (:lock (:sentexes kinds)) (roster/live-add! premises id)))
      id))
  ;; Tallied by kind (`vaelii.impl.profile`), the same call sites the RAM store carries, and
  ;; this is the store the number is *about*: a miss here is a positional slot read, a
  ;; positional frame read and a nippy thaw, where an index read is a map lookup.  On the
  ;; protocol method rather than inside `fetch`, so the two stores count the same events —
  ;; `mark-premise` below re-fetches where the RAM store reaches into its state map.
  (get-sentex [_ id] (prof/record-fetch :sentex) (fetch (:sentexes kinds) id))
  (delete-sentex! [_ id]
    (kill! (:sentexes kinds) id)
    (with-write (:lock (:sentexes kinds)) (roster/live-remove! premises id))
    (kill! (:provenance kinds) id)          ; provenance dies with its record
    nil)

  (put-justification [this justification]
    (let [id (clear-counter! counter (or (:id justification) (p/next-id this)))]
      (store! (:justifications kinds) id (assoc justification :id id))
      id))
  (get-justification [_ id] (prof/record-fetch :justification) (fetch (:justifications kinds) id))
  (delete-justification! [_ id]
    (kill! (:justifications kinds) id)
    (kill! (:provenance kinds) id)
    nil)

  (put-provenance    [_ id prov] (store! (:provenance kinds) id prov) prov)
  (get-provenance    [_ id]      (prof/record-fetch :provenance) (fetch (:provenance kinds) id))
  (delete-provenance! [_ id]     (kill! (:provenance kinds) id) nil)

  ;; Each enumeration answers the snapshot itself, an immutable `HandleRoster` taken under
  ;; the lock.  The snapshot is a bitmap copy and costs the roster's size, not the extent.
  ;; The protocol promises a `java.util.Set` answering membership, iteration, cardinality
  ;; and ordering, which the roster answers; a caller wanting `conj` converts with `set`.
  (sentex-ids    [_] (with-write (:lock (:sentexes kinds))
                       (roster/live-snapshot (:live-ids (:sentexes kinds)))))
  (justification-ids [_] (with-write (:lock (:justifications kinds))
                           (roster/live-snapshot (:live-ids (:justifications kinds)))))

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
        (with-write (:lock k) (roster/live-add! premises id))))
    nil)
  (unmark-premise! [_ id]
    ;; the same guard as mark-premise, pointing the other way: a derived record's
    ;; :strength is already nil, and re-storing it would append a frame whose only
    ;; fate is the tombstone the retraction writes right after
    (let [k (:sentexes kinds)]
      (when-let [sx (fetch k id)]
        (when (some? (:strength sx))
          (store! k id (assoc sx :strength nil) false)))
      (with-write (:lock k) (roster/live-remove! premises id)))
    nil)
  ;; the snapshot under the lock, answered as it is, as `sentex-ids` does
  (premise-ids      [_] (with-write (:lock (:sentexes kinds))
                          (roster/live-snapshot premises)))
  (premise-strength [_ id]
    ;; read the rank off the slot (bits 2..3) — one positional 24-byte read, no frame and
    ;; no thaw.  A rank-0 slot carries no strength (a non-premise, or a slot older than the
    ;; strength bits), so it falls back to the record, exactly as the premise bit does for a
    ;; slot that predates it; any write upgrades the slot and the fetch never runs again.
    ;;
    ;; The rank is a cache over the record like the premise bit beside it (`rebuild-premises!`),
    ;; and it shares that bit's flags-word residual: a torn flags page across a crash can leave a
    ;; stale rank on a non-tokenized store until the handle's next write (a tokenized open reads
    ;; every record; a `reindex`/re-mark repairs it).  The record stays the durable truth.
    ;;
    ;; Guard the id as `fetch` does — a non-integer informant or a negative id is the nil the
    ;; memory store answers, not a `read-slot` coercion throw; `premise-strength` must not
    ;; depend on the backend for a key it does not hold.
    (let [k (:sentexes kinds)]
      (if (and (integer? id) (not (neg? (long id))))
        (if-let [slot (with-write (:lock k) (usable! k) (f/read-slot (:idx k) id))]
          (let [rank (f/slot-strength (:flags slot))]
            (if (pos? rank)
              (strength/class-of-rank rank)
              (or (:strength (fetch k id)) :default)))
          :default)
        :default)))

  (clear-records! [_]
    ;; The counter, the blob, the stamp and the epoch are one step, under the monitor
    ;; `fsync` takes for the first three.  A daemon tick that read the counter before the
    ;; wipe and wrote the blob after it would leave a wiped store stamped with the pre-wipe
    ;; high-water mark, and `synced-seq` agreeing — so the next open starts issuing handles
    ;; from a number no record in the store has ever reached.
    ;;
    ;; The wipe truncates every log, so a record written after it lands at an offset a
    ;; removed record held, and one of the same byte length reproduces that record's slot
    ;; exactly.  A new epoch separates the two record sets in a slot fingerprint.  The blob
    ;; carrying it is written before the truncation, so a crash between the two leaves the
    ;; old records under the new epoch, which declines an image, and never the new records
    ;; under the old one.  A counter of 1 beside the old records reissues no handle, because
    ;; `recover-next-id` starts past the highest slot.
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
        (roster/live-clear! (:live-ids k))
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
    (with-write (:lock (:sentexes kinds)) (roster/live-clear! premises))
    ;; the dictionary goes with them: no frame survives to hold an id, and keeping the
    ;; ids would leave a wiped store carrying its predecessor's whole vocabulary
    (when dict (dtok/clear! dict))
    nil)

  ;; Both live-id rosters and the premise set are resident already (the namespace
  ;; docstring says why), so a tally is a read of one of them rather than the `set` copy
  ;; the enumeration takes.  On a bitmap it is the cardinality it already tracks and the
  ;; lowest set bit — neither walks the roster, so all four are O(1) under a lock the
  ;; writer holds only for two file writes.
  p/Tallying
  (sentex-tally        [_] (with-write (:lock (:sentexes kinds))
                             (roster/live-tally (:live-ids (:sentexes kinds)))))
  (justification-tally [_] (with-write (:lock (:justifications kinds))
                             (roster/live-tally (:live-ids (:justifications kinds)))))
  (a-sentex-id         [_] (with-write (:lock (:sentexes kinds))
                             (roster/live-least (:live-ids (:sentexes kinds)))))
  (a-justification-id  [_] (with-write (:lock (:justifications kinds))
                             (roster/live-least (:live-ids (:justifications kinds)))))
  (a-premise-id        [_] (with-write (:lock (:sentexes kinds))
                             (roster/live-least premises)))

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
    ;; The fetch per handle stays — the guard against a phantom premise is that the
    ;; record exists, and only the record says what strength it already carries.  What
    ;; batches is the *writing*: the marks that actually change a record become one log
    ;; write and one idx range instead of a re-store apiece.  Most of them change nothing
    ;; on an import, because the records were written carrying their strength.
    (let [k (:sentexes kinds)]
      (doseq [chunk (partition-all default-batch id->strength)]
        (let [have (into [] (keep (fn [[id strength]]
                                    (when-let [sx (fetch k id)] [id sx (or strength :default)])))
                         chunk)]
          (store-batch! k (into [] (keep (fn [[id sx want]]
                                           (when-not (= want (:strength sx))
                                             [id (assoc sx :strength want) true])))
                                have))
          (with-write (:lock k) (roster/live-add-all! premises (map first have))))))
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
      (f/scan-idx! (:idx k) (fn [id offset length _flags] (acc id offset length))))
    (cond-> (acc) epoch (assoc :epoch epoch))))

(defn slot-fingerprint
  "What the sentexes idx currently says, as `{:count :max-handle :digest}` — the stamp a
  derived-index snapshot is validated against (`vaelii.impl.disk.index-snapshot`).

  It is read off the **slots**, so it costs one sequential pass over a 24-byte-per-record
  file and decodes nothing.  That is the whole point: an image exists so an open reads
  bytes rather than records, and validating it against a content digest (walking every
  record through `fingerprint/accumulator`) would put
  all of them back on the open path.  What it detects is every way the record set can
  change under a snapshot — a record added, deleted, or re-stored (a re-store appends a
  new frame, so the handle's offset moves) — and a wipe, whose records reuse the
  truncated offsets and so are told apart by the `:epoch` `clear-records!` mints.

  It consults `usable!`: this is a *claim about the record set*, and a half-copied idx
  would answer with a fingerprint describing no version of the records that ever existed
  — which a derived image would then be stamped with, or validated against."
  [{:keys [kinds epoch]}]
  (kind-fingerprint (:sentexes kinds) @epoch))

(defn reasoning-fingerprint
  "The stamp a reasoning image is validated against: `{:sentexes fp :justifications fp}`,
  each a `kind-fingerprint`.  Belief reads both kinds — the sentexes, whose slots also
  move when a premise mark re-stores one, and the justifications — so a change to
  either moves the stamp, where `slot-fingerprint` alone misses a justification stored
  over sentexes that did not change."
  [{:keys [kinds epoch]}]
  (let [e @epoch]
    {:sentexes       (kind-fingerprint (:sentexes kinds) e)
     :justifications (kind-fingerprint (:justifications kinds) e)}))

(defn fsync
  "fsync every kind's log + idx, and rewrite the counters blob when the handle counter has
  moved since the last tick.

  The token dictionary is fsynced **first, under the sentexes kind lock** — that lock is
  what stops a record being appended between the two fsyncs, and so is what makes every
  record durable after this tick one whose tokens are durable too.

  **The counters blob is written only when it changed.**  Persisting it is a whole-file
  rewrite — a temp, an fsync of it, an `ATOMIC_MOVE` and an fsync of the directory — and
  the durability daemon ticks every three seconds for the life of the process, so writing
  it unconditionally charges a KB nobody is writing to those four operations a tick
  forever.  `synced-seq` holds what the file was last left holding; equal to the counter
  means the file already says what there is to say.  A skip can never cost a handle:
  `recover-next-id` takes the max of the blob and one past the highest slot in the idx, so
  a blob behind the counter is behind only on handles that were minted and never stored.

  **This runs on the durability daemon's thread**, and the counter it reads is bumped by
  the writer's.  A counter that moves between the read and the blob write adds no work —
  a blob one handle behind is what the paragraph above is about — but a `clear-records!`
  landing there costs the wipe: the blob would be stamped with the pre-wipe high-water
  mark and `synced-seq` would agree with it.  So the three that move together move under
  `counters-lock`, which the wipe takes for the same three; the counter is read inside
  it rather than before it, which is what makes the read part of the same step."
  [{:keys [dir kinds counter synced-seq dict counters-lock epoch]}]
  (with-write (:lock (:sentexes kinds))
    (when dict (dtok/fsync dict))
    (f/force! (:log (:sentexes kinds)) false)
    (f/force! (:idx (:sentexes kinds)) true))
  (doseq [[kind k] kinds :when (not= kind :sentexes)]
    (with-write (:lock k)
      (f/force! (:log k) false)
      (f/force! (:idx k) true)))
  (locking counters-lock
    (let [want @counter]
      (when-not (= want @synced-seq)
        (f/write-nippy-atomic! (counters-path dir) (counters-blob want @epoch))
        (reset! synced-seq want))))
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

(defn close!
  "Flush durably, record the log lengths this session closed at, close every RAF, then
  remove the dirty marker (a clean shutdown).

  The lengths are read **after** the fsync and written before anything closes, so the
  marker names exactly what is durable; the next open skips a log's tail walk while its
  length still agrees ([`f/log-tail-offset-from`](files.clj)).

  **Every handle is released whatever the flush did.**  The flush can fail — a full disk
  — and the caller above releases the directory's lock on a failed close as deliberately
  as on a clean one, so a throw that skipped the closes would hand the directory over
  with every `RandomAccessFile` still held.  The dirty marker is the one step that stays
  conditional: it says the store closed cleanly, and an unclean close is what it exists
  to record."
  [{:keys [dir kinds dict] :as store}]
  (try
    (fsync store)
    (f/write-clean-marker! dir (into {} (map (fn [[kind k]]
                                               [(clojure.core/name kind)
                                                (with-write (:lock k) (f/log-length (:log k)))]))
                                     kinds))
    (finally
      (doseq [[kind k] kinds]
        (with-write (:lock k)
          (close-quietly! (str (clojure.core/name kind) ".log") #(f/close! (:log k)))
          (close-quietly! (str (clojure.core/name kind) ".idx") #(f/close! (:idx k)))))
      (when dict (close-quietly! "the token dictionary" #(dtok/close! dict)))))
  (f/remove-dirty-marker! dir))

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
  "The premise set on open: the ids whose slot says premise, plus whatever the records
  say for the ids that have to be read.

  Which ids those are is the point of the flags.  A slot written before the premise bit
  existed says nothing about it, so its record is read — once, and never again after any
  write upgrades that slot.  A **tokenized** store reads every live record regardless,
  because that walk is also the token-damage check: a frame naming a token the
  dictionary does not hold is the record log's tail having outrun the dictionary's
  across a machine crash — the same cross-file skew `validate-idx-tail!` repairs between
  the log and its idx, and repaired the same way, by tombstoning the record rather than
  keeping an undecodable one.

  Wherever both speak the **record wins**, which is what makes the bit safe to trust:
  it is derived state over a durable record, exactly like the live-id set beside it.

  On a **dirty** open the walk covers every live record — as a tokenized open already
  does — and the slot flags are reconciled against them (`f/reconcile-slot-flags!`): the
  flags word is a cache and is not crash-atomic, so a torn flags page can leave a slot
  speaking a stale premise bit or strength rank, and the in-memory set the walk rebuilds
  fixes belief for this session but not the slot a later *clean* open would trust.  A slot
  that disagrees with its record is rewritten here, once, on the rare unclean open —
  self-healing, so the next open is fast again."
  [k root dict marked unsaid dirty?]
  (let [prem    marked
        n-said  (with-write (:lock k) (roster/live-tally marked))
        ;; A snapshot rather than the roster itself: the walk below tombstones a damaged
        ;; record through `kill!`, which drops that handle from the live set — an
        ;; iteration over the live bitmap would be walking a structure it is editing.
        ;; Under the lock like every other read of it, though this one runs on the opening
        ;; thread before the store is published: an invariant with an exception in it is
        ;; one nobody can check.
        walk    (if (or dict dirty?)
                  (with-write (:lock k) (roster/live-snapshot (:live-ids k)))
                  unsaid)
        damaged (volatile! 0)
        fixed   (volatile! 0)]
    (doseq [id walk]
      ;; only crash damage is repaired by tombstoning: a token the dictionary does not
      ;; hold or a body the codec cannot parse is the log's tail having outrun its
      ;; neighbours.  `:unknown-frame` is the opposite case — a build that cannot
      ;; decode a *valid* record — and rethrows, because a build that cannot read a
      ;; log must not delete it.
      (let [sx (try (fetch k id)
                    (catch clojure.lang.ExceptionInfo t
                      (when-not (#{:damaged-dictionary :malformed-record}
                                 (:type (ex-data t)))
                        (throw t))
                      (vswap! damaged inc)
                      (kill! k id)
                      nil))]
        (with-write (:lock k)
          (if (:strength sx) (roster/live-add! prem id) (roster/live-remove! prem id)))
        ;; a torn flags page across a crash may have left this slot's bit or rank stale;
        ;; the record is the truth, so rewrite the slot to it wherever they disagree
        (when (and dirty? sx)
          (let [premise? (some? (:strength sx))
                rank     (if premise? (strength/rank-of (:strength sx)) 0)]
            (when (f/reconcile-slot-flags! (:idx k) id premise? rank)
              (vswap! fixed inc))))))
    (when (pos? @damaged)
      (trove/log! {:level :warn
                   :msg (str "disk records: " @damaged " record(s) at " root
                             " cite tokens the dictionary does not hold — tombstoned")}))
    (when (pos? @fixed)
      (trove/log! {:level :warn :id ::flags-reconciled
                   :msg (str "disk records: reconciled " @fixed " slot flag(s) at " root
                             " against their records after an unclean shutdown"
                             " (torn flags page)")}))
    (trove/log! {:level :debug :id ::premise-set
                 :msg (str "disk records: premise set from " n-said
                           " annotated slot(s), " (count walk) " record(s) decoded")})
    (with-write (:lock k) (roster/live-optimize! prem))
    prem))

(defn open-record-store
  "Open a `DiskRecordStore` rooted at `dir/records`.  Recovers each kind, rebuilds the
  live-id sets, the premise set (sentexes with a non-nil :strength), and the id
  counter, and drops a dirty marker (removed on a clean `close!`).

  `:cache-capacity` sizes the per-kind hot-record LRU, defaulting to the
  `vaelii.disk.cache` property; 0 runs with no cache (what the fetch benchmark measures
  against, and the honest per-fetch cost).  `:tokenize?` writes sentex bodies as ids from
  a durable token dictionary rather than in full, defaulting to the `vaelii.disk.tokens`
  property; it is a *write* choice only — frames written either way always read."
  ([dir] (open-record-store dir nil))
  ([dir {:keys [cache-capacity tokenize?]
         :or   {cache-capacity (config/disk-cache-capacity)
                tokenize?      (config/disk-tokens?)}}]
   (let [root (str dir "/records")]
     (f/ensure-dir! root)
     (f/assert-format! root)
     ;; the dictionary is opened whenever the store *has* one, even with tokenized
     ;; writes off, because frames already written need it to decode
     (let [;; the marker says the last close was unclean; capture it once — it gates the
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
           closers (java.util.ArrayList.)]
       (try
         (let [dict   (when (or tokenize? (f/token-log-present? root))
                        (let [d (dtok/open-token-log root)]
                          (.add closers #(dtok/close! d))
                          d))
               codecs (codec/by-kind dict tokenize?)
               ;; a premise is a sentex whose :strength is non-nil, and its slot says so —
               ;; so the set rides the idx walk `open-kind` is already making, and only a
               ;; slot that does not say costs a record read (`rebuild-premises!`)
               marked (roster/live-roster)
               unsaid (java.util.ArrayList.)
               ;; runs inside `open-kind`'s idx walk, on the opening thread before the
               ;; store is published, so the roster takes no lock here
               tap    (fn [id flags]
                        (if-some [premise? (f/slot-premise flags)]
                          (when premise? (roster/live-add! marked id))
                          (.add unsaid id)))
               kinds  (into {} (map (fn [n]
                                      (let [k (open-kind root n cache-capacity codecs
                                                         (get clean n)
                                                         (when (= n "sentexes") tap))]
                                        (.add closers #(f/close! (:log k)))
                                        (.add closers #(f/close! (:idx k)))
                                        [(keyword n) k])))
                            kind-names)
               counters (f/read-nippy-file (counters-path root) {:seq 1})
               counter  (atom (recover-next-id counters kinds))
               prem     (rebuild-premises! (:sentexes kinds) root dict marked unsaid dirty?)]
           (f/create-dirty-marker! root)
           (->DiskRecordStore root kinds counter (atom nil) prem dict (Object.)
                              (atom (:epoch counters))))
         (catch Throwable t
           (doseq [c closers] (close-quietly! "a half-opened record store" c))
           (throw t)))))))

;; ---- compaction ---------------------------------------------------------

(defn- kind-dead-ratio
  "Dead-byte fraction of kind `k`: 1 - live-frame-bytes / log-length.  Live-frame
  bytes are summed from the live slots (offset + 4 + length)."
  ^double [k]
  (with-write (:lock k)
    (usable! k)
    (let [total (f/log-length (:log k))
          live  (volatile! 0)]
      (f/scan-idx! (:idx k) (fn [_ _ length _] (vswap! live + (+ 4 (long length)))))
      (if (pos? total) (- 1.0 (/ (double @live) (double total))) 0.0))))

(defn dead-ratio
  "Max dead-byte ratio across the kinds — the durability daemon's compaction trigger."
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

  It exists because the window this store's lifecycle turns on is *between* the snapshot
  and the reconcile, and it is a window a test cannot reach by sleeping: a rewrite of a
  test-sized log is over in microseconds, so \"close the directory while a rewrite is
  open\" reproduces by luck or not at all.  A barrier here holds the rewrite at exactly
  that point, so the handshake can be asserted rather than hoped for."}
  rewrite-barrier
  (atom nil))

(defn abort-compaction!
  "Tell an auto-compaction of `store` to abandon its rewrite: set `:aborted` on every
  kind, under the kind lock every other write of that atom takes.  Idempotent.  Called
  by `backend/close-dir!`, which is closing the store, so nothing here is written for a
  store that goes on being used.

  **What it reaches, and what it deliberately does not.**  A rewrite still copying
  frames sees the flag at its next check (`abort-check-frames`) and stops there; one
  that has reached the reconcile discards its temps, exactly as `clear-records!`'s abort
  does.  A rewrite **past its commit marker** is not reachable — and that is the answer,
  not a gap.  The reconcile reads the flag under the kind lock and holds that lock until
  the install is done, so an abort lands either before the read or after the install,
  never between; and a marker on disk is a rewrite the *next open* would finish off the
  marker anyway (`recover-compaction!`).  A wipe supersedes such an install because the
  wipe destroys what it would install; a close does not, so the close lets it finish now
  rather than handing the next opener a half-installed directory.

  **An abort of a rewrite that has not started yet sticks**, which is the difference
  between this and `clear-records!`'s abort and the reason it is written separately.  The
  compaction executor's task checks the durability registry and only *then* calls in
  here, so a close can take the kind lock in the gap between that check and the
  compaction's own snapshot — find `:compacting` nil, mark nothing, and leave the rewrite
  that starts a moment later believing nobody objected.  The wipe can shrug at that (it
  has already truncated the files the rewrite reads); a close cannot, because the whole
  of what it is waiting for is that rewrite.  So the flag is written whether or not one is
  running, and the snapshot carries an existing one across rather than clearing it.  The
  wipe keeps the `when c` form for the mirror-image reason: its store goes on living, and
  a flag left set on one would make `:compacting` non-nil forever, with every later
  `store!` folding an id into a `:touched` set nothing will ever read.

  It does **not** wait.  The join belongs to the caller that is about to give the
  directory away — `backend/close-dir!`, through
  `durability/await-compaction-quiescent!` — because this store holds no lock during the
  rewrite for a closer to block on."
  [{:keys [kinds]}]
  (doseq [k (vals kinds)]
    (with-write (:lock k)
      (swap! (:compacting k) #(assoc (or % {:touched #{}}) :aborted true))))
  nil)

(defn- compact-kind!
  "Rewrite kind `k`'s log with only its live frames, preserving slot ids, crash-safely
  — **copy-on-write**, so the O(live) record rewrite does not stall the kind's reads
  and writes.  The rewrite (read + thaw + re-freeze + write every live frame, the
  O(bytes) cost that can run to gigabytes) runs *without* the kind lock, reading the
  log's immutable region through a private read handle; the lock is held only for two
  brief brackets:

  - **snapshot** (front): capture the live slots and `cutoff` = log length, and arm
    delta tracking (`:compacting`), all so appends past `cutoff` and slot mutations
    made during the rewrite are recorded rather than missed.
  - **reconcile + swap** (end): fold the touched ids into the temp (copying their
    current frame, or tombstoning a since-deleted id), preserve the high-water mark,
    fsync, write the commit marker, replay the temps over the originals, drop them.

  Crash-safety is unchanged: the marker is written only after every live-file read the
  reconcile needs has succeeded, so a crash (or a `close!`) before it leaves the
  complete originals authoritative and the temps discarded, and one after it replays
  the fsynced temps.  A `clear-records!` or a `close-dir!` that lands mid-rewrite sets
  `:aborted` (`abort-compaction!`): the copy loop stops at its next check and the
  reconcile discards the temps, rather than resurrecting the wiped state or leaving a
  half-written temp under a directory another process has just been handed.

  **A slot whose frame the log cannot give back is dropped, not carried.**  It is what a
  truncated tail leaves under a slot the truncation did not reach, and a rewrite that
  re-froze the nil would put the handle back as a live record fetching to nothing.  Such
  a slot is tombstoned in the temp and the handle taken out of the live set, the premise
  set and the record cache once the install lands — with a `:warn` per handle, since a
  record disappearing is something an operator has to be told rather than shown by a
  later count."
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
                         (roster/live-remove-all! (:live-ids k) @lost)
                         (when premises (roster/live-remove-all! premises @lost))
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
      (loop [todo (seq snapshot) n 0]
        (when (and todo
                   (or (pos? (rem n abort-check-frames))
                       (not (:aborted @(:compacting k)))))
          (let [[id off len flags] (first todo)]
            (if-let [rec (f/read-record-sized rlog off len)]
              (let [[noff plen] (f/append-record-sized! tlog rec)]
                (f/write-slot! tidx id noff plen flags 0))
              (drop-slot! tidx id))
            (recur (next todo) (inc n)))))
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
  ;; A lost frame drops its handle from the premise roster only in the sentexes kind.  A
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
