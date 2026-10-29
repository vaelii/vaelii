;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.files
  "Low-level file primitives for the on-disk backend.

  - Append-only `.log` files hold length-prefixed nippy frames.
    Frame layout: `[len: i32 big-endian][nippy-bytes]`.  The offset returned from
    `append-record!` points at the len prefix.
  - `.idx` files are fixed-width arrays of 24-byte slots, indexed by id.
    Slot layout:
      bytes  0..7  offset (i64, -1 = empty, -2 = tombstone)
      bytes  8..15 length (i64)
      bytes 16..19 flags  (u32; bit 0 = the premise bit is meaningful, bit 1 = premise,
                           bits 2..3 = a premise's strength rank, 0 when unrecorded)
      bytes 20..23 gen    (u32, reserved — written as 0)
    Reads rely on the OS page cache; writes overwrite the slot in place.
    A slot is read in **one positional channel read**, not a seek plus four primitive
    `readLong`/`readInt` calls — a `RandomAccessFile` is unbuffered, so each of those is
    its own syscall and moving 24 bytes cost six of them (measured: 52% of a warm
    record fetch, `lein bench-records`).
  - `.nippy` files hold whole-blob metadata (counters, the premise set).  Callers
    rewrite them atomically via `write-nippy-atomic!`.

  **Shared-pointer invariant.**  A seek→read/write pair on a `RandomAccessFile` uses that
  object's single shared file pointer, so any access to a store's live RAF must hold the
  owning kind lock; the disk adapters take a per-kind lock around every such touch (write,
  `force!`) for exactly this reason.  The *read* primitives here (`read-slot`,
  `read-record`, `read-record-sized`) are positional `FileChannel` reads instead — they
  name the file offset in the call and never touch the pointer, so they neither disturb a
  concurrent seek nor need one of their own.

  Compression: frames freeze under the nippy compressor named by the
  `vaelii.disk.compress` system property (`lz4` | `zstd` | `none`); default none.
  nippy reads the compressor id from each frame header, so mixed frames thaw
  correctly.  Durability: `vaelii.disk.fsync=dsync` opens logs `rwd` (O_DSYNC) so
  every append is synchronous — off by default (the durability daemon fsyncs on a
  tick instead)."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [taoensso.nippy :as nippy]
            [taoensso.trove :as trove]
            [vaelii.impl.config :as config]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.progress :as progress])
  (:import [java.io ByteArrayInputStream DataInputStream DataOutputStream File
            RandomAccessFile FileInputStream FileOutputStream
            BufferedInputStream BufferedOutputStream]
           [java.nio.channels FileChannel]
           [java.nio.file Files Paths StandardCopyOption OpenOption
            StandardOpenOption]))

(def slot-bytes
  "Fixed slot width in `.idx` files: 8 (offset) + 8 (length) + 4 (flags) + 4 (gen) = 24."
  24)

(def empty-offset     "Slot offset meaning 'nothing stored at this id'." -1)
(def tombstone-offset "Slot offset meaning 'this id was deleted'."       -2)

(defn ensure-dir!
  "Create the directory at `path` (and any missing parents); return the `File`."
  ^File [^String path]
  (doto (File. path) (.mkdirs)))

(def format-version
  "On-disk layout version for a backend directory.  Bumped only on an incompatible
  layout change; a directory written before the sentinel is adopted as version 1."
  1)

(def ^:private supported-format-versions #{1})

(def manifest-bytes
  "The most an EDN **manifest** may hold — a dump's `meta.edn` and `index.edn`, a store's
  `format.edn`, an index directory's `layout.edn` and `records.edn`, a belief image's
  `manifest.edn`, a corpus's `report.edn`, a machine's `catalog.edn`.

  Every one of them is a handful of keys, and each is the *first* thing read about a
  directory nobody has promised anything about — `vaelii.browser.catalog` probes every
  entry of the KB search path this way — so an unbounded read is a whole file pulled into
  a string on the strength of its name.  A megabyte is orders of magnitude above the
  largest of them (a hand-written `catalog.edn` naming thousands of KBs) and still a
  bound."
  (* 1024 1024))

(defn read-edn-manifest
  "The EDN manifest in `f`, read under `manifest-bytes` — or a refusal
  (`:manifest-too-large`) naming the file and the bound.

  **The bound is on the read, not on the file's stated length.**  `File.length` answers
  0 for a FIFO and for most of `/proc`, and a symlink to one of those is a `slurp` that
  never ends; reading a bounded number of bytes and refusing the one past the bound
  needs the file to say nothing true about itself.  Bytes rather than characters, so the
  figure the refusal states is the figure that was read.

  Content the EDN reader cannot parse is refused by name too (`:malformed-manifest`), so
  a manifest cut mid-form is a `:type` a caller can discriminate on rather than a bare
  \"EOF while reading\".  Which of the two refusals means \"not a KB\" and which means
  \"a broken one\" is the caller's to decide."
  [f]
  (let [^File f (io/file f)
        limit (long manifest-bytes)
        out   (java.io.ByteArrayOutputStream.)
        buf   (byte-array 8192)]
    (with-open [^java.io.InputStream in (io/input-stream f)]
      (loop []
        (let [n (.read in buf)]
          (when (pos? n)
            (.write out buf 0 n)
            (when (<= (.size out) limit) (recur))))))
    (when (> (.size out) limit)
      (throw (ex-info (str "manifest " (.getPath f) " is longer than " limit
                           " bytes — a meta.edn / format.edn / layout.edn / catalog.edn"
                           " is a handful of keys, and a file this size under one of"
                           " those names is not one")
                      {:type :manifest-too-large :file (.getPath f) :max limit})))
    (try (edn/read-string (String. (.toByteArray out)
                                   java.nio.charset.StandardCharsets/UTF_8))
         (catch Exception e
           (throw (ex-info (str "manifest " (.getPath f) " is not readable EDN: "
                                (ex-message e) " — the file was cut mid-form, or was"
                                " never one")
                           {:type :malformed-manifest :file (.getPath f)} e))))))

(defonce ^:private ^java.util.concurrent.atomic.AtomicBoolean dir-fsync-warned
  (java.util.concurrent.atomic.AtomicBoolean. false))

(defn fsync-dir!
  "Best-effort fsync of the directory holding `path`, so a file's creation/deletion
  is durable.  Swallowed on filesystems that reject directory fsync — `FileChannel/open`
  on a directory is not portable.

  **Warned once**, because the swallow is not free: a commit marker's *existence* is
  the atomic commit point of a compaction, and `replay-temp-onto-raf!` truncates the
  live log before copying the temp over it.  Where the marker's directory entry never
  reaches the platter, a power loss mid-replay leaves no marker to replay from and no
  original to fall back on.  Silence makes that exposure indistinguishable from a
  filesystem where the fsync worked."
  [^String path]
  (try
    (when-let [dir (.getParentFile (File. path))]
      (with-open [ch (FileChannel/open (.toPath dir)
                                       (into-array OpenOption [StandardOpenOption/READ]))]
        (.force ch true)))
    (catch Throwable t
      (when (.compareAndSet dir-fsync-warned false true)
        (trove/log! {:level :warn :id ::dir-fsync-unsupported
                     :msg (str "this filesystem rejects directory fsync (" (.getMessage t)
                               ") — a file's creation or deletion is durable only when "
                               "the filesystem makes it so, which weakens the compaction "
                               "commit marker.  Reported once.")
                     :data {:path path}}))
      nil)))

(defn fsync-file!
  "fsync the file at `path`, then the directory holding it (`fsync-dir!`)."
  [^String path]
  (with-open [ch (FileChannel/open (.toPath (File. path))
                                   (into-array OpenOption [StandardOpenOption/WRITE]))]
    (.force ch true))
  (fsync-dir! path))

(defn- write-atomic!
  "Write `path` by calling `write!` on a `FileOutputStream` over a unique temp file,
  fsyncing the temp, atomic-renaming it over `path`, then fsyncing the parent dir —
  durable, not merely atomic (a power loss can otherwise leave the rename visible while
  the data blocks are still zeros).  The per-call unique temp suffix keeps a racing fsync
  tick from consuming another writer's temp."
  [^String path write!]
  (let [tmp    (str path ".tmp." (java.util.UUID/randomUUID))
        parent (.getParentFile (File. path))]
    (when parent (.mkdirs parent))
    (try
      (with-open [fos (FileOutputStream. tmp)]
        (write! fos)
        (.sync (.getFD fos)))
      ;; Unguarded by platform, unlike `index-snapshot/rename!`, and the difference is
      ;; the target: every file written this way — the counters, the premise set, the
      ;; clean marker, the image's meta and its fallback blob, the EDN manifests — is read
      ;; whole, and only the image's CSR sections are ever mapped.  So no process holds a
      ;; mapping this replace has to break.
      (Files/move (Paths/get tmp (into-array String []))
                  (Paths/get path (into-array String []))
                  (into-array java.nio.file.CopyOption
                              [StandardCopyOption/ATOMIC_MOVE
                               StandardCopyOption/REPLACE_EXISTING]))
      (fsync-dir! path)
      (finally
        (.delete (File. tmp))))))

(defn write-nippy-atomic!
  "Write `value` to `path` as a headerless nippy stream (`freeze-to-out!`), through
  `write-atomic!`'s temp, fsync and rename."
  [^String path value]
  (write-atomic! path (fn [^FileOutputStream fos]
                        (let [out (DataOutputStream. (BufferedOutputStream. fos))]
                          (nippy/freeze-to-out! out value)
                          (.flush out)))))

(defn- spit-manifest!
  "Write `m` to `path` as EDN through `write-atomic!`, so a crash mid-write leaves the
  previous manifest or the new one, never a file `read-edn-manifest` refuses as
  `:malformed-manifest`."
  [^String path m]
  (write-atomic! path (fn [^FileOutputStream fos]
                        (.write fos (.getBytes ^String (pr-str m)
                                               java.nio.charset.StandardCharsets/UTF_8)))))

(defn assert-format!
  "Check the store directory `root` against its `format.edn` sentinel: a known version
  is ok, an unknown one throws, and a missing sentinel is written with the current
  version (a pre-sentinel directory is by definition today's layout).

  **A damaged sentinel is refused, not rewritten.**  A directory whose sentinel was cut
  mid-write is one whose *records* were being written at the same moment, and writing
  over it would adopt whatever is beside it as today's layout — the one reading that is
  certainly wrong.  `:unreadable-store` names the file rather than the version, since
  there is no version to name.  A sentinel past `manifest-bytes` is refused as
  `:manifest-too-large`, as the catalog refuses it."
  [root]
  (let [file (File. (str root) "format.edn")]
    (if (.exists file)
      (let [m (try (read-edn-manifest file)
                   (catch clojure.lang.ExceptionInfo e
                     (if (= :manifest-too-large (:type (ex-data e))) (throw e) ::unreadable))
                   (catch Exception _ ::unreadable))]
        (when (= ::unreadable m)
          (throw (ex-info (str "the durable-store sentinel " (.getPath file)
                               " is not readable EDN — the directory was written by"
                               " something else, or its sentinel was cut mid-write")
                          {:type :unreadable-store :file (.getPath file) :root (str root)})))
        (let [v (:format-version m)]
          (when-not (contains? supported-format-versions v)
            (throw (ex-info (str "Unsupported durable-store format version " v " at " root
                                 " — this engine supports " (sort supported-format-versions) ".")
                            {:type :unsupported-format :found v
                             :supported supported-format-versions :root (str root)})))))
      (spit-manifest! (.getPath file) {:format-version format-version}))))

(def ^:private index-layout-file "layout.edn")

(defn index-layout-decision
  "Check an index directory `root`'s `layout.edn` sentinel against `current`
  (`kv/index-layout-version`), as one of three answers: `:current` when the layout version
  matches, `:stale` when it does not — an absent sentinel over a `populated?` log
  included, which is what an index written before the sentinel existed looks like —
  and `:unwritten` for a fresh, empty directory, which needs the sentinel but no
  rebuild.  A stale log replays cleanly and then misses every read whose key shape
  moved, so `:stale` is the caller's cue to clear the index, rebuild it from the
  records, and then `write-index-layout!`.

  **This reads and never writes.** A base mounted under `:base` opts is checked by
  the same call and may not be written to, so the caller writes the sentinel
  `:unwritten` calls for — `write-index-layout!` for a KB that owns the directory, nothing
  at all for a read-only mount.

  **A damaged sentinel is `:stale`**, not a refusal, and so is one past `manifest-bytes`.
  The question this answers is \"can I prove these entries were keyed the way this build
  keys them\", and a sentinel cut mid-write proves nothing — so the answer is the one an
  unprovable sentinel already gets, and the index is rebuilt from the records, which are
  the ground truth either way.  That is the opposite of `assert-format!`'s reading of
  the same damage, because an index is a cache and records are not."
  [root current populated?]
  (let [file (File. ^String (str root) ^String index-layout-file)]
    (if (.exists file)
      (if (= current (:index-layout (try (read-edn-manifest file) (catch Exception _ nil))))
        :current
        :stale)
      (if populated? :stale :unwritten))))

;; A rebuild's *first* write, not its last: `index-layout-decision` reads an absent
;; sentinel over an empty index as `:unwritten`, so a crash between the clear and the
;; rebuild's first frame would otherwise leave a directory that opens clean — an empty
;; index over full records, answering nothing.  Marking the directory before the clear
;; makes that crash window read as `:stale` instead, and `write-index-layout!` is what clears
;; the mark.  Any value that is not `current` would do; naming the state says why it is
;; there when somebody reads the file after a crash.
(defn mark-index-rebuilding!
  "Write `root`'s `layout.edn` as mid-rebuild, so an open that lands before
  `write-index-layout!` reads `:stale` and rebuilds again."
  [root]
  (spit-manifest! (str root "/" index-layout-file) {:index-layout ::rebuilding})
  nil)

(defn write-index-layout!
  "Write `root`'s `layout.edn` naming `current` — the commit mark of a layout
  rebuild (`index-layout-decision`)."
  [root current]
  (spit-manifest! (str root "/" index-layout-file) {:index-layout current})
  nil)

(def ^:private reasoners-file "reasoners.edn")

(defn recorded-reasoners
  "The reasoner names recorded in the store directory `root` (`reasoners.edn`), as a set,
  or nil when the directory records none.  Read through `read-edn-manifest`."
  [root]
  (let [file (File. ^String (str root) ^String reasoners-file)]
    (when (.exists file)
      (set (:reasoners (read-edn-manifest file))))))

(defn write-reasoners!
  "Record `names` as the reasoner set of the store directory `root`."
  [root names]
  (spit-manifest! (str root "/" reasoners-file) {:reasoners (vec (sort names))})
  nil)

(def ^:private records-identity-file "records.edn")

(defn records-identity
  "The record store `root`'s index was last built against, or nil when the directory has
  never been recorded.  Read through `read-edn-manifest`, so a file past the bound or cut
  mid-form is refused by name."
  [root]
  (let [file (File. ^String (str root) ^String records-identity-file)]
    (when (.exists file)
      (:records (read-edn-manifest file)))))

(defn write-records-identity!
  "Record which store `root`'s index describes.

  A `:disk-log` index over `:disk` records needs no such record: the two share the directory,
  so the files cannot describe anything else.  An index over records on a **server** can —
  the directory says nothing about which database, and the coverage check that would catch
  a mismatch compares record *counts*, which two unrelated databases match easily.  What
  gets through is worse than an empty index: reads answer out of another store's handles,
  and a re-assert of a sentence this store does hold mints a second handle for it."
  [root identity]
  ;; the identity is written on the *first* open, which is before anything else has had cause
  ;; to make the directory
  (.mkdirs (File. ^String (str root)))
  (spit-manifest! (str root "/" records-identity-file) {:records identity})
  nil)

(defn- dsync? [] (= :dsync (config/disk-fsync-mode)))

(defn- open-rw ^RandomAccessFile [^String path ^String mode]
  (let [parent (.getParentFile (File. path))]
    (when (and parent (not (.exists parent))) (.mkdirs parent)))
  (RandomAccessFile. path mode))

(defn open-log
  "Open a log file for append + read, positioned at EOF.  Under
  `vaelii.disk.fsync=dsync` the channel is `rwd` so every append is durable.

  The seek is guarded: a throw between the open and the return leaves a
  `RandomAccessFile` nothing holds a reference to and nothing will close, and the caller
  that answers a failed open by releasing the directory lock would then give the lock
  back over a handle this JVM still has."
  ^RandomAccessFile [^String path]
  (let [raf (open-rw path (if (dsync?) "rwd" "rw"))]
    (try (.seek raf (.length raf)) raf
         (catch Throwable t
           (try (.close raf) (catch Throwable _ nil))
           (throw t)))))

(defn open-idx
  "Open an idx file for random read/write.  Always `rw` — idx slots are
  reconstructible from the logs, so they need no per-write durability."
  ^RandomAccessFile [^String path]
  (open-rw path "rw"))

(defn open-log-read
  "Open a private read-only RAF on an existing log.  The copy-on-write compactor reads
  the log's immutable (already-written) region through its own handle, so it needn't
  hold the kind lock while it does the O(live) rewrite — a fresh RAF has its own file
  pointer, so this does not touch the shared-pointer invariant of the store's live RAF."
  ^RandomAccessFile [^String path]
  (open-rw path "r"))

(defn close! [^java.io.Closeable c] (when c (.close c)))

(defn force!
  "fsync `raf`'s channel; `meta-data?` includes file metadata (mtime, length)."
  [^RandomAccessFile raf meta-data?]
  (.force (.getChannel raf) (boolean meta-data?)))

;; ---- a store that stops ---------------------------------------------------
;; A disk store's channels are shared by every call, so a channel that closes under one
;; call — a thread interrupt closes a `FileChannel` it is blocked in, and a closed channel
;; also closes the `RandomAccessFile` that owns it — is closed for every later call.  An
;; I/O failure on a write leaves the file in a state the next open repairs rather than the
;; running session.  Either way the store answers every later call with one typed refusal
;; rather than whichever `IOException` the next channel it touches happens to throw.  The
;; latch is an atom per store holding `{:reason :path :cause}`; the first fault wins, and
;; a reopen is the only way out.

(defn- fault-message [{:keys [reason path]}]
  (str "disk store " path
       (case reason
         :closed         " is closed"
         :interrupted    " lost a channel to a thread interrupt"
         :channel-closed " lost a channel that closed under it"
         :write-failed   " failed a write"
         :fsync-failed   " failed an fsync")
       " — it refuses every call until the directory is opened again"))

(defn fault-refusal
  "The `:store-unusable` refusal for the latched fault `f`, carrying `:reason` and
  `:path`, with the throwable that latched it as the cause."
  [{:keys [reason path cause] :as f}]
  (ex-info (fault-message f) {:type :store-unusable :reason reason :path path} cause))

(defn check-fault!
  "Throw the latched refusal when `fault` holds one."
  [fault]
  (when-let [f @fault] (throw (fault-refusal f))))

(defn fault-reason
  "The latch reason for `t`, thrown by an access to a live channel, or nil when `t` does
  not stop the store.  A closed channel stops it on any access; any other `IOException`
  only on a write (`write?` true) or an fsync (`write?` `:fsync`), since a read that
  fails leaves nothing on disk changed."
  [^Throwable t write?]
  (cond
    (instance? java.nio.channels.ClosedByInterruptException t) :interrupted
    (instance? java.nio.channels.ClosedChannelException t)     :channel-closed
    (and write? (instance? java.io.IOException t))             (if (= :fsync write?)
                                                                 :fsync-failed
                                                                 :write-failed)))

(defn latch-fault!
  "Latch `fault` with `reason` unless it already holds a fault, and return the refusal
  for whichever fault it holds.  The first latch logs at `:error`, once: every later call
  is told through the refusal."
  [fault path reason ^Throwable t]
  (let [f        {:reason reason :path path :cause t}
        [old now] (swap-vals! fault #(or % f))]
    (when (nil? old)
      (trove/log! {:level :error :id ::store-faulted :msg (fault-message now) :error t}))
    (fault-refusal now)))

(defn latch-closed!
  "Latch `fault` as `:closed` unless it already holds a fault — what a clean close leaves,
  so a call on the store after it is refused by name rather than by a closed channel."
  [fault path]
  (swap! fault #(or % {:reason :closed :path path})))

(defmacro with-io-guard
  "Run `body` against a store's live channels, latching `fault` and throwing its refusal
  when what `body` throws stops the store (`fault-reason`).  Anything else travels
  unchanged."
  [fault path write? & body]
  `(try ~@body
        (catch java.io.IOException t#
          (if-let [r# (fault-reason t# ~write?)]
            (throw (latch-fault! ~fault ~path r# t#))
            (throw t#)))))

(defn- disk-compressor []
  (case (config/disk-compress)
    :zstd nippy/zstd-compressor
    :lz4  nippy/lz4-compressor
    nil))

(defn- freeze-bytes ^bytes [value]
  (if-let [c (disk-compressor)]
    (nippy/freeze value {:compressor c})
    (nippy/freeze value)))

;; Behind the class-name check (`vaelii.impl.io.thaw`): a log is a file, a file is
;; untrusted input, and a frame naming a class is refused before the name is resolved.
(defn- thaw-bytes [^bytes bs] (safe/thaw bs))

(defn- write-fully-at!
  "Write every remaining byte of `bb` to `ch` at file position `pos` — positional, so
  the RAF's shared file pointer is neither used nor moved, and looped because a channel
  write may be short."
  [^FileChannel ch ^java.nio.ByteBuffer bb ^long pos]
  (loop [p pos]
    (when (.hasRemaining bb)
      (recur (+ p (long (.write ch bb p)))))))

(defn- append-bytes!
  "Append `buf` — one or more complete frames, already packed — at the log's end and
  return the offset it landed at.  **All or nothing.**  A write that fails partway
  (`ENOSPC`, an I/O error) would otherwise leave a frame whose length prefix claims more
  bytes than follow it, with the session appending past it: the next dirty open's
  length-chain walk (`log-tail-offset`) would then step from that prefix into the
  middle of a later frame, read garbage as a length, stop, and truncate everything
  after — records fsynced by later ticks included.  So the log is set back to its
  pre-write length before the failure travels, and what it holds is frames the walk
  can step over, or nothing new.  Two syscalls on the hot path: the length and the
  one positional write.  Caller must hold the log's write lock."
  ^long [^RandomAccessFile log-raf ^bytes buf]
  (let [off (.length log-raf)]
    (try
      (write-fully-at! (.getChannel log-raf) (java.nio.ByteBuffer/wrap buf) off)
      (catch Throwable t
        (try (.setLength log-raf off)
             (catch Throwable rollback (.addSuppressed t rollback)))
        (throw t)))
    off))

(defn- frame-bytes
  "One frame — `[len: i32][payload]` — as a byte array."
  ^bytes [^bytes payload]
  (let [n   (alength payload)
        buf (byte-array (+ 4 n))
        bb  (java.nio.ByteBuffer/wrap buf)]
    (.putInt bb n)
    (.put bb payload)
    buf))

(defn append-record-sized!
  "Append a nippy-serialized value to the log as one frame; return `[offset
  payload-length]` — the byte offset of the `[len]` prefix, and how many payload bytes
  follow it, which is what an idx slot records (`write-slot!`), so the caller needs no
  second length read to learn it.  All-or-nothing (`append-bytes!`).  Caller must hold
  the log's write lock."
  [^RandomAccessFile log-raf value]
  (let [bs (freeze-bytes value)]
    [(append-bytes! log-raf (frame-bytes bs)) (alength bs)]))

(defn append-record!
  "Append a nippy-serialized value to the log; return the byte offset of the `[len]`
  prefix.  `append-record-sized!` for a caller that also wants the payload length."
  ^long [^RandomAccessFile log-raf value]
  (append-bytes! log-raf (frame-bytes (freeze-bytes value))))

(defn append-records!
  "Append every value in `values` to the log, each its own frame, **as one write**:
  the frames are packed into a single buffer and land together or not at all
  (`append-bytes!`), so a batch of ops is never half on disk.  Returns the offset of
  the first frame, or the log length when `values` is empty.  Caller must hold the
  log's write lock."
  ^long [^RandomAccessFile log-raf values]
  (let [frames (mapv #(frame-bytes (freeze-bytes %)) values)
        total  (reduce (fn [^long acc ^bytes f] (+ acc (alength f))) 0 frames)
        buf    (byte-array total)
        bb     (java.nio.ByteBuffer/wrap buf)]
    (doseq [^bytes f frames] (.put bb f))
    (append-bytes! log-raf buf)))

(defn append-records-sized!
  "Append every value in `values` to the log, each its own frame, **as one write** —
  `append-record-sized!`'s batch form.  Returns a vector of `[offset payload-length]` in
  input order, which is the pair an idx slot records, so the caller writes the slots
  without a second read of any length prefix.

  All-or-nothing for the whole batch (`append-bytes!`), which is stronger than a loop of
  single appends and is the point: a record at a time is two syscalls apiece on an
  unbuffered `RandomAccessFile`, and a bulk load pays that per record for nothing — the
  frames are known before any of them is written.  Caller must hold the log's write lock."
  [^RandomAccessFile log-raf values]
  (let [payloads (mapv freeze-bytes values)
        total    (reduce (fn [^long acc ^bytes b] (+ acc 4 (alength b))) 0 payloads)
        buf      (byte-array total)
        bb       (java.nio.ByteBuffer/wrap buf)]
    (doseq [^bytes b payloads]
      (.putInt bb (alength b))
      (.put bb b))
    (let [base (append-bytes! log-raf buf)]
      (first
       (reduce (fn [[acc ^long off] ^bytes b]
                 (let [n (alength b)]
                   [(conj acc [off n]) (+ off 4 n)]))
               [[] base] payloads)))))

(defn- read-at
  "Fill `bb` from `ch` starting at file position `pos`; true iff it filled completely
  (false at EOF).  A positional channel read names its offset, so it neither uses nor
  moves the RAF's shared file pointer."
  [^FileChannel ch ^java.nio.ByteBuffer bb ^long pos]
  (loop [p pos]
    (if (zero? (.remaining bb))
      true
      (let [n (.read ch bb p)]
        (if (neg? n) false (recur (+ p (long n))))))))

(defn read-record-sized
  "Thaw the frame at `offset` whose payload is `length` bytes — **one** positional read,
  of the payload alone.  The slot already recorded the payload length, so a caller
  holding the slot needs neither a seek nor a re-read of the length prefix."
  [^RandomAccessFile log-raf ^long offset ^long length]
  (when (and (>= offset 0) (pos? length))
    (let [bb (java.nio.ByteBuffer/allocate (int length))]
      (when (read-at (.getChannel log-raf) bb (+ offset 4))
        (thaw-bytes (.array bb))))))

(defn read-record
  "Read a nippy value from the log at `offset`; nil for a negative or past-EOF offset.
  For a caller that holds the slot, `read-record-sized` is one read instead of two."
  [^RandomAccessFile log-raf ^long offset]
  (when (>= offset 0)
    (let [ch  (.getChannel log-raf)
          hdr (java.nio.ByteBuffer/allocate 4)]
      (when (read-at ch hdr offset)
        (read-record-sized log-raf offset (.getInt hdr 0))))))

(defn log-length ^long [^RandomAccessFile log-raf] (.length log-raf))

(defn read-slot
  "Read a slot by id: `{:offset :length :flags :gen :tombstone?}`, or nil when the
  slot is past EOF (unwritten), empty (offset=-1), or a zero-filled gap
  (offset=0 AND length=0, left where a slot written past the idx's end grew it over
  unwritten ids — no real record has length 0, so this is unambiguous).

  One positional read of the 24 bytes, decoded in memory: a short read *is* the
  past-EOF test, so this costs neither a `.length` call to make that test nor a seek
  and four primitive reads to satisfy it."
  [^RandomAccessFile idx-raf ^long id]
  (let [bb (java.nio.ByteBuffer/allocate slot-bytes)]
    (when (read-at (.getChannel idx-raf) bb (* id slot-bytes))
      (let [offset (.getLong bb 0)
            length (.getLong bb 8)
            flags  (long (bit-and 0xffffffff (.getInt bb 16)))
            gen    (long (bit-and 0xffffffff (.getInt bb 20)))]
        (when (and (not= offset empty-offset)
                   (not (and (zero? offset) (zero? length))))
          {:offset offset :length length :flags flags :gen gen
           :tombstone? (= offset tombstone-offset)})))))

;; ---- slot flags ---------------------------------------------------------
;; Two bits of the reserved `flags` word, because one would not be enough: a slot
;; written before they existed reads as 0, and 0 must mean **unknown** rather than
;; "not a premise".  So bit 0 says the slot speaks at all and bit 1 is what it says.
;; A store therefore needs no version bump and no declaration anyone could set wrongly
;; — a slot written by an older build is answered from its record, and any write
;; upgrades it.
;;
;; Bits 2..3 carry a premise's **strength rank** — the same column trick, one field up.
;; `premise-strength` is read once per premise on every `recover`, and off disk that
;; meant paging the whole record for one keyword.  The rank rides the slot the open walk
;; already reads, so the reader answers off 24 bytes instead of a frame + thaw.  0 means
;; "unrecorded" — a non-premise, or a premise slot older than these bits — and sends the
;; caller to the record, so an older build's slots (and an older build reading a newer
;; one, which ignores bits it does not know) stay correct with no format bump.  1 is
;; `:default` and 2 is `:monotonic`, matching `strength/rank-of`.  Like the premise bit,
;; the rank is a cache over the durable record and shares its residual: the flags word is
;; not crash-atomic (a 24-byte slot straddles a page ~0.6% of the time), so a torn flags
;; page can leave a stale bit or rank across a crash.  `reconcile-slot-flags!` closes it —
;; a **dirty** open walks the records and rewrites every slot whose flags disagree — and
;; until that open the record stays the truth, with a re-mark or a compaction repairing it
;; the same way.

(def ^:private flag-premise-known 0x1)
(def ^:private flag-premise       0x2)
(def ^:private strength-shift 2)
(def ^:private strength-mask  (bit-shift-left 0x3 strength-shift))  ; bits 2..3

(defn premise-flags
  "The `flags` word for a slot whose record is, or is not, a premise, carrying the
  premise's strength `rank` (0 when not a premise, or when the rank is unrecorded) in
  bits 2..3."
  (^long [premise?] (premise-flags premise? 0))
  (^long [premise? ^long rank]
   (if premise?
     (bit-or flag-premise-known flag-premise
             (bit-and strength-mask (bit-shift-left rank strength-shift)))
     flag-premise-known)))

(defn slot-premise
  "What `flags` says about its record: `true`, `false`, or **nil** for a slot that does
  not say — which is what sends a caller to the record itself."
  [^long flags]
  (when (pos? (bit-and flags flag-premise-known))
    (pos? (bit-and flags flag-premise))))

(defn slot-strength
  "The strength rank a premise slot carries in bits 2..3, or 0 when it carries none — a
  non-premise, or a slot older than the strength bits — which sends the caller to the
  record for the answer."
  ^long [^long flags]
  (bit-and 0x3 (unsigned-bit-shift-right flags strength-shift)))

(defn write-slot!
  "Write a slot for `id` — the 24 bytes packed in memory and written with **one
  positional channel write**, the mirror of `read-slot`: a `RandomAccessFile` is
  unbuffered, so a seek plus four primitive writes is five syscalls for 24 bytes.  A
  slot past the file's end grows it, and the gap is read back as unwritten
  (`read-slot`'s zero test)."
  [^RandomAccessFile idx-raf id offset length flags gen]
  (let [bb (java.nio.ByteBuffer/allocate slot-bytes)]
    (.putLong bb (long offset))
    (.putLong bb (long length))
    (.putInt  bb (unchecked-int flags))
    (.putInt  bb (unchecked-int gen))
    (.flip bb)
    (write-fully-at! (.getChannel idx-raf) bb (* (long id) slot-bytes))))

(defn- consecutive-runs
  "`sorted` (by id) split into maximal runs of **consecutive** ids.  A batch of records
  minted in order, or a dump whose handles are preserved, is one run."
  [sorted]
  (reduce (fn [runs slot]
            (let [run (peek runs)]
              (if (and run (= (long (first slot)) (inc (long (first (peek run))))))
                (conj (pop runs) (conj run slot))
                (conj runs [slot]))))
          [] sorted))

(defn write-slots!
  "Write many slots — each `[id offset length flags gen]` — as **one positional write per
  run of consecutive ids**, where `write-slot!` is one write per slot.

  A slot is 24 bytes at `id * 24`, so a run of consecutive handles is a contiguous range
  of the idx and a batch of them is one syscall rather than one apiece.  Handles are
  minted in order and a preserved dump numbers its records in order, so the common case
  is a single write for the whole batch; the runs are what keeps it correct when it is
  not.  Caller must hold the idx's write lock."
  [^RandomAccessFile idx-raf slots]
  (let [ch (.getChannel idx-raf)]
    (doseq [run (consecutive-runs (sort-by first slots))]
      (let [bb (java.nio.ByteBuffer/allocate (* slot-bytes (count run)))]
        (doseq [[_ offset length flags gen] run]
          (.putLong bb (long offset))
          (.putLong bb (long length))
          (.putInt  bb (unchecked-int flags))
          (.putInt  bb (unchecked-int gen)))
        (.flip bb)
        (write-fully-at! ch bb (* (long (first (first run))) slot-bytes))))))

(defn- slot-flags-consistent?
  "Would this `flags` word answer the same as the record — directly, or by falling back?
  A slot is consistent when its premise bit is silent or matches `premise?`, **and** its
  rank is unrecorded (0, which sends the reader to the record) or matches `rec-rank` on a
  premise.  Anything else — a bit or a non-zero rank that disagrees — is a torn flags page
  a later clean open would trust, so it is not consistent."
  [^long flags premise? ^long rec-rank]
  (let [sp (slot-premise flags)
        sr (slot-strength flags)]
    (and (or (nil? sp) (= sp (boolean premise?)))
         (or (zero? sr) (and premise? (= sr rec-rank))))))

(defn reconcile-slot-flags!
  "Rewrite `id`'s slot flags to match its record's premise-ness and strength `rank` when
  the two would answer differently — a torn flags page across a crash can leave a slot
  speaking a stale bit or rank.  Returns true if the slot was rewritten.  A slot that is
  silent, or already agrees (an unrecorded rank included, since that falls back to the
  record), is left untouched.  Only the flags word moves — offset/length/gen are written
  back unchanged — and the record is the durable truth, so this is a repair toward it,
  never a new fact: idempotent, and safe to interrupt, since the next dirty open repeats
  it."
  [^RandomAccessFile idx-raf ^long id premise? ^long rank]
  (when-let [slot (read-slot idx-raf id)]
    (when-not (slot-flags-consistent? (long (:flags slot)) premise? rank)
      (write-slot! idx-raf id (:offset slot) (:length slot)
                   (premise-flags (boolean premise?) rank) (:gen slot))
      true)))

(defn tombstone-slot!
  "Mark slot `id` as a tombstone (offset=-2, other fields zeroed)."
  [^RandomAccessFile idx-raf ^long id]
  (write-slot! idx-raf id tombstone-offset 0 0 0))

(defn max-slot-id
  "The highest slot id the idx file can address, or -1 if empty.  Stable across
  deletes (a tombstone keeps its slot), so `1 + max` never reuses a handle."
  ^long [^RandomAccessFile idx-raf]
  (let [len (.length idx-raf)]
    (if (zero? len) -1 (dec (quot len slot-bytes)))))

(defn slot-count
  "The number of fixed-width slots the idx file currently holds."
  ^long [^RandomAccessFile idx-raf]
  (quot (.length idx-raf) slot-bytes))

(defn truncate!
  "Truncate a log or idx RAF to empty and reposition at the start — the whole-file
  wipe `clear-*!` needs."
  [^RandomAccessFile raf]
  (.setLength raf 0)
  (.seek raf 0))

(defn scan-idx!
  "Walk the idx from the start, invoking `(on-slot id offset length flags)` for every
  live slot (not empty, tombstone, or zero-filled gap).  Reads in 96 KiB chunks (a
  per-id `read-slot` on a large idx pays one seek each); re-seeks per chunk so an
  `on-slot` that itself seeks `idx-raf` cannot derail the scan.

  The flags ride along because this walk is the only one an open makes: whatever a slot
  can answer without reading its record has to be answered here or not at all.

  `r`, when non-nil, is a `vaelii.impl.progress` reporter ticked with the slots each
  chunk covers, live or not."
  ([idx-raf on-slot] (scan-idx! idx-raf on-slot nil))
  ([^RandomAccessFile idx-raf on-slot r]
   (let [total       (.length idx-raf)
         chunk-slots 4096
         chunk-bytes (* slot-bytes chunk-slots)
         buf         (byte-array chunk-bytes)]
     (loop [base-id 0 pos 0]
       (when (< pos total)
         (.seek idx-raf pos)
         (let [to-read (int (min chunk-bytes (- total pos)))
               n       (.read idx-raf buf 0 to-read)]
           (when (pos? n)
             (let [bb (java.nio.ByteBuffer/wrap buf 0 n)]
               (loop [i 0 off 0]
                 (when (<= (+ off slot-bytes) n)
                   (let [offset (.getLong bb off)
                         length (.getLong bb (int (+ off 8)))]
                     (when (and (not= offset empty-offset)
                                (not= offset tombstone-offset)
                                (not (and (zero? offset) (zero? length))))
                       (on-slot (+ base-id i) offset length
                                (long (bit-and 0xffffffff (.getInt bb (int (+ off 16)))))))
                     (recur (inc i) (long (+ off slot-bytes)))))))
             (when r (progress/tick! r (quot n slot-bytes)))
             ;; Advance by the WHOLE SLOTS consumed, never by `n`.  The inner loop
             ;; refuses a partial trailing slot, so a read that is not a multiple of
             ;; `slot-bytes` leaves a remainder — and stepping `pos` past it while
             ;; stepping `base-id` by the slot count alone would start the next chunk
             ;; mid-slot and misattribute every id from there on, silently.  `read` may
             ;; return short at any point; today's chunk size only makes that rare.  A
             ;; read too short to hold one slot ends the walk, which is what the inner
             ;; loop already says about a partial slot at the end of the file.
             (let [used (* slot-bytes (quot n slot-bytes))]
               (when (pos? used)
                 (recur (long (+ base-id (quot n slot-bytes)))
                        (long (+ pos used))))))))))))

(defn read-nippy-file
  "Read a whole-file nippy value, returning `default` when the file is missing,
  empty, or unreadable (a rare torn blob thaws to default + a warning rather than
  throwing — these blobs hold reconstructible metadata).

  **The file's bytes first, then the thaw over those.**  A torn blob is a prefix of one
  `write-nippy-atomic!` wrote, so every count it holds is one the writer wrote, and the
  thaw ends on the missing tail.  Bytes that are no prefix of a nippy stream can decode a
  count of any size; the `OutOfMemoryError` its allocation raises is rethrown, as every
  `VirtualMachineError` is, since a default read after a heap failure would hand a caller
  `{:seq 1}` for its counters.  The thaw is `thaw-from-in!`, because
  `write-nippy-atomic!` writes with `freeze-to-out!`: a headerless typed stream, not a
  `freeze`d array."
  ([path] (read-nippy-file path nil))
  ([^String path default]
   (let [f (File. path)]
     (if (and (.exists f) (pos? (.length f)))
       (try
         (let [bs (byte-array (.length f))]
           (with-open [in (DataInputStream.
                           (BufferedInputStream. (FileInputStream. f)))]
             (.readFully in bs))
           (with-open [in (DataInputStream. (ByteArrayInputStream. bs))]
             (safe/thaw-from-in! in)))
         (catch VirtualMachineError e (throw e))
         (catch Throwable t
           (trove/log! {:level :warn
                        :msg (str "disk.files: unreadable nippy blob " path
                                  " (" (.getMessage t) ") — falling back to default")})
           default))
       default))))

(defn- frame-length-at
  "The payload length of the frame whose prefix starts at `pos`, or nil where
  `log-tail-offset`'s length chain ends: fewer than four bytes remain, the prefix is
  non-positive, or the payload it promises runs past `len`.  Leaves the file pointer just
  past the prefix."
  [^RandomAccessFile log-raf ^long pos ^long len]
  (when (<= (+ pos 4) len)
    (.seek log-raf pos)
    (let [n (long (.readInt log-raf))]
      (when (and (pos? n) (<= (+ pos 4 n) len))
        n))))

(defn log-tail-offset
  "The truncation point after a torn trailing write, computed from the frame **lengths**
  alone — read a prefix, skip `n`, repeat — without thawing anything.

  This is `scan-log`'s return value without decoding the log, and decoding is the whole
  cost: finding one offset in a large log means thawing every frame ahead of it, whose
  values are then discarded, and it makes the open path depend on whether this build can
  decode what is in the log.  That dependency is not hypothetical — a record class rename
  turned one unreadable store into an exception per record, thrown from a scan whose
  only question was *how long is the log*.

  **Nothing is thawed, deliberately, and the length chain is enough.**  A frame is
  appended before the idx slot that points at it, so a torn tail frame is one nothing
  references, and the idx is the authority on what is live.  Truncating the tail is
  therefore tidiness rather than repair, and `validate-idx-tail!` — which still runs —
  is what actually reconciles a slot against a log that lost its end.  A frame whose
  payload is damaged but whose length is intact stays.  In a record log it fails (if
  anything references it at all) at that one record.  In a log the open reads whole — the
  token dictionary, the index's `kv.log`, the operation log — `scan-log` refuses it by
  name (`:damaged-frame`) unless it is the chain's last frame.  The alternative is worse
  in exactly the case that bit us: thawing to decide truncation means a build that cannot
  decode *deletes the log it cannot read*.

  A **non-positive** length terminates the walk rather than being stepped over.  A frame
  payload is a nippy value and is never empty, so a zero can only be space that was never
  written — and on a filesystem that zero-fills past a tear, stepping over zeros four
  bytes at a time would walk to EOF and pronounce the whole torn tail intact.

  The prefixes are read through a **read buffer** rather than one `seek`+`readInt` apiece: a
  `RandomAccessFile` is unbuffered, so per-frame reads make this syscall-bound (measured
  at 5.8M frames: 5.4s that way, 23ms this way). The buffer is filled by *positional*
  channel reads, which name the offset and never touch the shared file pointer — so this
  neither disturbs a concurrent append nor needs the kind lock."
  ^long [^RandomAccessFile log-raf]
  (let [ch  (.getChannel log-raf)
        len (.length log-raf)
        buf (java.nio.ByteBuffer/allocate 65536)]
    ;; `base` is the file offset of buf[0] and `limit` its valid byte count; -1 = unfilled
    (loop [pos 0, base -1, limit 0]
      (cond
        (> (+ pos 4) len) pos

        ;; the next prefix is not wholly inside the read buffer — refill from `pos`
        (or (neg? base) (< pos base) (> (+ pos 4) (+ base (long limit))))
        (let [_ (.clear buf)
              n (.read ch buf pos)]
          (if (< n 4) pos (recur pos pos n)))

        :else
        (let [n         (.getInt buf (int (- pos (long base))))   ; absolute, big-endian
              frame-end (+ pos 4 (long n))]
          (if (or (not (pos? n)) (> frame-end len))
            pos
            (recur (long frame-end) base limit)))))))

(defn scan-log
  "Scan an append-only log, calling `(f index value)` for each frame in order.  Returns
  the byte offset of the first byte past the last frame read — the truncation point
  after a torn trailing write.

  The walk follows the same length chain `log-tail-offset` walks, and stops where that
  chain ends.  A frame inside the chain whose payload does not thaw is one of two things,
  told apart by what follows it:

  - **The chain's last frame** is read as a torn tail: its length prefix landed and its
    payload did not.  The walk stops at its offset, logs it, and the caller truncates it
    exactly as it truncates a torn prefix.
  - **Any earlier frame** is damage inside the log, and the walk throws `:damaged-frame`
    naming `path`, the offset and the frame's index, with the thaw's exception as the
    cause.  Stopping there instead would drop every frame after it as though the log had
    ended, and a caller that rebuilds state from the log would lose all of them.

  A `VirtualMachineError` (an `OutOfMemoryError` above all) is rethrown as itself: it
  says the JVM could not finish the thaw, not that the frame is bad.

  A caller that wants only the truncation offset wants `log-tail-offset`, which reads the
  length prefixes and skips the decoding entirely.

  `r`, when non-nil, is a `vaelii.impl.progress` reporter ticked with the bytes each
  frame takes, its length prefix included."
  (^long [log-raf f] (scan-log log-raf nil f nil))
  (^long [log-raf path f] (scan-log log-raf path f nil))
  (^long [^RandomAccessFile log-raf path f r]
   (let [len (.length log-raf)]
     (loop [pos 0 idx 0]
       (if-let [n (frame-length-at log-raf pos len)]
         (let [frame-end (+ pos 4 (long n))
               bs        (byte-array n)
               _         (.readFully log-raf bs)
               ;; a one-element vector, so a frame that thaws to nil is still a value
               got       (try
                           [(thaw-bytes bs)]
                           (catch VirtualMachineError e (throw e))
                           (catch Throwable t
                             (when (frame-length-at log-raf frame-end len)
                               (throw (ex-info (str "frame " idx " of " (or path "the log")
                                                    " at byte offset " pos " does not decode,"
                                                    " and the log holds further frames after"
                                                    " it — damage inside the log, not a torn"
                                                    " tail (" (.getMessage t) ")")
                                               {:type :damaged-frame :path path :offset pos
                                                :frame idx :length n}
                                               t)))
                             (trove/log! {:level :warn :id ::torn-last-frame
                                          :msg (str "disk.files: the last frame of "
                                                    (or path "a log") ", at byte offset " pos
                                                    ", does not decode (" (.getMessage t)
                                                    ") — read as a torn tail")})
                             nil))]
           (if got
             (do (f idx (first got))
                 (when r (progress/tick! r (- frame-end pos)))
                 (recur frame-end (inc idx)))
             pos))
         pos)))))

(defn truncate-log!
  "Truncate the log to `new-len` — used after `scan-log` detects a torn tail frame."
  [^RandomAccessFile log-raf ^long new-len]
  (when (< new-len (.length log-raf))
    (.setLength log-raf new-len)
    (.seek log-raf new-len)))

(defn validate-idx-tail!
  "Tombstone every idx slot whose frame (offset + 4 + length) extends past the log's
  current length — a torn trailing write where the idx page was persisted but the log
  pages were not.  Returns the count repaired.

  **This catches a slot that outruns the log, and only that.**  A slot is 24 bytes and a
  page is 4096, which 24 does not divide, so about 0.6% of slots straddle a page boundary
  — and a crash can persist one of those pages and not the other, leaving a slot spliced
  from two different writes.  A splice whose offset and length still land inside the log
  passes this check and surfaces later as a thaw failure on that one handle
  (`:type :malformed-record`, `vaelii.impl.disk.codec`), which is a read that refuses
  rather than a wrong record.  Detecting the splice itself would take a per-slot checksum,
  which the 24-byte slot has no room for; the `gen` word is reserved and written as 0.

  Rides `scan-idx!`'s chunked walk, which reads the whole idx — a per-id `read-slot`
  would be a seek and a buffer allocation per slot where the chunked read pays one per
  4096 — so every live slot is tested and *tail* names where the damage can be rather
  than a range this bounds the walk to."
  ^long [^RandomAccessFile idx-raf ^RandomAccessFile log-raf]
  (let [log-len  (.length log-raf)
        repaired (volatile! 0)]
    (scan-idx! idx-raf (fn [id offset length _flags]
                         (when (> (+ (long offset) 4 (long length)) log-len)
                           (tombstone-slot! idx-raf id)
                           (vswap! repaired inc))))
    @repaired))

;; ---- crash-safe compaction ----------------------------------------------
;; A log is rewritten (never edited in place) with only its live frames into a temp,
;; the temp is fsynced, a commit marker is fsynced, then the temp replaces the
;; original.  The marker's existence is the atomic commit point: if a crash lands
;; after it, `recover-compaction!` replays the fsynced temps; before it, the
;; originals are still authoritative and the orphan temps are dropped.

(defn compact-temp-paths
  "Sibling temp + commit-marker paths for a crash-safe compaction of `targets` — the files
  rewritten together and installed together.  A record kind hands in its (log, idx) pair;
  the KV backend's write-ahead log is one file and hands in itself.  **One marker governs
  the set**, keyed off the first target, which is what makes the install atomic across
  however many files it covers.

  Returns `{:temps [[target temp] …] :marker marker}`, the temps in the order they were
  named — so a caller that installs them individually takes them apart, and the three
  helpers below that treat them as a set do not have to know how many there are."
  [& targets]
  {:temps  (mapv (fn [^String t] [t (str t ".compact")]) targets)
   :marker (str ^String (first targets) ".compact-commit")})

(defn- copy-into-channel!
  "Truncate `dst` to 0 and copy all of `src-path` into it from position 0.

  **A transfer that moves nothing with bytes outstanding throws.**  `transferFrom` is
  documented as free to return 0, and this is the post-marker install — the temp is the
  only complete copy of the log or idx at that moment, so stopping quietly on a short
  transfer would leave a *truncated* file in place of the original and call it done.  A
  throw is what the compaction paths are written for: before the marker they drop the
  temps, after it they retry and then mark the store failed."
  [^FileChannel dst ^String src-path]
  (with-open [in (FileInputStream. src-path)]
    (let [src   (.getChannel in)
          total (.size src)]
      (.truncate dst 0)
      (loop [pos 0]
        (when (< pos total)
          (let [n (.transferFrom dst src pos (- total pos))]
            (when-not (pos? n)
              (throw (ex-info (str "copy of " src-path " stalled at " pos " of " total
                                   " bytes")
                              {:type :short-transfer :path src-path
                               :copied pos :total total})))
            (recur (+ pos n))))))))

(defn replay-temp-onto-raf!
  "Install the freshly-built `tmp-path` over an already-open RAF: truncate, copy the
  temp's bytes in, fsync, leave positioned at EOF.  Used by the live compactor."
  [^RandomAccessFile target ^String tmp-path]
  (copy-into-channel! (.getChannel target) tmp-path)
  (.force (.getChannel target) true)
  (.seek target (.length target)))

(defn- replay-temp-onto-path!
  "Like `replay-temp-onto-raf!` but opens its own RAF — for recovery, before the store
  opens the file."
  [^String target-path ^String tmp-path]
  (with-open [raf (RandomAccessFile. target-path "rw")]
    (copy-into-channel! (.getChannel raf) tmp-path)
    (.force (.getChannel raf) true)))

(defn write-commit-marker!
  "Atomically create the compaction commit marker and fsync it (and its dir).  Its
  existence is the commit point."
  [^String marker info]
  (with-open [fos (FileOutputStream. marker)]
    (let [out (DataOutputStream. (BufferedOutputStream. fos))]
      (nippy/freeze-to-out! out info)
      (.flush out)
      (.sync (.getFD fos))))
  (fsync-dir! marker))

(defn delete-compact-temps!
  "Remove the commit marker then every temp in `temps` (marker first, so a crash
  mid-cleanup can't leave a marker without its temps).  Idempotent.

  The fsync is what makes the *removal* durable, so it is owed only when a directory
  entry actually went away — `.delete` answers that, and the common call finds nothing
  to delete.  `clear-records!` runs this per kind on every wipe, so an unconditional
  fsync would charge a whole-store flush per kind to a wipe that had no compaction in
  flight."
  [^String marker temps]
  (let [m (.delete (File. marker))
        d (reduce (fn [acc [_ ^String tmp]] (or (.delete (File. tmp)) acc)) false temps)]
    (when (or m d) (fsync-dir! marker))))

(defn recover-compaction!
  "Finish or discard a crash-interrupted compaction of `targets`, BEFORE they are opened
  for normal use.  Returns :replayed, :discarded-incomplete, or :none.  Idempotent.

  **The marker plus a complete set of temps is the commit**, whether the set is a record
  kind's (log, idx) pair or the KV backend's single write-ahead log: the originals stay
  authoritative until every temp is installed, so a crash before the marker keeps them and
  drops the orphan temps, and one after it replays what the marker vouches for."
  [& targets]
  (let [{:keys [temps marker]} (apply compact-temp-paths targets)
        marker?  (.exists (File. ^String marker))
        present  (filterv (fn [[_ ^String tmp]] (.exists (File. tmp))) temps)]
    (cond
      (and marker? (= (count present) (count temps)))
      (do
        (trove/log! {:level :warn
                     :msg (str "disk.files: finishing interrupted compaction of "
                               (first targets))})
        (doseq [[^String target ^String tmp] temps] (replay-temp-onto-path! target tmp))
        (delete-compact-temps! marker temps)
        :replayed)

      marker?
      ;; marker present but a temp is missing — deeper damage than we can repair; keep
      ;; the originals (validate-idx-tail! handles them) and clear the partial state.
      (do
        (trove/log! {:level :error
                     :msg (str "disk.files: compaction marker for " (first targets)
                               " present but a .compact temp is missing — keeping originals")})
        (delete-compact-temps! marker temps)
        :discarded-incomplete)

      (seq present)
      (do (doseq [[_ ^String tmp] present] (.delete (File. tmp)))
          :discarded-incomplete)

      :else :none)))

;; ---- unclean-shutdown marker --------------------------------------------

(defn dirty-marker-path ^String [root] (str root "/dirty.marker"))

(defn token-log-present?
  "True when `root` holds a `tokens.log` at all, an **empty** one included — so a store
  must open the dictionary to decode its frames, whether or not it still writes tokenized
  ones.  Emptiness is not absence: a `tokens.log` a crash tore to zero bytes leaves the
  sentexes log's tokenized frames citing ids no dictionary holds, and opening the (empty)
  dictionary is what turns each such frame into a typed `:damaged-dictionary` tombstone on
  `rebuild-premises!`'s walk.  Opening the dictionary only at a non-empty length would
  leave `open-record-store` with a nil dictionary and the tokenized decoder dereferencing
  it."
  [root]
  (.exists (File. (str root) "tokens.log")))

(defn dirty-marker-present?
  "True when a previous session's dirty marker survives — that session never ran a
  clean close!, so the open path should run its crash checks."
  [root]
  (.exists (File. (dirty-marker-path root))))

(defn create-dirty-marker!
  "Durably drop the dirty marker (fsync the file AND its dir)."
  [root]
  (let [p (dirty-marker-path root)]
    (with-open [fos (FileOutputStream. p)]
      (.write fos (.getBytes (str (System/currentTimeMillis)) "UTF-8"))
      (.sync (.getFD fos)))
    (fsync-dir! p)))

(defn remove-dirty-marker!
  "Remove the dirty marker after a clean fsync+close.  Idempotent."
  [root]
  (.delete (File. (dirty-marker-path root)))
  (fsync-dir! (dirty-marker-path root)))

;; ---- clean-shutdown log lengths -----------------------------------------
;; A clean close records how long each log was when it fsynced.  On the next open a log
;; whose length still matches needs no tail scan: nothing was appended after the fsync,
;; so there is no torn tail to find.
;;
;; The check is **self-validating**, which is what makes it safe to trust.  A crash
;; leaves the marker describing an earlier, shorter log, and the mismatch sends the open
;; down the full scan; so does a marker that is absent, unreadable, or claims a log
;; longer than exists.  `remove-clean-marker!` on open narrows it further, so the marker
;; exists only while nothing holds the store — a stale one cannot outlive one session.
;;
;; The lengths are a **hint and the bytes are the truth**, the same discipline the
;; counters blob follows: any disagreement resolves toward the file.

(defn clean-marker-path ^String [root] (str root "/clean.nippy"))

(defn write-clean-marker!
  "Durably record `lengths` (a `name -> log length` map) as this session's clean close.
  Call after the final fsync and before closing, so the lengths are the durable ones."
  [root lengths]
  (write-nippy-atomic! (clean-marker-path root) {:logs lengths}))

(defn read-clean-marker
  "The `name -> length` map a clean close left, or nil (absent or unreadable)."
  [root]
  (:logs (read-nippy-file (clean-marker-path root) nil)))

(defn remove-clean-marker!
  "Drop the clean marker — called on open, so it never describes a store in use."
  [root]
  (.delete (File. (clean-marker-path root)))
  (fsync-dir! (clean-marker-path root)))

(defn log-tail-offset-from
  "The truncation offset for `log-raf`, skipping the walk entirely when `clean-length`
  (this log's entry in the clean marker) equals its current length.  Returns
  `[offset scanned?]` so a caller can report whether the fast path was taken."
  [^RandomAccessFile log-raf clean-length]
  (let [len (.length log-raf)]
    (if (and (integer? clean-length) (= (long clean-length) len))
      [len false]
      [(log-tail-offset log-raf) true])))
