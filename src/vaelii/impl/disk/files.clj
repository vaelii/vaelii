;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.files
  "Low-level file primitives for the on-disk backend (docs/storage.md).

  - Append-only `.log` files hold length-prefixed nippy frames, `[len: i32 big-endian]
    [nippy-bytes]`. The offset `append-record!` returns points at the len prefix.
  - `.idx` files are fixed-width arrays of 24-byte slots indexed by id:
    bytes  0..7  offset (i64, -1 = empty, -2 = tombstone)
    bytes  8..15 length (i64)
    bytes 16..19 flags (u32; bit 0 = the premise bit is meaningful, bit 1 = premise, bits
                 2..3 = a premise's strength rank, 0 when unrecorded)
    bytes 20..23 gen (u32, reserved, written as 0)
    A slot is read in one positional channel read; writes overwrite the slot in place.
  - `.nippy` files hold whole-blob metadata (counters, the premise set), rewritten
    atomically by `write-nippy-atomic!`.

  A seek then read or write on a `RandomAccessFile` uses its single shared file pointer, so
  any access to a store's live RAF holds the owning kind lock. The read primitives
  (`read-slot`, `read-record`, `read-record-sized`) are positional `FileChannel` reads, which
  never touch the pointer.

  Frames freeze under the nippy compressor named by `vaelii.disk.compress` (`lz4` | `zstd` |
  `none`, default none); nippy reads the compressor id from each frame header.
  `vaelii.disk.fsync=dsync` opens logs `rwd` so every append is synchronous; the default
  leaves fsync to the durability daemon."
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
  "The most an EDN manifest may hold (a dump's `meta.edn` and `index.edn`, a store's
  `format.edn`, an index directory's `layout.edn` and `records.edn`, a belief image's
  `manifest.edn`, a corpus's `report.edn`, a machine's `catalog.edn`). Each is the first
  thing read about a directory nobody has promised anything about, so the read is bounded."
  (* 1024 1024))

(defn read-edn-manifest
  "The EDN manifest in `f`, read under `manifest-bytes`, or a refusal (`:manifest-too-large`)
  naming the file and the bound. The bound is on the bytes read, not on `File.length`, which
  answers 0 for a FIFO. Content the EDN reader cannot parse is refused as
  `:malformed-manifest`; the caller decides which refusal means a broken KB."
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
  "Best-effort fsync of the directory holding `path`, so a file's creation or deletion is
  durable. Swallowed on filesystems that reject directory fsync, and warned once: a
  commit marker's directory entry is the atomic commit point of a compaction."
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
  "Check the store directory `root` against its `format.edn` sentinel: a known version is
  ok, an unknown one throws, and a missing sentinel is written with the current version. A
  damaged sentinel is refused (`:unreadable-store`), not rewritten, and one past
  `manifest-bytes` is refused as `:manifest-too-large`."
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
  (`kv/index-layout-version`): `:current` when the version matches, `:stale` when it does
  not (an absent sentinel over a `populated?` log, a damaged one, and one past
  `manifest-bytes` included), and `:unwritten` for a fresh, empty directory. `:stale` is the
  caller's cue to clear the index, rebuild it from the records and `write-index-layout!`.
  This reads and never writes, since a base mounted under `:base` may not be written to."
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

(def ^:private load-key-file "load-key.edn")

(defn recorded-load-key
  "The load key recorded in the store directory `root` (`load-key.edn`), or nil when it
  records none or the file does not read as a manifest."
  [root]
  (let [file (File. ^String (str root) ^String load-key-file)]
    (when (.exists file)
      (try (read-edn-manifest file)
           (catch clojure.lang.ExceptionInfo _ nil)))))

(defn write-load-key!
  "Record `m` as the load key of the store directory `root`."
  [root m]
  (spit-manifest! (str root "/" load-key-file) m)
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
;; call (a thread interrupt closes a `FileChannel` it is blocked in, and with it the
;; owning `RandomAccessFile`) is closed for every later call. Either that or an I/O
;; failure on a write makes the store answer every later call with one typed refusal.
;; The latch is an atom per store holding `{:reason :path :cause}`; the first fault wins,
;; and a reopen is the only way out (docs/storage.md, "A store that stops").

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
  "Append `buf` (one or more complete frames, already packed) at the log's end and return the
  offset it landed at. All or nothing: a write that fails partway sets the log back to its
  pre-write length before the failure travels, so the length-chain walk (`log-tail-offset`)
  never steps into the middle of a later frame. Caller must hold the log's write lock."
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
  "Append every value in `values` to the log, each its own frame, as one write
  (`append-record-sized!`'s batch form). Returns a vector of `[offset payload-length]` in
  input order, the pair an idx slot records. All or nothing for the batch
  (`append-bytes!`). Caller must hold the log's write lock."
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
;; Bit 0 says the flags word speaks at all and bit 1 is what it says, because a slot
;; written before the bits existed reads as 0, and 0 must mean unknown, not "not a
;; premise". Bits 2..3 carry a premise's strength rank (1 `:default`, 2 `:monotonic`,
;; matching `strength/rank-of`; 0 means unrecorded), so `premise-strength` on `recover`
;; answers off the slot the open walk already reads. An older build's slots, and an older
;; build reading a newer one, stay correct with no format bump. The flags word is a cache
;; over the durable record and is not crash-atomic (a 24-byte slot straddles a page ~0.6%
;; of the time), so `reconcile-slot-flags!` rewrites every slot whose flags disagree on a
;; dirty open, and until then the record is the truth.

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
  "Walk the idx from the start, invoking `(on-slot id offset length flags)` for every live
  slot (not empty, tombstone or zero-filled gap), in 96 KiB chunks. The flags ride along
  because an open's walk is the only one that can answer what a slot knows without reading
  its record. `r`, when non-nil, is a `vaelii.impl.progress` reporter ticked with the slots
  each chunk covers."
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
             ;; Advance by the whole slots consumed, never by `n`: a read that is not a
             ;; multiple of `slot-bytes` leaves a remainder, and stepping `pos` past it
             ;; while stepping `base-id` by the slot count would start the next chunk
             ;; mid-slot and misattribute every later id. A read too short to hold one
             ;; slot ends the walk.
             (let [used (* slot-bytes (quot n slot-bytes))]
               (when (pos? used)
                 (recur (long (+ base-id (quot n slot-bytes)))
                        (long (+ pos used))))))))))))

(defn read-nippy-file
  "Read a whole-file nippy value, returning `default` when the file is missing, empty or
  unreadable (a torn blob thaws to default and a warning). The file's bytes are read first and
  thawed with `thaw-from-in!`, because `write-nippy-atomic!` writes a headerless typed stream.
  A `VirtualMachineError` is rethrown as itself, so a heap failure never returns `default`."
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

(def ^:private load-stated-file "load-stated.nippy")

(defn recorded-load-stated
  "The handle sets the load key's sources stated, one per source in load order, recorded in
  the store directory `root` under the records fingerprint `fp`; nil when `root` records
  none under `fp`.  A nippy file, since a layer's statements outgrow `manifest-bytes`."
  [root fp]
  (let [m (read-nippy-file (str root "/" load-stated-file) nil)]
    (when (and (map? m) (= fp (:records m)))
      (mapv #(some->> % (into #{})) (:handles m)))))

(defn write-load-stated!
  "Record `handles`, a seq of handle sets or nils, under the records fingerprint `fp` in
  the store directory `root`."
  [root fp handles]
  (write-nippy-atomic! (str root "/" load-stated-file)
                       {:records fp :handles (mapv #(some->> % sort vec) handles)})
  nil)

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
  "The truncation point after a torn trailing write, computed from the frame lengths alone
  (read a prefix, skip `n`, repeat) without thawing anything: `scan-log`'s return value
  without decoding the log. A frame is appended before the idx slot that points at it, so
  truncating the tail is tidiness, and `validate-idx-tail!` reconciles a slot against a log
  that lost its end. A non-positive length terminates the walk, since a payload is never
  empty and a zero is space never written. The prefixes are read through a buffer by
  positional channel reads, which never touch the shared file pointer, so this needs no kind
  lock. See docs/storage.md, \"Durability + crash-safety\"."
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
  "Scan an append-only log, calling `(f index value)` for each frame in order. Returns the
  byte offset of the first byte past the last frame read, the truncation point after a torn
  trailing write. The walk follows `log-tail-offset`'s length chain. A frame whose payload
  does not thaw is a torn tail when it is the chain's last (the walk stops at its offset and
  logs it), and damage otherwise: the walk throws `:damaged-frame` naming `path`, the offset
  and the frame's index, with the thaw's exception as cause. A `VirtualMachineError` is
  rethrown as itself. `r`, when non-nil, is a progress reporter ticked with the bytes each
  frame takes."
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
  "Tombstone every idx slot whose frame (offset + 4 + length) extends past the log's current
  length, a torn trailing write where the idx page persisted and the log pages did not.
  Returns the count repaired. It catches a slot that outruns the log and only that: a slot
  spliced from two pages that still lands inside the log surfaces later as a thaw failure
  on that handle (`:type :malformed-record`), since the 24-byte slot has no room for a
  checksum. Rides `scan-idx!`'s chunked walk, so every live slot is tested."
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
  "Sibling temp and commit-marker paths for a crash-safe compaction of `targets`, the files
  rewritten and installed together (a record kind's (log, idx) pair, or the KV backend's one
  log). One marker governs the set, keyed off the first target. Returns `{:temps [[target
  temp] …] :marker marker}` in the order named."
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

(defn delete-tree!
  "Delete `f` and, when it is a directory and not a link to one, what it holds."
  [^File f]
  (when (and (.isDirectory f) (not (java.nio.file.Files/isSymbolicLink (.toPath f))))
    (run! delete-tree! (.listFiles f)))
  (.delete f))

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
;; A clean close records how long each log was when it fsynced. An open whose log length
;; still matches needs no tail scan. The check validates itself: a crash leaves a marker
;; describing a shorter log, and a marker that is absent, unreadable or claims a log longer
;; than exists sends the open down the full scan. `remove-clean-marker!` on open keeps a
;; stale marker from outliving one session. The lengths are a hint and the bytes are the
;; truth.

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
