;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.frames
  "The chunked **nippy stream** framing every serialization in the engine writes to a
  file or a sink — one home, so the export dump, the import reader and the snapshot sink
  cannot drift.

  A chunked stream is a run of `[int32 length][compressed chunk]`, each chunk an
  independent compression window over back-to-back nippy frames.  Constant memory on both
  sides: the writer holds one chunk and never the corpus, and the reader thaws a chunk on
  demand and drops it.  A *frame* is whatever the caller freezes — a record's field map, an
  index `[key value]` pair, a JTMS `[handle label]` pair — this namespace neither reads a
  frame nor cares what one is.

  **Why it is its own namespace and not `export`'s private helper.**  Three callers write
  and read this format — `vaelii.impl.io.export` (the dump), `vaelii.impl.io.import` (the
  reader) and `vaelii.impl.io.snapshot` (the index image) — and the snapshot sink
  is meant to be *a thin adapter over this framing, not a second copy of it*.  A second
  copy is exactly the drift a shared projection was created to avoid one layer up: two
  writers that agree today and diverge on the next compression tweak.  So the framing lives
  once, here, and the container-specific concerns (what a dump's `meta.edn` records, an
  image's manifest) stay with each caller.  The dump's stream **names** are not one of
  those concerns: which streams exist and what each is called is the layout the writer
  and the reader must agree on — a second copy is the same drift one level down — so the
  names live here too, beside the framing they name (`meta-file` and its six siblings
  below).

  The legacy single-window reader (`read-window-seq`) is kept for a v4/v5 foreign dump that
  wrote one compression window over the whole file; the engine's own dumps have been chunked
  since v6."
  (:require [clojure.java.io :as io]
            [taoensso.nippy :as nippy]
            [vaelii.impl.io.thaw :as safe])
  (:import (java.io BufferedInputStream BufferedOutputStream ByteArrayInputStream
                    ByteArrayOutputStream DataInputStream DataOutputStream
                    EOFException InputStream OutputStream)
           (java.lang.reflect Constructor)
           (java.util.zip GZIPInputStream GZIPOutputStream)
           (org.tukaani.xz LZMA2Options XZInputStream XZOutputStream)))

;;; ── the dump's on-disk layout ─────────────────────────────────────────
;;; One home for the stream names the export writer and the import reader share, so the
;;; two halves of the round trip cannot drift: a rename on the write side alone would
;;; produce a dump the reader reports as *missing* rather than misnamed, and the
;;; discovery moment would be a restore.  `round_trip_test` pins the literal spellings:
;;; the layout is a frozen wire contract, so a change here is a format version.

(def meta-file
  "The dump's manifest — what `vaelii.impl.io.export` writes about the dump."
  "meta.edn")
(def sentex-file
  "The sentex record stream."
  "sentexes.nippy.stream")
(def justification-file
  "The justification record stream."
  "justifications.nippy.stream")
(def provenance-file
  "The `[handle provenance-map]` stream."
  "provenance.nippy.stream")
(def index-dir
  "The subdirectory a `:records+index` dump carries the index cache in."
  "index")
(def index-entry-file
  "The index `[key value]` entry stream, inside `index-dir`."
  "entries.nippy.stream")
(def index-meta-file
  "The index cache's own manifest, inside `index-dir`."
  "index.edn")

;;; ── writing ───────────────────────────────────────────────────────────

(def ^:private xz-dict-bytes
  "The LZMA2 dictionary an `:xz` chunk is compressed against.

  A chunk is its own compression window, so the dictionary can never fill past the chunk
  — and `LZMA2Options`'s default is a preset-6 8 MiB one, against a default 10,000-frame
  chunk that measures about 1 MB.  Sizing it to the chunk adds no work and saves the
  difference: over a 34k-sentex dump's sentex stream the compressed bytes are **identical**
  from 8 MiB down to 1 MiB (245,816 either way, in the same time), while the encoder's
  working set falls from 93 MB to 12 MB.  This is that with headroom: a **2 MiB**
  dictionary, whose encoder allocates about 24 MB (`vaelii.impl.io.export` quotes that
  figure, so the two move together).  A caller
  who raises `:chunk-size` past it loses only the matches a window wider than this would
  have found."
  (* 2 1024 1024))

(defn- wrap-output
  "The compressing wrapper for one chunk, matching the stream's `:compression`.  Each
  chunk is its own container — closing the wrapper writes the codec's trailer before
  the chunk's length is known, which is what lets a reader decompress any one chunk
  without the rest.  So an `:xz` stream allocates **an encoder per chunk** rather than one
  for the whole file; `xz-dict-bytes` is what keeps that a small allocation.

  **A codec this cannot write is refused, not written flat.**  The compression a sink
  is given rides the manifest it commits (`vaelii.impl.io.snapshot`), so a value that
  fell through to the bare stream would leave plain nippy bytes under a manifest naming
  a codec — and `wrap-input`, which refuses the same value, would then fail to read back
  a file this reported as written.  `:zstd` is the live case: the reader accepts a dump
  some other tool wrote in it and nothing here writes it."
  ^OutputStream [^OutputStream out compression]
  (case compression
    :gzip       (GZIPOutputStream. out)
    :xz         (XZOutputStream. out (doto (LZMA2Options.)
                                       (.setDictSize (int xz-dict-bytes))))
    (:none nil) out
    (throw (ex-info (str "cannot write compression " compression
                         " — a stream is written :gzip, :xz or :none")
                    {:type :unsupported-compression :compression compression}))))

(defn write-frames!
  "Write `frames` into `file` in the chunked layout, `chunk-size` frames per chunk.
  Returns how many frames were written.

  Lazy by construction and by contract: one chunk is realized, frozen, compressed and
  flushed before the next is asked for, so the writer's footprint is a chunk rather
  than a corpus.  `:on-chunk` is called with the running frame count at each chunk
  boundary — the progress hook, and the point a caller's callback can throw to cancel."
  [file frames {:keys [compression chunk-size on-chunk]}]
  (let [written (volatile! 0)]
    (with-open [out (io/output-stream (io/file file))
                raw (DataOutputStream. (BufferedOutputStream. out))]
      (doseq [chunk (partition-all chunk-size frames)]
        (let [baos (ByteArrayOutputStream.)]
          (with-open [cout (DataOutputStream. (wrap-output baos compression))]
            (doseq [frame chunk] (nippy/freeze-to-out! cout frame)))
          (let [^bytes bs (.toByteArray baos)]
            (.writeInt raw (alength bs))
            (.write raw bs 0 (alength bs))))
        (let [n (vswap! written + (count chunk))]
          (when on-chunk (on-chunk n)))))
    @written))

;;; ── reading ───────────────────────────────────────────────────────────

(defn- reflective-input
  "Wrap `in` in the input stream named by `class-name` via its `(InputStream)`
  constructor.  A codec here is one a dump may *arrive* in and this engine does not write,
  so it is resolved reflectively: the dump imports iff the library is on the classpath,
  and a clear error names the missing dep otherwise.  **`:zstd` is the only one**, and so
  the only codec whose readability depends on what a build happens to carry — `:gzip`,
  `:none` and `:xz` are all written here, from imported classes, and read back from the
  same ones."
  ^InputStream [^String class-name ^InputStream in]
  (try
    (let [k    (Class/forName class-name)
          ctor (.getConstructor k (into-array Class [InputStream]))
          ^Constructor ctor ctor]
      (cast InputStream (.newInstance ctor (object-array [in]))))
    (catch ClassNotFoundException _
      (throw (ex-info (str "compression codec not on the classpath: " class-name
                           " — add the dependency, or re-export the dump with :gzip / :none")
                      {:type :unsupported-compression :codec class-name})))))

(defn- wrap-input
  "The un-compression wrapper for a stream, matching the export's `:compression`."
  ^InputStream [^InputStream in compression]
  (case compression
    :gzip       (GZIPInputStream. in)
    (:none nil) in
    :xz         (XZInputStream. in)
    :zstd       (reflective-input "io.airlift.compress.zstd.ZstdInputStream" in)
    (throw (ex-info (str "unknown compression " (pr-str compression)
                         " — a dump is read :gzip, :xz, :zstd or :none")
                    {:type :unsupported-compression :compression compression}))))

(defn- wrap-file-input
  "`file`'s bytes under `compression`'s wrapper — with the file **closed** when the
  wrapper refuses them.

  The acquisition chain is the reason this is not written inline: `wrap-input` throws on a
  codec this build cannot read, and `GZIPInputStream`'s own constructor throws on a
  section whose first bytes are not gzip — a dump whose `meta.edn` names a compression its
  payload does not carry, which is exactly the dump a reader meets.  Either throw out of a
  nested constructor call leaves the descriptor this line opened with nothing holding a
  reference to it and nothing that will close it."
  ^InputStream [file compression]
  (let [raw (io/input-stream (io/file file))]
    (try
      (wrap-input raw compression)
      (catch Throwable t
        (try (.close raw) (catch Throwable c (.addSuppressed t c)))
        (throw t)))))

(defn- thaw-until-eof
  "Realize every back-to-back nippy frame from `in` into a vector, stopping at EOF.
  Caller holds the class-name check open (`thaw-chunk`)."
  [^DataInputStream in]
  (loop [acc (transient [])]
    (let [item (try (nippy/thaw-from-in! in) (catch EOFException _ ::eof))]
      (if (identical? ::eof item) (persistent! acc) (recur (conj! acc item))))))

(defn- thaw-chunk
  "Decompress + thaw one v6 chunk payload (`bs`) into a vector of frames.

  Behind the class-name check (`vaelii.impl.io.thaw`): a stream file is untrusted input,
  and a frame naming a class is refused before the name is resolved.  The entry point is opened
  once per **chunk** rather than once per frame — a chunk is ten thousand frames by
  default, and the binding is the same one for all of them."
  [^bytes bs compression]
  (safe/guarded
   (fn []
     (with-open [in (DataInputStream.
                     (BufferedInputStream.
                      (wrap-input (ByteArrayInputStream. bs) compression)))]
       (thaw-until-eof in)))))

;; ---- the stream behind a lazy seq -------------------------------------------
;; A reader hands back a lazy seq over an open file, and a lazy seq cannot tell when its
;; consumer stops asking — a `take`, a `doseq` whose body threw, an install that refused
;; a malformed frame.  Three things close the stream, so none of those leaks a handle:
;;
;; - **full consumption**, at the EOF step, the common case;
;; - **a failure inside the seq** — a torn chunk, an undecodable frame — closes it before
;;   the throw travels (`closing-on-failure`);
;; - **the seq being dropped**: a `Cleaner` watches the step closure every unrealized
;;   tail holds, and closes the stream once nothing holds one any more.  GC-timed, so a
;;   consumer that knows it stopped early calls `close-frames!` instead of waiting.
;;
;; The cleaner tracks the *step closure*, not the head: a consumer walking a `doseq`
;; drops the head as it goes, while the closure stays reachable from the tail still to be
;; realized, and is dropped exactly when the rest of the seq is.

(def ^:private ^java.lang.ref.Cleaner cleaner (java.lang.ref.Cleaner/create))

;; `close-frames!` needs the closer for a seq a caller hands back, and the head cannot
;; carry it in metadata: `clojure.lang.LazySeq.withMeta` is `new LazySeq(meta, seq())`, so
;; `with-meta` on the head **realizes its first element** — the reader would decompress and
;; thaw a whole chunk at construction, for every reader built and never consumed.  So the
;; head stays untouched and the closers live here, keyed on identity through weak
;; references: an entry holds nothing alive, and both `framed` and `close-frames!` sweep
;; the cleared ones, so a reader nobody closes explicitly costs one dead entry until the
;; next call and nothing after it.  The queue holds one entry per *open* reader.
(defonce ^{:private true
           :tag java.util.concurrent.ConcurrentLinkedQueue}
  open-readers
  (java.util.concurrent.ConcurrentLinkedQueue.))

(defn- sweep-readers!
  "Drop registry entries whose seq has been collected, and run `f` on the entry whose seq
  is `frames` (removing it).  One pass; the registry is a handful of entries."
  [frames f]
  (let [^java.util.Iterator it (.iterator open-readers)]
    (loop []
      (when (.hasNext it)
        (let [e ^clojure.lang.MapEntry (.next it)
              s (.get ^java.lang.ref.WeakReference (key e))]
          (cond
            (nil? s)              (.remove it)
            (identical? s frames) (do (.remove it) (f (val e)))
            :else                 nil))
        (recur)))))

(defn- closing-on-failure
  "Run `(read)` and return its value; a throw closes `in` first, then travels."
  [^InputStream in read]
  (try (read)
       (catch Throwable t
         (try (.close in) (catch Throwable _ nil))
         (throw t))))

(defn- framed
  "The lazy seq `(step)` over `in` — **unrealized**, so nothing is read until it is asked
  for — with the stream's close registered on the step closure for the dropped-seq case
  and in `open-readers` for `close-frames!`."
  [^InputStream in step]
  (.register cleaner step (fn [] (try (.close in) (catch Throwable _ nil))))
  (let [s (step)]
    (sweep-readers! nil (fn [_] nil))
    (.add open-readers
          (clojure.lang.MapEntry. (java.lang.ref.WeakReference. s) #(.close in)))
    s))

(defn close-frames!
  "Close the stream behind a seq one of the readers below returned, for a consumer that
  stopped before the end.  Idempotent; a no-op on any other seq."
  [frames]
  (when frames (sweep-readers! frames (fn [c] (c))))
  nil)

(defn closer
  "`frames` as a `java.io.Closeable`, so a consumer can put the stream in the `with-open`
  it already has rather than wrapping its whole body in a `try`.

  A frame seq closes its own file on being consumed to the end, and on a failure it
  raises itself — but **not** on a throw out of the consumer's body, which is the exit a
  cancelled load, a refused frame and a failed write all take.  Every such consumer holds
  a sink under `with-open` already; one more binding there is the whole of what it takes
  to give the stream the same lifetime, and `with-open` closes in reverse order, so the
  stream goes after the sink that was reading against it."
  ^java.io.Closeable [frames]
  (reify java.io.Closeable
    (close [_] (close-frames! frames))))

(def ^:private max-chunk-bytes
  "The largest chunk `read-chunked-seq` will allocate for.  A chunk is read off a
  four-byte length the file states, and a dump is untrusted input — a crafted or torn
  length of two billion is a two-gigabyte allocation before a byte of it is checked, and
  a negative one an untyped throw.  The writer's default chunk (`chunk-size` frames)
  measures about a megabyte compressed, so this is generous headroom while still a bound."
  (* 256 1024 1024))

(defn read-chunked-seq
  "Lazy seq of frames from a v6+ chunked stream file: a run of `[int32 length]
  [compressed chunk]`.  Chunks are read serially and thawed on demand, so the whole
  file never sits in heap.  A length outside `[0, max-chunk-bytes]` is refused
  `:truncated-dump` before anything is allocated for it.  The stream closes when fully
  consumed, when a read or thaw inside it fails, or when the seq is dropped;
  `close-frames!` closes it sooner."
  [file compression]
  (let [^DataInputStream in (DataInputStream.
                             (BufferedInputStream. (io/input-stream (io/file file))))
        read-frame! (fn []
                      (try
                        (let [len (.readInt in)]
                          (when (or (neg? len) (> len max-chunk-bytes))
                            (throw (ex-info (str "chunk length " len " is not one this framing"
                                                 " writes — a chunk is 0 to "
                                                 max-chunk-bytes " bytes, so the stream is"
                                                 " torn, or is not a vaelii chunked"
                                                 " stream")
                                            {:type :truncated-dump :file (str file)
                                             :length len :max max-chunk-bytes})))
                          (let [bs (byte-array len)]
                            (.readFully in bs)
                            bs))
                        (catch EOFException _ nil)))
        step (fn step []
               (lazy-seq
                (if-let [bs (closing-on-failure in read-frame!)]
                  (concat (closing-on-failure in #(thaw-chunk bs compression)) (step))
                  (do (.close in) nil))))]
    (framed in step)))

(defn read-window-seq
  "Lazy seq of frames from a legacy v4/v5 stream file — one compression window over
  back-to-back frames, read serially.  The stream closes as `read-chunked-seq`'s does."
  [file compression]
  (let [^DataInputStream in (DataInputStream.
                             (BufferedInputStream.
                              (wrap-file-input file compression)))
        step (fn step []
               (lazy-seq
                (let [item (closing-on-failure
                            in #(try (safe/thaw-from-in! in) (catch EOFException _ ::eof)))]
                  (if (identical? ::eof item)
                    (do (.close in) nil)
                    (cons item (step))))))]
    (framed in step)))
