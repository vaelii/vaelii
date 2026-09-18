;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.index-snapshot
  "A **mapped snapshot** of the columnar index, which pages its cold tail to disk
  instead of holding all of it in heap.

  `:disk-columnar` keeps durable records and rebuilds the derived index on every open.
  That rebuild is O(records) — measured at 5.6 s for 313k, ~30 min at 100M — and the
  rebuilt structure is then wholly resident, which is the wall the scale plan names.
  This writes the compacted index to disk once and maps it back, so an open reads bytes
  and the fact-scaled postings live in the page cache rather than the heap.

  ## The design is a snapshot, not a store

  The index is **derived state**: `reindex` rebuilds every entry from the records.  That
  is what makes this cheap — no write-ahead log, no op log, no crash-consistent mutation
  protocol, no bucket directory.  It needs a *snapshot* that can be thrown away and
  rebuilt whenever it is in doubt, and \"in doubt\" resolves to `reindex` in every case.

  It is also why there is no directory to page.  A flat-map index keys every trie node by
  a boxed vector of its whole path prefix, so an out-of-core design over it has to page
  the keys themselves; the columnar trie has no keys at all — a node's identity is its
  `int` id and its position in the parallel arrays *is* the directory.  `columnar/compact!`
  already produces exactly the arrays this writes.

  ## What is written

  Under `<dir>/index/`, four things:

  * `trie.csr` — the trie's six CSR sections (`fcounts` `foffsets` `fedge-tok`
    `fedge-tgt` `fleaf-off` `fhandles`), each a raw little-endian `int` run behind a
    header naming the counts.
  * `roots.csr` — **every** root family (context/functor roots, the argument roots, the
    term, rule and exception indexes) as the same CSR shape over `dense-roots`' packed
    `long` keys: sorted keys, an offset column, one shared handle run.  Plus the scope
    table the argument roots decode through — one `(predicate, position)` pair per entry,
    indexed by the scope id their packed keys carry (`dense-roots`' `argfam-id`).  The
    table is vocabulary-scaled and rides this file because this file's key column is its
    only reader: written in one pass, discarded as one unit, so the two cannot drift.
  * `roots-fallback.nippy` — everything the routed families do not claim: the term and
    slot rosters, whose members are *names* rather than handles.  Both are
    vocabulary-scaled.  It is still index truth — the slot roster is what the
    predicate-agnostic argument reads descend through — so its entry count and byte
    length ride the meta and are checked on open like the CSR sections' lengths, and its
    load is strict (`read-fallback`).
  * `tokens.log` — the durable token dictionary the `int` edges cite, in
    `vaelii.impl.disk.tokens`' format (append-only, id = append position, content-keyed,
    first-writer-wins, never reused).  That module is reused rather than a second
    dictionary format minted: persisting the trie's `int` edges is precisely the format
    `vaelii.impl.tokens` names as its durable variant.

  **One file per structure**, not one per section.  A structure is mapped or discarded as
  a unit, so per-section files would multiply the crash window by six for nothing; the
  section table in the header already names the offsets `map` needs.

  ## The residency split

  `scale-100m.md`'s rule is *never page the walk* — the worst measured index pathology was
  the leading-variable trie fan, 18,512 lookups for one query, and a disk seek is worse
  than the round trip that pathology was made of.  So the load is deliberately asymmetric:

  * **resident** — the CSR skeleton (`fcounts` `foffsets` `fedge-tok` `fedge-tgt`), the
    roots' key and offset columns, the scope table, the token dictionary, and the
    fallback blob.  Every one of them is path- or vocabulary-scaled.
  * **mapped** — `fleaf-off` / `fhandles` and the roots' handle run.  Each posting is
    touched only when its own term is queried.  Cold by construction.

  **No handle family is an exception to that split.**  The resident half is where the
  index's *shape* lives and the mapped half is where its mass lives, and the line between
  them is the line between what the vocabulary sizes and what the facts do.

  With `mmap` the OS page cache is the residency policy, which is the point — but only
  because the skeleton stays hot.

  ## Validity is the whole design

  The failure to fear is a stale snapshot that passes its check: one can be perfectly
  self-consistent and describe a KB that no longer exists.  So the stamp covers the
  **records**, not the snapshot's own bytes, and it is checked on **every** open — never
  behind a flag.  Three things must agree or the snapshot is discarded and `reindex` runs:
  the format and `kv/index-layout-version`, the byte-order tag (the sections are always
  little-endian, so this guards a future format that changes the order, not this machine's
  architecture), and `record-store/slot-fingerprint`.  The
  decision carries a reason from `import`'s vocabulary — `:absent` `:layout-changed`
  `:records-differ` `:entries-truncated` `:unsupported-platform` — because a rebuild
  nobody can explain is a rebuild nobody notices.

  ## The platform

  The commit is an atomic rename over a file this process has mapped, which Windows does
  not permit, so `:index :snapshot` is **refused** there (`enabled?`) and an image
  found on disk is discarded as `:unsupported-platform` rather than read and never
  refreshed.  Nothing else in the durable store is implicated: the logs are appends and
  the slots are positional writes.

  A commit is one atomic step: the sections are written to temps and fsynced, the meta is
  **deleted**, the temps are renamed into place, and the meta is written last.  Its
  presence is the commit point, so a crash anywhere leaves no meta, and no meta means
  reindex.

  ## What it measured

  1.72–1.84× off the index's resident heap and a 1.5× faster open, on a corpus whose
  vocabulary is fixed — and resident heap that still grows with the facts, because the
  token dictionary is fact-scaled and the CSR skeleton is path-scaled.  The acceptance
  property it was built for does **not** hold, which is why it is off by default."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.columnar :as col]
            [vaelii.impl.config :as config]
            [vaelii.impl.dense-roots :as roots]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.dense-roots :as dense-roots-types])
  (:import [java.io File RandomAccessFile]
           [java.nio Buffer ByteBuffer ByteOrder IntBuffer LongBuffer]
           [java.nio.channels FileChannel FileChannel$MapMode]
           [java.nio.file Files Paths StandardCopyOption]
           [java.util Arrays]))

(def ^:const format-version
  "The snapshot's own layout number, beside `kv/index-layout-version` (which says what the
  *entries* mean).  Bump when a section's shape or order changes."
  2)

(def ^:private ^:const trie-magic  0x56545249)     ; "VTRI"
(def ^:private ^:const roots-magic 0x56524f54)     ; "VROT"

(def ^:private byte-order-tag
  "The byte order the sections are written in — always little-endian, on every platform,
  since `put-ints!` and `map-ints` both force it.  So an image is portable across
  architectures: a big-endian JVM reads it back correctly, not as noise.  Recorded in the
  meta and checked on load so a future format that changed the order could not be read
  under this one's assumptions — it cannot mismatch an image this code wrote."
  "LITTLE_ENDIAN")

;; ---- the platform the image publishes on --------------------------------

(defn- os-name
  "The platform, as a fn so a test can name one this machine is not — asserting the
  guard by re-reading `os.name` would assert the expression it is checking."
  ^String []
  (str (System/getProperty "os.name")))

(defn- publishable-platform?
  "Can an image be *published* here?  The question is the rename, not the map: a
  read-only `FileChannel.map` works everywhere, and what Windows does not permit is
  `Files/move` with `REPLACE_EXISTING` over a target that is currently mapped — which is
  how `rename!` below commits every section.  The JVM offers no portable unmap, so there
  is no way to hold the guarantee there.

  Windows is the refused case and everything else is admitted: the evidence is one
  operating system's file-locking model, so \"not Windows\" is the honest reading of it.
  The durable store itself is untouched by this — its logs and slots are ordinary
  appends and positional writes, and refusing them here would turn a working platform
  into a refused one on the strength of an off-by-default feature."
  []
  (not (str/starts-with? (str/lower-case (os-name)) "windows")))

(defn enabled?
  "Can this platform serve a mapped image?  True, or a throw — never false.

  Which KBs get an image is `kb/backend-axes`' answer, not this one's: `:index :snapshot`
  names the representation and `kb/snapshot-mode?` reads the axis.  What is left here is
  the platform, and it refuses rather than degrades. An operator who named
  `:disk-snapshot` and silently got `:disk-columnar` would be told nothing about the
  rebuild they think they no longer pay for, which is the whole of what the name bought."
  []
  (when-not (publishable-platform?)
    (throw (ex-info (str "the :snapshot index publishes by renaming a new file over the"
                         " live one while it is mapped, which " (os-name) " does not"
                         " permit.  Take :disk-columnar, which rebuilds its index from"
                         " the records on open, or :disk-log, whose index is durable.")
                    {:type :unsupported-platform :index :snapshot :os (os-name)
                     :remedy {:index :columnar}})))
  true)

(defn snapshot-root ^String [dir] (str dir "/index"))

;; ---- the cadence -------------------------------------------------------
;; The image is written when the directory closes, which is right for what it describes
;; and thin for a writer that runs for weeks: a process killed outright has no image, and
;; the next open pays the whole `reindex` the backend was named to skip.  So the writer
;; refreshes it mid-life, when the live index has drifted far enough from the one on disk.
;;
;; **On the writer's thread, and that is not a detail.**  `vaelii.impl.columnar`'s fields
;; are `^:unsynchronized-mutable` and its docstring says whose job the synchronization is:
;; *"the caller's, to keep its reads on the writer's thread."*  `save!` compacts the live
;; trie in place, so a refresh queued onto `disk/durability.clj`'s compaction executor —
;; where the record store and the KV put theirs, both of them built around a monitor —
;; would mutate this index from a second thread.  The record store can be compacted by the
;; daemon; this index can only be written by whoever writes it.
;;
;; The cost is a stall: a refresh is a full CSR rewrite, not a delta, so the writer waits
;; out an image-sized write.  `vaelii.index.snapshot-drift` and the compaction interval
;; floor are what keep that rare, and `docs/storage.md` states the trade rather than
;; leaving it to be discovered.
;;
;; **The write entry point is the only path that reaches this**, and that scoping is the thing to
;; know before diagnosing an image count.  `kb/create-sentex` asks `due?`; nothing else
;; does.  `reindex/index-one!` posts straight to `p/index-sentex`, and the importer's inline
;; bulk load goes through that same function — so a store filled by `reindex` or by an
;; import gets exactly one image, at the close, whatever the drift threshold says, while the
;; same content arriving through `assert` is measured and can refresh many times over.
;;
;; **And a writer that closes cleanly can decline the refresh outright**, with
;; `vaelii.disk.auto-compact=false` — see `due?`.  A batch that fills a whole KB in one run
;; wants exactly one image, at the end.  The interval floor is the wrong lever for that (it
;; only rate-limits, and moves the record store's compaction with it) and so is the drift
;; ratio, whose `0` is the *most* eager setting rather than the off one.

(defonce ^:private image-state
  ;; `{canonical-snapshot-root {:roots n :at ms}}` — the indexed-root count the image on
  ;; disk holds and when it was written or read.  Drift is measured against the first; the
  ;; second is what the interval floor is applied to.
  ;;
  ;; **Keyed canonically**, because the two sides reach it by different spellings of one
  ;; directory: a save is handed the `:dir` opt as the caller wrote it, and the write entry point
  ;; is handed the KB's own `dir`, which the disk backend has already resolved.  On macOS
  ;; that is `/var/…` against `/private/var/…` — two keys, so the cadence would read a
  ;; baseline nothing ever wrote and never fire.
  (atom {}))

(defn- state-key ^String [dir]
  (let [root (snapshot-root dir)]
    (try (.getCanonicalPath (File. root)) (catch Throwable _ root))))

(defn- note-image! [dir roots]
  (swap! image-state assoc (state-key dir) {:roots (long roots) :at (System/currentTimeMillis)})
  nil)

(defn note-attempt!
  "Restart `dir`'s interval floor without moving its drift baseline — what a refresh does
  as it begins.

  The baseline belongs to an image that is actually on disk, so only a completed save
  moves it (`note-image!`).  The *clock* is a different claim — how recently a refresh was
  attempted — and it has to advance whether or not one landed: a save that throws, and a
  save that declines (`:unchanged`, `:empty`), both leave the drift exactly where it was,
  so a cadence stamped only on success reads due again on the very next write.  That turns
  a broken directory into an image-sized write per assert.  Stamped here, it retries once
  a floor, which is the cadence the floor exists to impose.

  A no-op for a directory with no cadence state: `due?` cannot fire without one, so
  minting a baseline here would be inventing an image nothing wrote."
  [dir]
  (let [k (state-key dir)]
    (swap! image-state
           (fn [m] (if (contains? m k)
                     (update m k assoc :at (System/currentTimeMillis))
                     m))))
  nil)

(defn note-no-image!
  "Start `dir`'s cadence clock with **no** image on disk — what an open does before it
  knows whether one is there.  A `load!` that maps overwrites this with the real count;
  one that rebuilds leaves it standing, which is the truth: nothing usable is on disk.

  Without this a directory that has never held an image would have no baseline, so
  `drift` would answer 0.0 forever and a writer that ran for weeks and was killed would
  reopen onto nothing — which is the failure the cadence exists to close, and the one a
  fresh directory is most exposed to.

  **It starts a clock and never resets one.**  Every KB constructed over a directory runs
  this, and they share one index — so a second `open-kb` over a directory whose image is
  current would otherwise reset the baseline to zero, `drift` would read 1.0 against an
  image that is exactly right, and the first write past the interval floor would rewrite
  a whole CSR for nothing.  A close is what drops the state (`forget-image!`), which is
  the point at which what is on disk stops being knowable from in here."
  [dir]
  (let [k (state-key dir)]
    (swap! image-state
           (fn [m] (if (contains? m k)
                     m
                     (assoc m k {:roots 0 :at (System/currentTimeMillis)})))))
  nil)

(defn forget-image!
  "Drop `dir`'s cadence state — what a close does, so a directory reopened in this JVM
  measures its drift against the image it actually finds rather than against one this
  process happened to write earlier."
  [dir]
  (swap! image-state dissoc (state-key dir))
  nil)

(defn- drift-of
  "`drift` over a cadence entry already read out of the state."
  ^double [{:keys [roots]} roots-now]
  (cond
    (nil? roots)         0.0
    (zero? (long roots)) (if (pos? (long roots-now)) 1.0 0.0)
    :else (/ (double (Math/abs (- (long roots-now) (long roots)))) (double roots))))

(defn drift
  "How far `roots-now` has moved from the image at `dir`, as a ratio of the image's own
  count — or 0.0 when this JVM has neither written nor read one, since there is nothing
  to have drifted from and a refresh would be writing an image against no baseline."
  ^double [dir roots-now]
  (drift-of (get @image-state (state-key dir)) roots-now))

(defn due?
  "Has `dir`'s image drifted past `vaelii.index.snapshot-drift`, with the compaction
  interval floor elapsed since the last one?

  The floor is `vaelii.disk.compact-min-interval-ms`, shared with the record store's
  compaction rather than given a knob of its own: both answer the same question — how
  often may a background rewrite of a derived structure interrupt this KB — and two knobs
  would be two answers to it.

  **`vaelii.disk.auto-compact=false` turns the mid-life refresh off**, leaving the image to
  the close and to the JVM-shutdown hook.  Same knob as the record store's background and
  opportunistic compaction, on the same argument the shared floor rests on: a refresh *is*
  an opportunistic compaction of a derived structure — `save!` calls `columnar/compact!` —
  so an operator who has said not to do those must not still be paying one per drift
  threshold, on the writer's thread, with nothing saying so.  The caller that wants the
  switch is the batch that fills a whole KB in one run and closes cleanly: it needs exactly
  one image, at the end.

  **The drift ratio cannot say that, and `0` is the trap.**  As a *threshold* zero means
  \"any drift at all\", so it is the most eager setting in the range and rewrites the image
  on every write past the floor — 400 asserts under `0` and a floor of `0` measured 401
  images.  It is the pathology the threshold exists to bound, not the off switch.

  **One state read, one `state-key`.**  This is asked per write on a `:disk-snapshot` KB
  and `state-key` resolves a canonical path, so the switch is read first — an off switch
  that still paid a `realpath` per write would not be off for the writer that asked for it
  — and the entry is then read once, with the drift computed off it rather than reaching
  for the same key again through `drift`."
  [dir roots-now]
  (and (config/disk-auto-compact?)
       (let [{:keys [at] :as st} (get @image-state (state-key dir))]
         (and (some? at)
              (>= (- (System/currentTimeMillis) (long at))
                  (long (config/disk-compact-min-interval-ms)))
              (>= (drift-of st roots-now) (config/index-snapshot-drift))))))

(defn- meta-path      ^String [root] (str root "/snapshot.meta"))
(defn- trie-path      ^String [root] (str root "/trie.csr"))
(defn- roots-path     ^String [root] (str root "/roots.csr"))
(defn- fallback-path  ^String [root] (str root "/roots-fallback.nippy"))

;; ---- raw section i/o ----------------------------------------------------

(def ^:private ^:const chunk-ints 65536)

(defn- put-ints!
  "Append `n` ints of `src` (an `int[]` or an `IntBuffer`) to `ch`, little-endian."
  [^FileChannel ch src ^long n]
  (let [bb (doto (ByteBuffer/allocate (* 4 (int (min n chunk-ints))))
             (.order ByteOrder/LITTLE_ENDIAN))]
    (loop [i 0]
      (when (< i n)
        (let [k (int (min chunk-ints (- n i)))]
          (.clear bb)
          (let [ib (.asIntBuffer bb)]
            (if (instance? IntBuffer src)
              (let [^IntBuffer s (doto (.duplicate ^IntBuffer src) (.position (int i)) (.limit (int (+ i k))))]
                (.put ib s))
              (.put ib ^ints src (int i) k)))
          (.limit ^Buffer bb (* 4 k))
          (.position ^Buffer bb 0)
          (while (.hasRemaining bb) (.write ch bb))
          (recur (+ i k)))))))

(defn- put-longs! [^FileChannel ch ^longs src]
  (let [n  (alength src)
        bb (doto (ByteBuffer/allocate (* 8 (int (min n chunk-ints))))
             (.order ByteOrder/LITTLE_ENDIAN))]
    (loop [i 0]
      (when (< i n)
        (let [k (int (min chunk-ints (- n i)))]
          (.clear bb)
          (.put (.asLongBuffer bb) src (int i) k)
          (.limit ^Buffer bb (* 8 k))
          (.position ^Buffer bb 0)
          (while (.hasRemaining bb) (.write ch bb))
          (recur (+ i k)))))))

(defn- put-header! [^FileChannel ch ints]
  (let [bb (doto (ByteBuffer/allocate (* 4 (count ints))) (.order ByteOrder/LITTLE_ENDIAN))]
    (doseq [v ints] (.putInt bb (int v)))
    (.position ^Buffer bb 0)
    (while (.hasRemaining bb) (.write ch bb))))

(defn- section-len [src] (if (instance? IntBuffer src) (.limit ^IntBuffer src) (alength ^ints src)))

(defn- open-write
  "A truncated `rw` channel on `path`.  The truncate is guarded rather than chained onto
  the open: a `.setLength` that throws leaves a `RandomAccessFile` nothing holds a
  reference to and nothing will close, and a publish that fails on a full disk is
  exactly when the process keeps running."
  ^FileChannel [^String path]
  (let [raf (RandomAccessFile. path "rw")]
    (try (.setLength raf 0) (.getChannel raf)
         (catch Throwable t
           (try (.close raf) (catch Throwable _ nil))
           (throw t)))))

(defn- rename! [^String from ^String to]
  (Files/move (Paths/get from (into-array String []))
              (Paths/get to (into-array String []))
              (into-array java.nio.file.CopyOption
                          [StandardCopyOption/ATOMIC_MOVE StandardCopyOption/REPLACE_EXISTING])))

(defn- map-ints ^IntBuffer [^FileChannel ch ^long off ^long n]
  (-> (.map ch FileChannel$MapMode/READ_ONLY off (* 4 n))
      (.order ByteOrder/LITTLE_ENDIAN)
      (.asIntBuffer)))

(defn- map-longs ^LongBuffer [^FileChannel ch ^long off ^long n]
  (-> (.map ch FileChannel$MapMode/READ_ONLY off (* 8 n))
      (.order ByteOrder/LITTLE_ENDIAN)
      (.asLongBuffer)))

(defn- read-ints
  "A section copied into heap — the resident half of the split."
  ^ints [^FileChannel ch ^long off ^long n]
  (let [^IntBuffer b (map-ints ch off n)
        a (int-array n)]
    (.get b a 0 (int n))
    a))

(defn- read-header ^ints [^FileChannel ch ^long n]
  (let [^IntBuffer b (map-ints ch 0 n)
        a (int-array n)]
    (.get b a 0 (int n))
    a))

;; ---- the token remap ----------------------------------------------------

(defn- sort-edge-runs!
  "Re-sort each node's `[token target]` edge run by token.

  The remap into the durable dictionary's id space permutes the labels, and the frozen
  `-get-child` **binary-searches** the run — so per-node sorted order is part of the
  format rather than an accident of how the trie was built.  Sorted through a packed
  `(token << 32) | index` key so a wide node (a broad relation's level-2 node reaches
  hundreds of thousands of children) costs O(w log w), not the O(w²) an in-place pair
  insertion would."
  [^ints offsets ^ints etok ^ints etgt ^long nodes]
  (dotimes [i nodes]
    (let [lo (aget offsets (int i))
          hi (aget offsets (int (inc i)))
          w  (- hi lo)]
      (when (> w 1)
        (let [keys (long-array w)]
          (dotimes [j w]
            (aset keys j (bit-or (bit-shift-left (long (aget etok (+ lo j))) 32) (long j))))
          (Arrays/sort keys)
          (let [ot (int-array w) og (int-array w)]
            (dotimes [j w]
              (let [src (int (bit-and (aget keys j) 0xffffffff))]
                (aset ot j (aget etok (+ lo src)))
                (aset og j (aget etgt (+ lo src)))))
            (System/arraycopy ot 0 etok lo w)
            (System/arraycopy og 0 etgt lo w)))))))

(defn- durable-remap
  "Intern every in-RAM token into the durable dictionary, in id order, and return the
  `int[]` from in-RAM ids to durable ones.

  It is the identity whenever the snapshot was itself loaded from this dictionary (the
  load rebuilds the in-RAM ids from the log, in order), and a genuine permutation after a
  `reindex` re-interned the vocabulary in arrival order.  Both are correct and only the
  second costs anything: **ids are opaque edge labels**, so what has to be preserved is
  the answers, never the numbers."
  ^ints [dict tl]
  (let [n  (long (tok/token-count dict))
        rm (int-array n)]
    (dotimes [i n] (aset rm i (int (dtok/intern! tl (tok/id-token dict i)))))
    rm))

(defn- remap-edges ^ints [^ints etok ^ints remap]
  (let [n (alength etok)
        o (int-array n)]
    (dotimes [i n] (aset o i (aget remap (aget etok i))))
    o))

;; ---- writing ------------------------------------------------------------

(defn- write-trie! [^String path {:keys [nodes counts offsets edge-tok edge-tgt leaf-off handles]}]
  (let [e (section-len edge-tok)
        h (section-len handles)]
    (with-open [ch (open-write path)]
      (put-header! ch [trie-magic format-version nodes e h 0])
      (put-ints! ch counts   nodes)
      (put-ints! ch offsets  (inc (long nodes)))
      (put-ints! ch edge-tok e)
      (put-ints! ch edge-tgt e)
      (put-ints! ch leaf-off (inc (long nodes)))
      (put-ints! ch handles  h)
      (.force ch true))
    {:nodes nodes :edges e :leaves h}))

(defn- write-roots!
  "The routed families as three columns, and the scope table that decodes the argument
  roots among them.

  The table rides this file rather than a log beside `tokens.log` because the key column
  here is its only reader: the two are written in one pass and discarded as one unit, so
  they cannot drift apart.  `tokens.log` is durable ground truth appended as facts arrive,
  which is why it can disagree with an image and why `:duplicate-tokens` exists to repair
  that."
  [^String path {:keys [keys offsets handles preds positions]}]
  (let [k (alength ^longs keys)
        h (alength ^ints handles)
        a (alength ^ints preds)]
    (with-open [ch (open-write path)]
      (put-header! ch [roots-magic format-version k h a])
      (put-longs! ch keys)
      (put-ints!  ch offsets (inc (long k)))
      (put-ints!  ch handles h)
      (put-ints!  ch preds   a)
      (put-ints!  ch positions a)
      (.force ch true))
    {:keys k :handles h :scopes a}))

(defn save!
  "Write a mapped snapshot of `store` (a columnar `IndexStore`) under `dir/index`, stamped
  with `(stamp-fn)`.  Returns `{:index :saved …}`, or `{:index :skipped :reason r}`.

  The stamp arrives as a thunk rather than as a record store: what an image is valid
  against is a *fingerprint of the records*, and which store computed it is none of this
  namespace's business — `record-store/slot-fingerprint` is what the disk KB passes.
  A thunk, so `load!` can decline before paying for it.

  Compacts the trie first — the CSR arrays `compact!` produces *are* the on-disk layout,
  so there is no serialization step, only a write.  An empty index saves nothing and
  drops any meta that survives, since a stale one describing a wiped KB is the one thing
  worse than none.

  **A failed save costs the new image, never the one already there.**  Every section is
  written to a `.tmp` beside its target and the meta — the commit mark — is dropped only
  once all of them are complete, so a throw anywhere before that leaves the previous
  image whole and readable, **and takes the temps it had written with it**: a section is
  the size of the index, and one left behind by a save that never committed is a file
  nothing reads and nothing else deletes.  The stamp is taken *first*, before a byte
  moves, because it is the one input that lives in another component: on the shutdown
  path that component can already be closed, and taking it late would trade a working
  image for none."
  [dir store stamp-fn]
  (let [root (snapshot-root dir)]
    (f/ensure-dir! root)
    (cond
      (not (col/columnar? store))
      {:index :skipped :reason :not-columnar}

      (zero? (long (p/count-at store [])))
      (do (.delete (File. (meta-path root)))
          {:index :skipped :reason :empty})

      ;; Still reading out of the image it was opened from, so the image *is* this index
      ;; and rewriting it would be pure loss: `snapshot-columns` thaws the roots to read
      ;; them, which would pull the whole cold tail back into heap at the very moment the
      ;; KB is closing.  A write would have thawed one or both halves and this is false.
      (and (col/mapped? store) (dense-roots-types/mapped? (:roots store)))
      {:index :skipped :reason :unchanged}

      :else
      (let [t0    (System/nanoTime)
            stamp (stamp-fn)
            ;; **Freezing the live trie under an unconsumed lazy read is safe**, and it is
            ;; worth noting so, because the write entry point reaches here mid-life while a caller
            ;; may be holding one: `core/sentexes-matching` promises a seq that is lazy over
            ;; live state, and asserting while walking one is the supported pattern
            ;; `forward-chain` is built on.  What makes it safe is that an index read is
            ;; eager *per read* — `res/candidate-handles` has realized its handles before
            ;; `match-one` returns, and `t-lookup` builds its answer with `into #{}` — so no
            ;; walk is ever part-way through the trie when this runs.  What stays lazy above
            ;; is the `get-sentex` per handle, which is the record store's, and at a variable
            ;; context one whole index read per reader (`vantage/fan-distinct`), which lands
            ;; either side of the freeze and never inside it.  The read primitives dispatch
            ;; on `frozen?` at call time (`vaelii.impl.columnar`), so the reader after this
            ;; reads the CSR and answers the same set.
            _     (col/compact! store)
            csr   (col/csr store)
            dict  (:dict store)
            rts   (:roots store)
            tmp   #(str % ".tmp")
            ;; named out here so the `finally` can reach them: a save that throws
            ;; part-way leaves the previous image whole, but it also leaves behind
            ;; whatever `.tmp` sections it had already written — index-sized files,
            ;; which on a KB that is never reopened sit in the directory for good.
            ;; They are cleared on the way out unless the meta committed, and deleting
            ;; a temp that was already renamed is a harmless false.
            temps [(tmp (trie-path root)) (tmp (roots-path root)) (tmp (fallback-path root))]
            done  (volatile! false)
            ;; this fn's own handle on the durable dictionary, and every step below it
            ;; can throw — a full disk mid-write, a mapped section that will not read.
            ;; It closes in a `finally`, or a failed save would leak a file handle on
            ;; exactly the directory a `close-dir!` is trying to let go of.
            tl    (dtok/open-token-log root)]
        (try
          (let [remap (durable-remap dict tl)
                etok  (remap-edges (:edge-tok csr) remap)
                ;; a copy, because `sort-edge-runs!` permutes it and the live index's own
                ;; array must not move.  The skeleton is heap `int[]` in every trie mode —
                ;; only the leaf pair is ever mapped (`columnar/t-csr`), and the walk reads
                ;; edge targets at every frontier node, so they never page — so this is an
                ;; array clone, never a buffer read.
                etgt  (aclone ^ints (:edge-tgt csr))
                _     (sort-edge-runs! (:offsets csr) etok etgt (:nodes csr))
                cols  (merge (dense-roots-types/snapshot-columns rts remap)
                             (roots/argfam-table rts remap))
                tstat (write-trie!  (tmp (trie-path root))
                                    (assoc csr :edge-tok etok :edge-tgt etgt))
                rstat (write-roots! (tmp (roots-path root)) cols)
                fents (vec (roots/fallback-entries rts))]
            ;; beside its target rather than over it, so the blob the previous meta
            ;; describes stays intact until the swap below
            (f/write-nippy-atomic! (tmp (fallback-path root)) fents)
            (dtok/fsync tl)
            ;; the meta is the commit point: drop it, swap the sections in, write it last
            (.delete (File. (meta-path root)))
            (rename! (tmp (trie-path root))     (trie-path root))
            (rename! (tmp (roots-path root))    (roots-path root))
            (rename! (tmp (fallback-path root)) (fallback-path root))
            (f/write-nippy-atomic!
             (meta-path root)
             {:format       format-version
              :index-layout kv/index-layout-version
              :byte-order   byte-order-tag
              :records      stamp
              :trie         tstat
              :roots        rstat
              ;; the blob carries the slot roster, which the agnostic argument reads
              ;; descend through, so its size is recorded and checked like the CSR sections'
              :fallback     {:entries (count fents)
                             :bytes   (.length (File. (fallback-path root)))}
              :tokens       (dtok/token-count tl)})
            (vreset! done true)
            (note-image! dir (p/count-at store []))
            (let [ms (/ (- (System/nanoTime) t0) 1e6)]
              (trove/log! {:level :info :id ::saved
                           :msg (format "wrote the mapped index snapshot at %s in %.0f ms (%d nodes, %d leaf handles, %d root postings)"
                                        root ms (long (:nodes tstat)) (long (:leaves tstat)) (long (:keys rstat)))})
              {:index :saved :ms ms :trie tstat :roots rstat}))
          ;; the deletes first, because `.delete` answers false where the close throws:
          ;; a token log that will not close must not be the reason index-sized temps
          ;; are left behind, and it is still the failure the caller reads.
          (finally
            (when-not @done
              (doseq [^String p temps] (.delete (File. p))))
            (dtok/close! tl)))))))

;; ---- reading ------------------------------------------------------------

(defn- file-len ^long [^String path] (let [f (File. path)] (if (.exists f) (.length f) -1)))

(defn- decision
  "Why this open cannot map the snapshot, or nil when it can.  Every mismatch class is its
  own reason, so the log says what changed rather than that something did.

  Ordered by what a reader needs told first, not by what is cheapest to ask: the record
  fingerprint runs ahead of the three truncation tests, and it is the expensive one — a
  sequential scan of the sentexes idx, where a truncation test is a `File.length`.  A
  truncated image therefore pays that scan before being rejected.  It adds no work that
  matters, since every rejection falls through to a rebuild that reads the records
  anyway, and the ordering buys a diagnosis that names the store rather than the file."
  [root m stamp-fn]
  (let [{:keys [nodes edges leaves]} (:trie m)
        {kn :keys hn :handles}       (:roots m)]
    (cond
      (nil? m)                                       :absent
      ;; An image is readable here and could never be refreshed: the publish is what the
      ;; platform refuses, and a mapped index that cannot be rewritten is a cache that
      ;; goes stale against its own records the moment one moves.  So it joins the
      ;; mismatch classes beside byte order, which is the same portability question one
      ;; layer down, and inherits their reindex path.
      (not (publishable-platform?))                  :unsupported-platform
      (not= format-version (:format m))              :layout-changed
      (not= kv/index-layout-version (:index-layout m)) :layout-changed
      (not= byte-order-tag (:byte-order m))          :byte-order
      (not= (:records m) (stamp-fn))                 :records-differ
      (or (nil? nodes) (nil? kn))                    :entries-truncated
      (< (file-len (trie-path root))
         (+ 24 (* 4 (+ (long nodes) (inc (long nodes)) (long edges) (long edges)
                       (inc (long nodes)) (long leaves)))))
      :entries-truncated
      (< (file-len (roots-path root))
         (+ 20 (* 8 (long kn)) (* 4 (inc (long kn))) (* 4 (long hn))
            (* 8 (long (or (:scopes (:roots m)) 0)))))
      :entries-truncated
      ;; the fallback blob is read whole, so its length is checked exactly — a
      ;; missing file (-1) and a meta with no record of it both land here
      (not= (file-len (fallback-path root))
            (long (or (:bytes (:fallback m)) -2)))
      :entries-truncated
      :else nil)))

(defn- load-trie! [store ^String path {:keys [nodes edges leaves]}]
  (with-open [raf (RandomAccessFile. path "r")]
    (let [ch  (.getChannel raf)
          ^ints hdr (read-header ch 6)]
      (when-not (= trie-magic (aget hdr 0))
        ;; A sentence, because this message is spliced into the user-visible WARN at
        ;; `mount-or-rebuild!` — "the index snapshot at /var/kb did not read (trie
        ;; snapshot magic)" told a reader nothing about whether their data was gone.
        (throw (ex-info (str "the trie file is not a vaelii trie snapshot — its magic number is "
                             (aget hdr 0) ", expected " trie-magic
                             "; the index will be rebuilt from the records, which are untouched")
                        {:type :bad-snapshot :part :trie :path path
                         :magic (aget hdr 0) :expected trie-magic})))
      (let [n   (long nodes) e (long edges) h (long leaves)
            o1  24
            o2  (+ o1 (* 4 n))
            o3  (+ o2 (* 4 (inc n)))
            o4  (+ o3 (* 4 e))
            o5  (+ o4 (* 4 e))
            o6  (+ o5 (* 4 (inc n)))]
        (col/install-csr!
         store
         ;; resident: the skeleton the walk reads at every frontier node
         {:counts*   (read-ints ch o1 n)
          :offsets*  (read-ints ch o2 (inc n))
          :edge-tok* (read-ints ch o3 e)
          :edge-tgt* (read-ints ch o4 e)
          ;; mapped: the leaves, read once at a walk's terminus
          :leaf-off* (map-ints ch o5 (inc n))
          :handles*  (map-ints ch o6 h)})))))

(defn- load-roots!
  "Map the three routed columns, and read the scope table resident.

  The table is vocabulary-scaled — one entry per `(predicate, position)` pair the corpus
  exhibits — so it joins the resident half of the split beside the key and offset columns
  rather than the mapped half.  It is read before the columns are installed: a packed
  argument key whose scope id decodes to nothing is a key that answers the wrong posting,
  and the throw belongs before the install rather than at the first read after it."
  [store ^String path {kn :keys hn :handles an :scopes}]
  (with-open [raf (RandomAccessFile. path "r")]
    (let [ch  (.getChannel raf)
          ^ints hdr (read-header ch 5)]
      (when-not (= roots-magic (aget hdr 0))
        (throw (ex-info (str "the roots file is not a vaelii roots snapshot — its magic number is "
                             (aget hdr 0) ", expected " roots-magic
                             "; the index will be rebuilt from the records, which are untouched")
                        {:type :bad-snapshot :part :roots :path path
                         :magic (aget hdr 0) :expected roots-magic})))
      (let [k  (long kn) h (long hn) a (long (or an 0))
            o1 20
            o2 (+ o1 (* 8 k))
            o3 (+ o2 (* 4 (inc k)))
            o4 (+ o3 (* 4 h))
            o5 (+ o4 (* 4 a))]
        (roots/load-argfam! (:roots store) (read-ints ch o4 a) (read-ints ch o5 a) a)
        (dense-roots-types/install-mapped! (:roots store)
                                           (map-longs ch o1 k)          ; resident enough to be read
                                           (map-ints  ch o2 (inc k))
                                           (map-ints  ch o3 h)
                                           k)))))

(defn- load-dictionary!
  "Rebuild the in-RAM dictionary from the durable log, **in id order**, so an in-RAM id is
  the durable id the mapped edges cite.  O(dictionary), which this namespace's own header
  is careful to say is **fact-scaled** rather than vocabulary-scaled: a token is often a
  whole compound term, and the term index keys one per record.  Nor is it the only
  per-entry cost of an open — `load-trie!` copies the node and edge skeletons into heap,
  named in the header for what it is.

  The two dictionaries must agree on equality, and this is where a disagreement would
  show.  Both key `tokens/Key`, which defers to `hasheq`/`equiv`, so `2` and `(int 2)`
  are one token in each — and the log holds numbers and whole compound terms as well as
  symbols, since every trie token is interned through it.  The count check is what makes
  the agreement a fact rather than an assumption: a mismatch means the id order has
  shifted and every mapped edge cites the wrong entry, silently, so it throws into
  `load!`'s catch and the index is rebuilt from the records instead.

  **A log that already holds such a pair is repaired here rather than diagnosed forever.**
  Written by a build whose forward map keyed on Java equality, it holds `2` and `(int 2)`
  as two frames; every reload collapses them, every open reads the mismatch, and the
  rebuilt index is snapshotted against the same unrepairable log — so the next open pays
  for it again, and the one after that. `repair-duplicates!` rewrites the log without the
  pair, which moves every id past it: legal exactly here, because this log's ids are cited
  by the mapped edges and nothing else, and the commit marker is dropped **first** so a
  crash between the two leaves no image describing a numbering the log no longer uses.
  The throw then names the cause and says the repair happened, where `:torn-snapshot`
  named the wrong one."
  [dict ^String root]
  (let [tl (dtok/open-token-log root)]
    (try
      (let [dups (dtok/duplicate-count tl)]
        (when (pos? dups)
          (.delete (File. (meta-path root)))
          (let [kept (dtok/repair-duplicates! tl)]
            (throw (ex-info (str "the durable token dictionary at " root " holds " dups
                                 " token(s) an older build wrote twice — Java-unequal but"
                                 " Clojure-equal, an integral pair such as 2 and (int 2)"
                                 " — so it reloads one entry short of the log per"
                                 " duplicate and every id past the first has shifted."
                                 " The log has been rewritten without them (" kept
                                 " entries) and the index is being rebuilt from the"
                                 " records, which are untouched; nothing is owed, and the"
                                 " next open maps its image again")
                            {:type :duplicate-tokens :path root
                             :duplicates dups :entries kept})))))
      (tok/clear-tokens! dict)
      ;; interned on the way in, shape preserved.  A token is often a whole compound
      ;; term — the term index is keyed by one per record — so a dictionary rebuilt
      ;; without this holds a private copy of every name in every one of them, which is
      ;; the opposite of what interning the vocabulary is for.  `intern-deep` rather than
      ;; `canon`, since a `[::subterm k]` marker and a rule's antecedent are vectors and
      ;; canonicalizing would flatten both to lists.
      (let [durable (dtok/token-count tl)]
        (dotimes [i durable]
          (tok/intern-token! dict (sx/intern-deep (dtok/token tl i))))
        (let [loaded (long (tok/token-count dict))]
          (when (not= loaded durable)
            (throw (ex-info (str "the durable token dictionary at " root " reloaded as "
                                 loaded " entries where it holds " durable
                                 " — the ids the mapped edges cite have shifted")
                            {:type :torn-snapshot :path root
                             :durable durable :loaded loaded}))))
        durable)
      (finally (dtok/close! tl)))))

(defn- read-fallback
  "The fallback blob, read strictly: it carries the slot roster, which the
  predicate-agnostic argument reads descend through, so a torn thaw or an entry count
  that disagrees with the meta throws (into `load!`'s catch, which rebuilds) rather than
  defaulting to an empty value the index would then serve as `#{}` on every
  `sentexes-with-arg`."
  [root m]
  (let [v    (f/read-nippy-file (fallback-path root) ::torn)
        want (long (get-in m [:fallback :entries] -1))]
    (when (or (= ::torn v) (not= (count v) want))
      (throw (ex-info (str "the roots fallback blob did not thaw whole — "
                           (if (= ::torn v)
                             "unreadable"
                             (str (count v) " entries where the meta records " want))
                           " — and it holds the term and slot rosters, which the"
                           " predicate-agnostic argument reads descend through")
                      {:type :torn-snapshot :path (fallback-path root)
                       :entries (when-not (= ::torn v) (count v)) :expected want})))
    v))

(defn load!
  "Map `dir/index` into `store`, or say why it cannot be.  Returns `{:index :mapped …}` or
  `{:index :rebuild :reason r}` with `r` one of `:absent` `:layout-changed` `:byte-order`
  `:unsupported-platform` `:records-differ` `:entries-truncated` `:duplicate-tokens`
  `:unreadable`.

  The caller reindexes on any `:rebuild` — which is always legal, because the index is
  derived state and this is a cache of it.

  `:duplicate-tokens` is the one rebuild that also **repairs** as it declines
  (`load-dictionary!`), and so the one a reader should not expect twice over one
  directory."
  [dir store stamp-fn]
  (let [root (snapshot-root dir)
        m    (f/read-nippy-file (meta-path root) nil)]
    (cond
      (not (col/columnar? store)) {:index :rebuild :reason :absent}
      (nil? m)                    {:index :rebuild :reason :absent}
      :else
      (if-let [why (decision root m stamp-fn)]
        {:index :rebuild :reason why}
        (try
          (let [t0 (System/nanoTime)]
            (p/clear-index! store)                     ; also wipes the shared dictionary
            (load-dictionary! (:dict store) root)
            (load-trie!  store (trie-path root)  (:trie m))
            (load-roots! store (roots-path root) (:roots m))
            (roots/load-fallback! (:roots store) (read-fallback root m))
            (note-image! dir (p/count-at store []))
            (let [ms (/ (- (System/nanoTime) t0) 1e6)]
              (trove/log! {:level :info :id ::mapped
                           :msg (format "mapped the index snapshot at %s in %.0f ms (%d tokens, %d nodes)"
                                        root ms (long (:tokens m)) (long (:nodes (:trie m))))})
              {:index :mapped :ms ms :trie (:trie m) :roots (:roots m)}))
          (catch Throwable t
            ;; a cause this open could do something about names itself, so the operator
            ;; reads what happened rather than "did not read" a third time
            (let [why (if (= :duplicate-tokens (:type (ex-data t))) :duplicate-tokens :unreadable)]
              (trove/log! {:level :warn :id ::unreadable
                           :msg (str "the index snapshot at " root " did not read ("
                                     (.getMessage t) ") — rebuilding from the records")})
              (p/clear-index! store)
              {:index :rebuild :reason why})))))))

(defn discard!
  "Delete a snapshot's commit marker — what a caller does when it knows the image is dead
  and would rather the next open not have to work that out."
  [dir]
  (.delete (File. (meta-path (snapshot-root dir))))
  nil)
