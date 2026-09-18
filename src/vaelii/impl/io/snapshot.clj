;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.snapshot
  "A **snapshot** of the KB's derived state, and the two-op *sink* it is written through.

  Derived state — the index, and (from 0.9.0's second thread) the taxonomy and the JTMS
  labels — is rebuilt from the records on every open by `reindex` / `recover`, at a cost
  that is O(records).  A snapshot is a *cache* of that rebuild: written once, read back on
  the next open, and installed instead of recomputed.  It is never a source of truth.  Its
  only failure mode is \"recompute\", never \"wrong answer\", which is what keeps it clear of
  order independence — a snapshot is stamped to the exact records it was derived from, and a
  mismatch takes the slow path (`reindex`/`recover`), never a stale belief.

  ## One image, many sinks

  There is more than one place a snapshot might live — a directory of files, a Postgres
  blob, memory for a test — and letting each invent its own serialization is the drift the
  shared `[key value]` index projection was created to avoid one layer up.  So the shape is
  one **sink**:

  * a snapshot is a set of **named sections** plus a **manifest**;
  * a `SnapshotSink` knows only how to *write a named section* (a constant-memory stream of
    frames) and to *commit a manifest*; a `SnapshotSource` knows how to *read a section back*
    and to *read the manifest*;
  * the **projections** (the index's `[key value]`, and later the taxonomy's edges and the
    JTMS's labels) and the **validity check** (`decision`) live here, above the sink, written
    once;
  * the **targets** — `file-sink` / `file-source` over `vaelii.impl.io.frames`, and
    `memory-medium` for a test — live below it, each a small adapter.

  A section written to one sink loads from another, the same property `p/index-entries` /
  `p/index-load` already give the index across backends.

  **The protocol has out-of-tree implementations, so it is a published shape and not a private
  one.**  `vaelii-postgres` (`vaelii.postgres.snapshot/pg-sink` / `pg-source`) and
  `vaelii-sqlite` (`vaelii.sqlite.snapshot/sqlite-sink` / `sqlite-source`) each implement
  both protocols and drive them through `save-index!` / `load-index!`, and both suites
  cross-load a section against `memory-medium` to check the two targets agree.  What is
  reached only from this repo's own tests is `file-sink` / `file-source`: the reference
  target, and the one that shows an implementer what a section and a manifest have to be.

  ## The manifest is the commit point

  It is written **last**, exactly as a dump's `meta.edn` is: a half-written image has no
  manifest, so `read-manifest` returns nil and the image is never offered — the caller
  rebuilds.  Opening a `file-sink` deletes any existing manifest first, so the window in
  which an old manifest could describe half-rewritten sections does not exist.

  ## Validity is the whole design

  `decision` is lifted from `vaelii.impl.disk.index-snapshot/decision`: one reason per
  mismatch class, and any non-nil reason discards the *whole* image and falls back to a
  rebuild.  The classes:

  * `:absent`          — no manifest (missing, or a save that never committed);
  * `:layout-changed`  — the snapshot format version, or `kv/index-layout-version`, is not
                         this build's (an index in another layout reads as *empty* rather
                         than wrong, which is the undiagnosable failure this forecloses);
  * `:records-differ`  — the manifest's records stamp is not the store's now (a different
                         KB, or the same one after a write);
  * `:entries-truncated` — a section is short or unreadable, caught while installing (a torn
                         nippy chunk is indistinguishable from a clean EOF, so truncation shows only as a
                         frame count below what the manifest recorded).

  There is no `:byte-order` class here, though `index-snapshot` has one: that image writes
  raw little-endian `int` runs, so an image from a machine of the other endianness must be
  refused; these sections are nippy frames, which are endian-neutral, so a byte-order
  mismatch cannot arise and the format version subsumes any encoding change.

  The stamp is `vaelii.impl.io.fingerprint`'s records digest, which **ports**: a `:disk`
  store hashes its slots, a `:memory` store folds its records, a SQL store answers a count
  — and all compare against the same manifest number.  Which digest a caller passes is its
  business; the sink only compares."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [taoensso.trove :as trove]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.snapshot :as snapshot-types
             :refer [SnapshotSink SnapshotSource commit! read-manifest read-section
                     write-section!]])
  (:import (java.io File)))

(def format-version
  "The snapshot's own layout number, beside `kv/index-layout-version` (which says what the
  section *entries* mean).  Bump when a section's shape or the manifest's shape changes."
  1)

(def index-section
  "The section name the index's `[key value]` projection is written under."
  "index")

;;; ── the sink protocol ──────────────────────────────────────────────────────

;;; ── the file target, over the shared framing ───────────────────────────

(def ^:private manifest-file "manifest.edn")

(defn- section-file ^File [^String root ^String name]
  (io/file root (str name ".nippy.stream")))

(defrecord FileSink [^String root compression chunk-size]
  SnapshotSink
  (write-section! [_ name frames]
    (let [^File f (section-file root name)]
      (io/make-parents f)
      (frames/write-frames! f frames {:compression compression :chunk-size chunk-size})))
  (commit! [_ manifest]
    ;; the compression rides the manifest, so the source reads the sections back without
    ;; being told; last, so its presence is the commit
    (let [^File f (io/file root manifest-file)]
      (io/make-parents f)
      (spit f (with-out-str
                (binding [*print-length* nil *print-level* nil]
                  (prn (assoc manifest :compression compression))))))))

(defn file-sink
  "A sink writing sections and a `manifest.edn` under `root`.  Opening it deletes any
  existing manifest, so from here until `commit!` the image reads as absent — the window
  in which a stale manifest could describe half-rewritten sections is closed by
  construction.  `:compression` defaults to `:none` (an image is a fast local cache, and
  the CPU a codec costs is usually the wrong trade for it); `:chunk-size` to 10000.

  **Bare, though it deletes a file.**  The `!` convention marks an operation the KB cannot
  take back (`docs/api.md`), and a manifest is an artifact of a cache rather than stored
  knowledge: dropping it costs a `reindex`, which is the fallback `load-index!` takes on
  any `decision` reason anyway.  Nothing a record holds is reachable through it.

  **And it belongs here rather than in `save-index!`.**  Invalidating before the first
  section is a property of *this* target — a directory of files, where the manifest and
  the sections are separate objects with a window between them.  A sink whose commit is
  one transactional write has no such window and needs no such step, and `save-index!`
  sits above the protocol and writes through whichever sink it is handed.  Moving the step up
  would mean a third protocol op every out-of-tree implementer had to grow, to say
  something two of the three targets have nothing to say about."
  ([root] (file-sink root {}))
  ([root {:keys [compression chunk-size] :or {compression :none chunk-size 10000}}]
   (let [^File d (io/file root)]
     (.mkdirs d)
     (.delete (io/file root manifest-file)))
   (->FileSink (str root) compression chunk-size)))

(defrecord FileSource [^String root manifest*]
  SnapshotSource
  (read-manifest [_]
    (let [^File f (io/file root manifest-file)]
      (when (.exists f)
        ;; a corrupt manifest is a different fact from an absent one, but the caller turns
        ;; both into the same rebuild; nil, and it rebuilds
        (try (edn/read-string (slurp f)) (catch Exception _ nil)))))
  (read-section [this name]
    (let [m (or @manifest* (reset! manifest* (read-manifest this)))]
      (frames/read-chunked-seq (section-file root name) (:compression m)))))

(defn file-source
  "A read-only source over a directory `file-sink` wrote.  Reads nothing until asked —
  `read-manifest` for the validity check, `read-section` for the install."
  [root]
  (->FileSource (str root) (atom nil)))

;;; ── the memory target, for tests and as a second real sink ─────────────

(defrecord MemoryMedium [state]
  ;; one object that is both sink and source over one atom, so a test writes and reads the
  ;; same image without a file — and, more than a convenience, the second target that keeps
  ;; the file sink honest: a section written here loads there and vice versa, which is the
  ;; portability the protocol exists to give.
  SnapshotSink
  (write-section! [_ name frames]
    (let [v (vec frames)]                       ; a memory image holds its frames, by nature
      (swap! state assoc-in [:sections name] v)
      (count v)))
  (commit! [_ manifest]
    (swap! state assoc :manifest manifest)
    nil)
  SnapshotSource
  (read-manifest [_] (:manifest @state))
  (read-section [_ name] (get-in @state [:sections name])))

(defn memory-medium
  "An in-heap snapshot medium, usable as both a `SnapshotSink` and a `SnapshotSource`.
  Holds the whole image in RAM — the price of being a test double and a portability oracle,
  not a scale target."
  []
  (->MemoryMedium (atom {:sections {} :manifest nil})))

;;; ── the index projection ───────────────────────────────────────────────

(defn index-frames
  "The index's entries as `[key value]` frames — the portable projection every backend
  shares (`p/index-entries`).  This streams what the store holds rather than deriving
  anything: a writer that called `index-sentex` would be `reindex` with extra steps,
  writing an index it had just computed instead of the one the KB was answering from.

  Each pair is normalized to a **vector**: the backends emit a mix of `MapEntry`s and plain
  vectors (the map-backed stores yield entries, the tiered one yields vectors, the columnar
  one yields both), and nippy gives `MapEntry` its own type id — so without this, two
  byte-identical logical indexes froze to byte-different streams according to which backend
  held them.  Shared verbatim with the export dump (`vaelii.impl.io.export`), so a dump's
  index and a standalone image are one projection rather than two."
  [index]
  (map (fn [[k v]] [k v]) (p/index-entries index)))

;;; ── validity ───────────────────────────────────────────────────────────

(defn index-mismatch
  "The content-validity core an index cache shares wherever it is stored: the layout it is
  keyed in, and the records it was derived from.  Returns `:layout-changed`,
  `:records-differ`, or nil.  Each container adds its own classes around this — an image
  (`decision`, below) adds `:absent` and a format-version check; a dump
  (`vaelii.impl.io.import/index-decision`) adds `:absent` and `:handles-remapped`.

  The **mapped** image is the one container that asks the same two questions inline
  rather than through here (`vaelii.impl.disk.index-snapshot/decision`): it interleaves a
  byte-order class between them, and orders the whole cond by what a reader needs told
  first rather than by what is cheapest to ask."
  [meta stamp]
  (cond
    (not= kv/index-layout-version (:index-layout meta)) :layout-changed
    (not= (:records meta) stamp)                        :records-differ
    :else                                               nil))

(defn decision
  "Why the image described by manifest `m` cannot be trusted against `stamp` (the store's
  current records fingerprint), or nil when it can.  The medium-agnostic reading of the
  question `vaelii.impl.disk.index-snapshot/decision` answers for a mapped image — that
  one draws its own truncation and platform classes from the files it maps and does not
  come through here.  The image is a cache, so any non-nil reason discards the whole of
  it and the caller rebuilds.  `:entries-truncated` is not decided
  here — a nippy stream's truncation is indistinguishable from a clean EOF, so it can only be caught while
  the section is installed, against the count the manifest recorded."
  [m stamp]
  (cond
    (nil? m)                                         :absent
    (not= format-version (:format m))                :layout-changed
    :else                                            (index-mismatch m stamp)))

(defn index-manifest
  "The manifest for an index image: the two format numbers, the records stamp it is valid
  against, and the section's frame count for the truncation check."
  [stamp entry-count]
  {:format       format-version
   :index-layout kv/index-layout-version
   :records      stamp
   :sections     {index-section {:count entry-count}}})

;;; ── save / load the index ──────────────────────────────────────────────

(def ^:private install-batch 10000)

(defn install-entries!
  "Install a stream of `[key value]` frames into `index` in bounded batches, returning the
  count installed.  Checked at the end, not realized first — an index image is several
  entries per record, so holding one to inspect it would cost more heap than the records
  did.  A frame that is not a `[key value]` pair throws; the caller's rebuild clears
  whatever was installed.

  Public because the two places an index arrives from a file — a snapshot section
  (`load-index!`, below) and a dump's `index/entries` stream (`vaelii.impl.io.import`) —
  are the same install and must stay one: same batch size, same refusal, same count to
  check against the manifest that vouches for the stream."
  [index frames]
  (let [n (volatile! 0)]
    (doseq [batch (partition-all install-batch frames)]
      (when-not (every? #(and (sequential? %) (= 2 (count %))) batch)
        (throw (ex-info (str "index entry stream holds "
                             (pr-str (first (remove #(and (sequential? %) (= 2 (count %)))
                                                    batch)))
                             ", which is not a [key value] pair — every entry of an index"
                             " section is a two-element sequential")
                        {:type :malformed-entry})))
      (vswap! n + (count batch))
      (p/index-load index batch))
    @n))

(defn save-index!
  "Write `index`'s projection through `sink` as the index section, then commit a manifest
  stamped with `stamp` (the records fingerprint).  Returns the committed manifest.

  The manifest is committed **after** the section, so a crash mid-write leaves an image
  with no manifest, which `load-index!` reads as `:absent` and rebuilds."
  [sink index stamp]
  (let [n        (write-section! sink index-section (index-frames index))
        manifest (index-manifest stamp n)]
    (commit! sink manifest)
    manifest))

(defn load-index!
  "Validate the image behind `source` against `stamp` (the store's current records
  fingerprint) and install its index section into `index`, or report why it was discarded.
  Returns `{:index :replayed :entries n}` or `{:index :rebuild :reason r}` with `r` one of
  `:absent :layout-changed :records-differ :entries-truncated`.

  The caller reindexes on any `:rebuild`, which is always legal because the index is derived
  state and this is a cache of it — and reindex clears the index first, so a partial install
  left by a truncated section is wiped.  `index` must be **empty** on entry, the same
  contract `p/index-load` carries."
  [source index stamp]
  (let [m (read-manifest source)]
    (if-let [why (decision m stamp)]
      {:index :rebuild :reason why}
      (let [expected (long (get-in m [:sections index-section :count]))
            frames   (volatile! nil)]
        (try
          (let [n (install-entries! index (vreset! frames (read-section source index-section)))]
            (if (= (long n) expected)
              {:index :replayed :entries n}
              (do (trove/log! {:level :warn :id ::index-short
                               :msg (str "snapshot index section holds " n " entries, the "
                                         "manifest records " expected " — rebuilding")})
                  {:index :rebuild :reason :entries-truncated})))
          (catch Exception e
            (trove/log! {:level :warn :id ::index-unreadable
                         :msg (str "snapshot index section unreadable (" (ex-message e)
                                   ") — rebuilding from the records")})
            {:index :rebuild :reason :entries-truncated})
          ;; an install that refused a frame stopped before the section's end, and the
          ;; file behind the seq is still open until somebody says so
          (finally (frames/close-frames! @frames)))))))
