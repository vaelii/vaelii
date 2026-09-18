;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.export
  "Write a KB out as a portable **export dump** — a directory holding the record
  store's three streams, in a format that survives a backend change, an
  index-representation change, and a record class rename.

  The `:disk` store directory looks like an archive and is not one: it holds frozen
  *records*, so renaming a record class makes every frame in it thaw to a
  `{:nippy/unthawable …}` placeholder — silently, because a placeholder is a perfectly
  good map.  Hence the one non-negotiable rule of this format:

  > **A frame never carries a class name.**

  A frame is the record's **field map** — `(into {} record)`, a plain map — so a rename
  changes nothing a dump holds, and `vaelii.impl.io.import`'s `field-map` already
  accepts one.

  What a dump holds is what the record store holds, because everything else the KB has
  is derived from it: sentexes, justifications, and per-handle provenance.  A premise
  needs no stream of its own — a premise *is* a sentex whose `:strength` is non-nil, a
  field on the record in both backends, so the mark rides along with it.  The index is
  a cache (`reindex`), the taxonomy and the TMS labels are recomputed (`recover`).

      <dump>/
        meta.edn                     the marker, the schema, and the counts
        sentexes.nippy.stream        one frame per sentex
        justifications.nippy.stream  one frame per justification
        provenance.nippy.stream      [handle provenance-map] per frame (omitted when none)
        index/entries.nippy.stream   [key value] per frame — only in :records+index
        index/index.edn              the layout version + the records fingerprint

  **The index is optional and always discardable.**  `:variant :records+index` writes it
  as well, in the `[structured-key value]` projection every index backend shares
  (`p/index-entries`), so an index written by one backend loads into another.  It is a
  *cache*: a reader replays it only when it can prove the entries were derived from
  exactly the records beside them (`vaelii.impl.io.fingerprint`), and rebuilds otherwise.
  That is what makes writing it safe — an index that does not match its records is worse
  than no index, because every lookup then answers confidently and short.

  **Framing** is the chunked layout `vaelii.impl.io.frames` writes and reads: a
  run of `[int32 length][compressed chunk]`, each chunk an independent compression
  window over back-to-back nippy frames.  Constant memory on both sides — the writer
  holds one chunk, never the corpus.  `meta.edn` *states* the framing rather than
  implying it through a version number, because the engine's dumps number their own
  format and a reader must never have to guess.

  **`meta.edn` is written last**, which makes it double as the completion marker:
  `vaelii.browser.catalog/classify` keys on it, so a half-written or cancelled export is
  not offered as loadable.  That is the one ordering constraint in the whole format.

  Export from a KB nobody is writing: the walk fetches record by record, and the
  single-writer contract offers no snapshot to walk instead."
  (:require [clojure.java.io :as io]
            [taoensso.trove :as trove]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.snapshot :as snapshot]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as reasoning-image]
            [vaelii.impl.sentex :as sx])
  (:import (java.io File)
           (java.time Instant)))

(def format-marker
  "The dump's own marker.  The engine's dumps carry no `:format` and number their
  format on a line of their own, so ours announces whose it is rather than colliding
  with a foreign version space."
  :vaelii/export)

(def format-version
  "Version 1: field-map frames, chunked framing, handles preserved."
  1)

;; The stream names live in `vaelii.impl.io.frames`, shared with the import reader —
;; the two halves of the round trip must agree on the layout, so it is stated once.

(def variants
  "What a dump can hold.  `:records` is the whole KB — everything else is derived from
  the records and rebuilt on the way in.  `:records+index` adds the index as a cache the
  reader may or may not use; it never adds knowledge, only speed."
  #{:records :records+index})

;;; ── compression ───────────────────────────────────────────────────────

(def ^:private compressions
  "What a writer emits.  Measured on a 47k-sentex generated corpus: `:none` 5.2 MB in
  0.3s, `:gzip` 463 kB in 1.0s, `:xz` 331 kB in 2.4s.  So `:gzip` is the default — it
  eats most of what the field names cost, at a speed nobody notices — and `:xz`
  (LZMA2) buys another 28% for 2.3x the write, the trade a multi-gigabyte archive is
  usually willing to make.  Its encoder is **per chunk** — a chunk is its own compression
  window, which is what lets a reader decompress any one of them — so one is allocated and
  dropped per chunk rather than held for the stream, and `vaelii.impl.io.frames` sizes its
  dictionary to a chunk (`xz-dict-bytes`) so that allocation is 24 MB rather than 93.
  Either way the peak is one encoder, whatever the corpus.  `:none` is the opt-out.

  The reader additionally reads `:zstd` from a dump some other tool wrote, which is why
  it refuses it and we do not write it."
  #{:gzip :xz :none})

(defn- check-compression!
  "Refuse a codec we cannot write, **before** the destination directory exists — a
  failed export should leave nothing behind to clean up."
  [compression]
  (when-not (contains? compressions compression)
    (throw (ex-info (str "unknown compression " compression " — a dump is written "
                         (pr-str (sort compressions)))
                    {:type :unsupported-compression :compression compression
                     :supported compressions}))))

;;; ── the destination ───────────────────────────────────────────────────

(defn- ensure-empty-dir!
  "`dir` as an empty directory, created when it does not exist.  A directory that
  already holds anything is **refused**: a dump merged into another dump is not a
  dump — the streams would interleave two KBs' handles and `meta.edn` would count one
  of them."
  ^File [dir]
  (let [^File d (io/file dir)]
    (when (.isFile d)
      (throw (ex-info (str "export destination " (.getPath d) " is a file, not a directory")
                      {:type :not-a-directory :dir (.getPath d)})))
    (when-let [kids (seq (.listFiles d))]
      (throw (ex-info (str "export destination " (.getPath d) " is not empty ("
                           (count kids) " entries) — a dump is a directory of its own")
                      {:type :not-empty :dir (.getPath d)
                       :entries (mapv #(.getName ^File %) (take 8 kids))})))
    (.mkdirs d)
    d))

(defn- dir-bytes [^File d]
  (transduce (comp (filter (fn [^File f] (.isFile f)))
                   (map (fn [^File f] (.length f))))
             + 0 (file-seq d)))

;;; ── the frame streams ─────────────────────────────────────────────────

(defn- record-frames
  "The frame stream for `ids`: each record fetched by handle and written as its
  **field map**.  `(into {} record)` is a shape conversion, not a translation — a
  Clojure record is already a map — and it is what drops the class name and the
  positional layout, which is the whole point of the format.

  A rule frame adds `:sentence` — the `implies` form `sentex/sentence-of` builds from the
  record's `:antecedent` and `:consequent` — because a rule record holds no sentence and
  a dump's rule frame carries one, so the format a reader parses is the same whichever
  build wrote it.

  A handle whose record has gone is skipped rather than written as a hole, so the
  count `meta.edn` reports is the count the stream holds.

  `tap` (optional) is called with `[handle record]` for each frame written, so a caller
  that needs to see every record — the index fingerprint does — rides the walk the writer
  is already making rather than making a second one."
  ([store fetch ids] (record-frames store fetch ids nil))
  ([store fetch ids tap]
   (keep (fn [id]
           (when-let [rec (fetch store id)]
             (when tap (tap id rec))
             (cond-> (into {} rec)
               (some? (:antecedent rec)) (assoc :sentence (sx/sentence-of rec)))))
         ids)))

(defn- provenance-frames
  "The `[handle provenance-map]` frames for the handles that have one.  Provenance is
  optional per handle and belief never reads it, so this is a filter over the same walk
  rather than a stream the store could enumerate.

  **Justification handles as well as sentex ones.**  `core/add-provenance` writes under
  whatever handle it is given, the provenance store is keyed by handle rather than by
  kind, and the two kinds draw from one counter — so a walk over the sentexes alone
  drops every stamp a caller put on a firing."
  [store ids]
  (keep (fn [id] (when-let [prov (p/get-provenance store id)] [id prov])) ids))

;;; ── the marker ────────────────────────────────────────────────────────

(defn- git-head
  "The working tree's git HEAD, short, or nil when there is no readable one (an
  uberjar, a source drop).  Read from `.git` rather than shelled out to `git`."
  []
  (try
    (let [head (io/file ".git" "HEAD")]
      (when (.exists head)
        (let [line (.trim (slurp head))
              sha  (if (.startsWith line "ref: ")
                     (let [ref (io/file ".git" (subs line 5))]
                       (when (.exists ref) (.trim (slurp ref))))
                     line)]
          (when (seq sha) (subs sha 0 (min 12 (count sha)))))))
    (catch Exception _ nil)))

(defn- writer-id
  "How the writing build names itself in `meta.edn`: the `vaelii.build` system
  property or `VAELII_BUILD` when a build stamps one, else the git HEAD, else `dev`.
  Diagnostic only — a dump that will not read is first a question about which build
  wrote it."
  []
  (str "vaelii "
       (or (System/getProperty "vaelii.build") (System/getenv "VAELII_BUILD")
           (git-head) "dev")))

(defn- write-meta!
  "Write `meta.edn` — an array map, so the file reads in the order the schema is
  stated rather than in hash order."
  [^File d m]
  (spit (io/file d frames/meta-file)
        (with-out-str (binding [*print-length* nil *print-level* nil] (prn m)))))

;;; ── the entry point ───────────────────────────────────────────────────

(def ^:private no-progress (fn [_]))

(def ^:private export-opt-keys
  "Every key `export!` reads."
  #{:variant :compression :chunk-size :provenance? :belief? :on-progress})

(defn- check-export-opts!
  "Refuse an opts key `export!` does not read, and a non-nil non-map `opts` — before
  the value checks, and like them before the destination directory exists.
  `check-compression!` and `check-variant!` hold the *values* of two known keys; this
  is the key check beside them, and the failure it stops is quieter than a bad value:
  a misspelt `:varient` or `:provenence?` takes its default in silence and writes a
  dump other than the one asked for — no index where one was ordered, the unbounded
  provenance stream where it was dropped — under a summary that looks exactly right."
  [opts]
  (opts/check! opts export-opt-keys "export!"
               (str "An option nothing reads takes the default in silence,"
                    " which here writes a dump other than the one asked for."))
  ;; the one bound-domains value beside the two dump-shape checks: `:on-progress` is a
  ;; function, so a non-fn one is a bare cast on the first chunk boundary rather than the
  ;; typed refusal every sibling gives (`opts/bound-domains`)
  (opts/check-values! opts "export!"))

(defn- check-variant! [variant]
  (when-not (contains? variants variant)
    (throw (ex-info (str "unknown variant " variant " — a dump is written "
                         (pr-str (sort variants)))
                    {:type :unsupported-variant :variant variant :supported variants}))))

(defn- write-index!
  "Write the index dump: the entry stream, then `index.edn`.  Returns the entry count.

  `index.edn` is what makes the entries usable rather than merely present — the layout
  version they are keyed in, and the fingerprint of the records they were derived from.
  A reader with either answer different discards them.  It is written **after** the
  entries, for the same reason `meta.edn` is written last: a half-written entry stream
  with no `index.edn` beside it is read as a dump that simply has no index."
  [^File d index fingerprint frame-opts]
  (let [idx-d (io/file d frames/index-dir)]
    (.mkdirs idx-d)
    (let [n (frames/write-frames! (io/file idx-d frames/index-entry-file) (snapshot/index-frames index)
                                  frame-opts)]
      (spit (io/file idx-d frames/index-meta-file)
            (with-out-str
              (binding [*print-length* nil *print-level* nil]
                (prn (array-map :index-layout kv/index-layout-version
                                :entry-count  n
                                :records      fingerprint)))))
      n)))

(defn export!
  "Export `kb`'s records to `dir` as a portable dump, and return a summary:

      {:variant :records :sentexes n :justifications n :provenance n
       :index-entries n :bytes n :elapsed-ms n :dir \"…\"}

  `opts`: `{:variant :records|:records+index :compression :gzip|:xz|:none :chunk-size n
  :provenance? bool :on-progress f}` (defaults `:records`, `:gzip`, 10000 and true;
  `:xz` trades write speed for
  a materially smaller archive — compression is a stream wrapper around a whole chunk,
  orthogonal to the nippy encoding of the frames inside it).  `:on-progress` is called
  with `{:phase :done :total}` — the form a corpus reader's `load-dir!`,
  `io.import/import-dump` and `io.generate/load-into` report, so
  `vaelii.browser.catalog` draws a bar from it — at every chunk boundary, in phase order
  `:sentexes`, `:justifications`, `:provenance`, `:index-entries`, `:meta`.  A callback
  that **throws** is how a caller cancels: the throw propagates out of the phase it
  interrupted, leaving a directory with no `meta.edn`, which is not a loadable dump.

  Handles are exported as they stand — a justification names its antecedents by
  handle, and an `exceptWhen` meta-sentex names its rule by handle *inside a stored
  sentence*, so a dump that renumbered would have to rewrite content.

  `:records+index` additionally writes `index/`, whose entries are only ever a cache: the
  fingerprint beside them is computed on the **same walk** that writes the sentex frames,
  so a reader can tell whether they describe the records it just stored, and rebuild if
  not.  It is the expensive half of the dump and then some — measured at 6.2 entries per
  record and 3.8× the records' bytes, for a load twice as fast —
  so it is opt-in rather than the default.

  `:belief? true`, the default, also writes `reasoning/`: the KB's reasoning image
  (`vaelii.impl.reasoning-image`), stamped with content fingerprints of the sentexes and the
  justifications this dump streams, taken on the same two walks.  An import that lands
  exactly those records under the same source identity installs it in place of `recover`.
  It is written only for a KB on the dense network, with the default provers and solver,
  whose network covers its records; the summary's `:reasoning-image` is `:written`,
  `:not-writable` or `:omitted` (`:belief? false`).  A phase `:belief` reports it.

  `dir` must not exist or must be empty (`:type :not-empty`), and `meta.edn` is
  written **last**.  The provenance stream is omitted entirely when no handle carries
  provenance; the reader already treats it as optional.

  **`:provenance? false` omits it even when handles do carry it**, and it is not a
  micro-optimization: provenance is an open per-handle map an application layers whatever
  it likes into, so it has no size bound of its own and can dominate the records it
  annotates.  Measured on the converted engine KB — 10.2M sentexes — the provenance
  stream is 317.9 MB of a 556 MB dump, **57%, larger than the records**, and what it
  holds there is the extraction pipeline's own bookkeeping rather than anything a reader
  of the ontology wants.  Belief never reads provenance and the importer treats the
  stream as optional, so a dump without it is a complete KB, just an unannotated one;
  that makes this the right knob for a dump meant to be downloaded, and the wrong one for
  a backup."
  ([kb dir] (export! kb dir {}))
  ([kb dir {:keys [variant compression chunk-size on-progress provenance? belief?]
            :or   {variant :records compression :gzip chunk-size 10000
                   on-progress no-progress provenance? true belief? true}
            :as   opts}]
   (check-export-opts! opts)
   (check-compression! compression)
   (check-variant! variant)
   (let [t0       (System/nanoTime)
         ^File d  (ensure-empty-dir! dir)
         records  (:records kb)
         sx-set   (p/sentex-ids records)
         j-set    (p/justification-ids records)
         ;; the handles are sorted so a dump is a deterministic function of the KB
         ;; rather than of map iteration order.  Sorting realizes an integer per
         ;; record — the *records* are what streams, one chunk at a time.
         sx-ids   (sort sx-set)
         j-ids    (sort j-set)
         chunk    (fn [phase total]
                    (fn [done] (on-progress {:phase phase :done done :total total})))
         frame-opts {:compression compression :chunk-size chunk-size}
         index?   (= :records+index variant)
         ;; the fingerprint rides the sentex walk rather than making a second one —
         ;; the writer already fetches every record, and on `:disk` that is a page read
         ;; apiece
         ;; the reasoning image rides the same two walks: its stamp is the content
         ;; fingerprint of the sentexes and of the justifications this dump streams
         image?   (and belief? (reasoning-image/writable? kb))
         fprint   (when (or index? image?) (fp/accumulator))
         jprint   (when image? (fp/accumulator fp/justification-hash))
         sx-n (frames/write-frames! (io/file d frames/sentex-file)
                                    (record-frames records p/get-sentex sx-ids fprint)
                                    (assoc frame-opts :on-chunk (chunk :sentexes (count sx-set))))
         j-n  (frames/write-frames! (io/file d frames/justification-file)
                                    (record-frames records p/get-justification j-ids jprint)
                                    (assoc frame-opts :on-chunk (chunk :justifications (count j-set))))
         ;; `seq` realizes only as far as the first handle carrying provenance, so a KB
         ;; with none writes no file rather than an empty one.  The total is unknown
         ;; until the walk ends — a filter over the record handles, not a stream with a
         ;; count of its own — so the phase reports progress against nil.
         prov (when provenance?
                (seq (provenance-frames records (concat sx-ids j-ids))))
         p-n  (if prov
                (frames/write-frames! (io/file d frames/provenance-file) prov
                                      (assoc frame-opts :on-chunk (chunk :provenance nil)))
                0)
         i-n  (if index?
                (write-index! d (:index kb) (fprint)
                              (assoc frame-opts :on-chunk (chunk :index-entries nil)))
                0)
         image (when image?
                 (on-progress {:phase :reasoning-image :done 0 :total 1})
                 (reasoning-image/write-sections!
                  kb (io/file d reasoning-image/dir-name)
                  (reasoning-image/stamp kb {:sentexes (fprint) :justifications (jprint)})))]
     (on-progress {:phase :meta :done 0 :total 1})
     (write-meta! d (array-map
                     :format              format-marker
                     :format-version      format-version
                     :variant             variant
                     :dialect             :vaelii
                     :frames              :field-map
                     :framing             :chunked
                     :compression         compression
                     :sentex-count        sx-n
                     :justification-count j-n
                     :provenance-count    p-n
                     :index-entry-count   i-n
                     :reasoning-image     (some? image)
                     :handle-policy       :preserved
                     :written-at          (str (Instant/now))
                     :writer              (writer-id)))
     (let [summary {:variant        variant
                    :sentexes       sx-n
                    :justifications j-n
                    :provenance     p-n
                    :index-entries  i-n
                    :reasoning-image (cond image :written belief? :not-writable :else :omitted)
                    :bytes          (dir-bytes d)
                    :elapsed-ms     (quot (- (System/nanoTime) t0) 1000000)
                    :dir            (.getAbsolutePath d)}]
       (trove/log! {:level :info :id ::exported
                    :msg   (str "exported " sx-n " sentexes, " j-n " justifications"
                                (when index? (str ", " i-n " index entries"))
                                " to " (.getAbsolutePath d))
                    :data  summary})
       summary))))
