;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.export
  "Write a KB out as a portable export dump: a directory holding the record store's streams
  in a format that survives a backend change, an index-representation change and a record
  class rename. A frame never carries a class name; it is the record's field map. `meta.edn`
  is written last and is the completion marker. The index is optional and always
  discardable. See docs/storage.md, \"Exporting and importing a dump\"."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.snapshot :as snapshot]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.progress :as progress]
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
  "What a writer emits: `:gzip` (the default), `:xz` and `:none`. The encoder is per chunk, so
  the peak is one encoder whatever the corpus. The reader also reads `:zstd` from a dump
  another tool wrote, and the writer does not emit it. Measurements: docs/storage.md,
  \"Exporting and importing a dump\"."
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

(defn ensure-empty-dir!
  "`dir` as an empty directory, created when it does not exist. A directory that already
  holds anything is refused with `:not-empty`, a file with `:not-a-directory`. `what`
  names the destination and `noun` the thing written, in the messages."
  ^File [dir what noun]
  (let [^File d (io/file dir)]
    (when (.isFile d)
      (throw (ex-info (str what " " (.getPath d) " is a file, not a directory")
                      {:type :not-a-directory :dir (.getPath d)})))
    (when-let [kids (seq (.listFiles d))]
      (throw (ex-info (str what " " (.getPath d) " is not empty ("
                           (count kids) " entries) — " noun " is a directory of its own")
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
  "The frame stream for `ids`: each record fetched by handle and written as its field map
  (`(into {} record)`, which drops the class name and positional layout). A rule frame adds
  `:sentence`, built by `sentex/sentence-of`. A handle whose record has gone is skipped.
  `tap`, when non-nil, is called with `[handle record]` per frame written, so the index
  fingerprint rides this walk. `r` is a `vaelii.impl.progress` reporter ticked once per
  handle."
  [store fetch ids tap r]
  (keep (fn [id]
          (progress/tick! r)
          (when-let [rec (fetch store id)]
            (when tap (tap id rec))
            (cond-> (into {} rec)
              (some? (:antecedent rec)) (assoc :sentence (sx/sentence-of rec)))))
        ids))

(defn- provenance-frames
  "The `[handle provenance-map]` frames for the handles that have one, a filter over the same
  walk. It covers justification handles as well as sentex ones, since provenance is keyed by
  handle and the two kinds share one counter. `r` is a progress reporter ticked once per
  handle."
  [store ids r]
  (keep (fn [id]
          (progress/tick! r)
          (when-let [prov (p/get-provenance store id)] [id prov]))
        ids))

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

(defn- jar-build
  "`<version> <revision>` off the engine jar's Maven descriptor, or nil when the descriptor
  is not inside a jar.  A checkout's `target/classes` copy names the last compile's
  revision, so a checkout reads its git HEAD instead."
  []
  (when-let [u (io/resource "META-INF/maven/com.vaelii/vaelii/pom.properties")]
    (when (= "jar" (.getProtocol ^java.net.URL u))
      (let [props (java.util.Properties.)]
        (with-open [in (io/input-stream u)] (.load props in))
        (some->> [(.getProperty props "version")
                  (some-> (.getProperty props "revision") str/trim not-empty
                          (as-> r (subs r 0 (min 12 (count r)))))]
                 (remove str/blank?) seq (str/join " "))))))

(defn- writer-id
  "How the writing build names itself in `meta.edn`: the `vaelii.build` system
  property or `VAELII_BUILD` when a build sets a build label (a blank one sets none), else
  the engine jar's version and revision, else the git HEAD of the working directory, else
  `dev`.
  Diagnostic only — a dump that will not read is first a question about which build
  wrote it."
  []
  (str "vaelii "
       (or (some-> (System/getProperty "vaelii.build") str/trim not-empty)
           (some-> (System/getenv "VAELII_BUILD") str/trim not-empty)
           (jar-build) (git-head) "dev")))

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
    (let [n (with-open [r (progress/start ::write-index
                                          "export: write the index entries"
                                          nil)]
              (frames/write-frames! (io/file idx-d frames/index-entry-file)
                                    (progress/each r (snapshot/index-frames index))
                                    frame-opts))]
      (spit (io/file idx-d frames/index-meta-file)
            (with-out-str
              (binding [*print-length* nil *print-level* nil]
                (prn (array-map :index-layout kv/index-layout-version
                                :entry-count  n
                                :records      fingerprint)))))
      n)))

(defn export!
  "Export `kb`'s records to `dir` as a portable dump, and return a summary `{:variant :records
  :sentexes n :justifications n :provenance n :index-entries n :bytes n :elapsed-ms n :dir
  \"…\"}`.

  `opts`: `{:variant :records|:records+index :compression :gzip|:xz|:none :chunk-size n
  :provenance? bool :belief? bool :on-progress f}`, defaults `:records`, `:gzip`, 10000, true
  and true. `:on-progress` is called with `{:phase :done :total}` at every chunk boundary, in
  phase order `:sentexes`, `:justifications`, `:provenance`, `:index-entries`, `:belief`,
  `:meta`; a callback that throws cancels the export and leaves a directory with no
  `meta.edn`. Handles are exported as they stand. `:records+index` also writes `index/`,
  with its fingerprint computed on the same walk as the sentex frames. `:belief? true` also
  writes `reasoning/` for a KB on the dense network with the default provers and solver; the
  summary's `:reasoning-image` is `:written`, `:not-writable` (also when the change clock
  moved during the export) or `:omitted`. `:provenance? false` omits the provenance stream,
  which is also omitted when no handle carries one. `dir` must not exist or must be empty
  (`:type :not-empty`). See docs/storage.md, \"Exporting and importing a dump\"."
  ([kb dir] (export! kb dir {}))
  ([kb dir {:keys [variant compression chunk-size on-progress provenance? belief?]
            :or   {variant :records compression :gzip chunk-size 10000
                   on-progress no-progress provenance? true belief? true}
            :as   opts}]
   (check-export-opts! opts)
   (check-compression! compression)
   (check-variant! variant)
   (let [t0       (System/nanoTime)
         clock    (observe/change-clock)
         ^File d  (ensure-empty-dir! dir "export destination" "a dump")
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
         ;; the reasoning image rides the same two walks: its fingerprint is the content
         ;; fingerprint of the sentexes and of the justifications this dump streams
         image?   (and belief? (reasoning-image/writable? kb))
         fprint   (when (or index? image?) (fp/accumulator))
         jprint   (when image? (fp/accumulator fp/justification-hash))
         sx-n (with-open [r (progress/start ::write-sentexes
                                            "export: write the sentexes"
                                            (count sx-set))]
                (frames/write-frames! (io/file d frames/sentex-file)
                                      (record-frames records p/get-sentex sx-ids fprint r)
                                      (assoc frame-opts :on-chunk (chunk :sentexes (count sx-set)))))
         j-n  (with-open [r (progress/start ::write-justifications
                                            "export: write the justifications"
                                            (count j-set))]
                (frames/write-frames! (io/file d frames/justification-file)
                                      (record-frames records p/get-justification j-ids jprint r)
                                      (assoc frame-opts
                                             :on-chunk (chunk :justifications (count j-set)))))
         ;; `seq` realizes only as far as the first handle carrying provenance, so a KB
         ;; with none writes no file rather than an empty one.  The total is unknown
         ;; until the walk ends — a filter over the record handles, not a stream with a
         ;; count of its own — so the phase reports progress against nil.
         p-n  (if provenance?
                (with-open [r (progress/start ::write-provenance
                                              "export: write the provenance"
                                              (+ (count sx-set) (count j-set)))]
                  (if-let [prov (seq (provenance-frames records (concat sx-ids j-ids) r))]
                    (frames/write-frames! (io/file d frames/provenance-file) prov
                                          (assoc frame-opts :on-chunk (chunk :provenance nil)))
                    0))
                0)
         i-n  (if index?
                (write-index! d (:index kb) (fprint)
                              (assoc frame-opts :on-chunk (chunk :index-entries nil)))
                0)
         image (when image?
                 (on-progress {:phase :reasoning-image :done 0 :total 1})
                 (reasoning-image/write-sections!
                  kb (io/file d reasoning-image/dir-name)
                  (reasoning-image/manifest-for kb {:sentexes (fprint) :justifications (jprint)})
                  #(= clock (observe/change-clock))))]
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
                     :reasoners           (vec (sort (kb/reasoners-of kb)))
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
