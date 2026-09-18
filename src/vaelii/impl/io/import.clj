;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.import
  "Import a vaelii **export dump** — a directory of record streams — into a KB,
  landing in exactly the state the engine's own restart path (`reindex` / `recover`) already
  knows how to produce.

  A dump is a directory whose `meta.edn` is the marker and schema; every other file is
  a nippy stream:

      sentexes.nippy.stream        one field-map frame per sentex
      justifications.nippy.stream  one per justification
      provenance.nippy.stream      [handle map] per frame — optional

  A `:records+index` dump also carries the index, as a **cache** that is used only when
  it can be proved to describe the records that were just stored (see *the index* below);
  otherwise the index is rebuilt, and the summary says which happened and why.

  **Framing.**  A chunked stream is a run of `[int32 length][compressed chunk]`, each
  chunk a compression window over back-to-back nippy frames; a window stream is one
  compression window over the lot.  Our own dumps **state** which (`:framing`); a
  foreign dump's is inferred from its own version line.  Both are constant-memory lazy
  seqs.

  **A frame of our own dialect is a plain field map** whose `:sentence` is already
  there — but a rule's `set/*Rule` wrappers and its variable names canonicalized *into*
  the record (`:direction` / `:defeasible` / `:varmap`), so both are written back around
  it before the constructor sees it.  A frame that is *not* ours goes to a foreign
  reader (`vaelii.impl.foreign`), which is resolved at runtime and may not be in the
  build at all.  The discrimination is on the **frame**, never on `meta.edn`'s
  `:dialect`: a declaration is not an authority over the bytes beside it, and keying off
  the frame keeps a mixed dump readable.

  Whatever the dialect, **every sentence is re-canonicalized** through this build's own
  constructor (`res/kb-sentex`).  A stored canonical form is never trusted, not even
  our own: variable numbering, symmetric argument order and comparison folding belong to
  the *reading* build, and a record indexed under a key this build's `lookup` never
  reproduces would be silently unfindable.

  **Handles are preserved** for a dump of ours: every record is stored at the handle the
  dump gave it, so a handle means the same thing either side of an export.  Safe because
  the destination must be empty and because a store's counter clears any handle written
  that way (`p/next-id`) — without which the next `assert` would mint handle 1 again and
  overwrite the first imported record.  Two things can still stop a handle landing as
  given, and neither is silent: a frame with no `:id`, and a frame whose canonical form
  is one already stored, which **collapses** onto that handle (a dedup this build is
  right to perform — two engine forms can canonicalize to one stored record — and the
  dump's numbering cannot survive it).  Either makes the import `:remapped`, and then one
  `old->new` map carries the dump's ids across: justification references, and the
  `(sentexHandle H)` a meta-sentex embeds *inside stored content*, which
  `rewrite-embedded-handles!` rewrites in the sentence.  A meta-sentex whose embedded
  handle cannot be resolved is **dropped**, and the drop reaches the map as well as the
  store (`forget-deleted`): a dump id whose record is gone has to stop resolving, or the
  references to it resolve to a handle nothing is stored at.

  **The index is replayed only when it can be proved to fit**, and discarding it is
  always safe — which is what makes a cache out of what would otherwise be a risk.  An
  index that does not match its records is *worse* than no index: every lookup then
  answers confidently and short, and nothing in the engine is positioned to notice.  So
  all three of these must hold (`index-decision`):

  * the entries are keyed in the layout this build reads (`kv/index-layout-version`);
  * the fingerprint accumulated **while storing** equals the one written beside the
    entries (`vaelii.impl.io.fingerprint`) — accumulated, not recomputed, since a second
    pass over the records to validate a cache would cost more than the cache saves;
  * the handles were preserved, so a posting names the record it named in the source.

  Anything else rebuilds, at `:info`, with the reason named.  A cache that silently
  stops being used is a cache nobody maintains.

  The store-facing replay is written against the engine's real protocols: populate the record
  store with the re-canonicalized records + justifications + premise marks, then either
  install the dumped index (`p/index-load`) or rebuild it (`reindex`), then
  `core/recover` — which rebuilds the JTMS and the taxonomy **from the records**, so a
  replayed index shortcuts the index and nothing else.  Out of scope: the `:pg-memory`
  variant."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.snapshot :as snapshot]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as ri]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as st]))

(def export-format
  "The marker `vaelii.impl.io.export` writes.  Version numbers alone cannot tell a dump
  of ours from a foreign one — ours starts at 1, which sits inside numbering somebody
  else was already using — so the dialect is named rather than deduced."
  :vaelii/export)

(def supported-export-versions
  "Export-format versions this build reads."
  #{1})

(defn- ours?
  "Is this `meta.edn` one of ours?  Governs which streams are read and how a frame's
  premise mark is decided; the *frame* still decides how a sentence is reconstructed."
  [meta]
  (= export-format (:format meta)))

(def manifest-bytes
  "The most an EDN **manifest** may hold — a dump's `meta.edn`, a store's `format.edn`, a
  corpus's `report.edn`, an index's `index.edn`, a machine's `catalog.edn`.

  Every one of them is a handful of keys: a marker, a version, some counts, a
  compression name.  They are also the *first* thing read about a directory nobody has
  promised anything about — `vaelii.browser.catalog` probes every entry of the KB search
  path this way, and a load reads one before it opens a stream — so an unbounded read is
  a whole file pulled into a string on the strength of its name.  A megabyte is orders
  of magnitude above the largest of them (a hand-written `catalog.edn` naming thousands
  of KBs) and still a bound."
  (* 1024 1024))

(defn read-edn-manifest
  "The EDN manifest in `f`, read under `manifest-bytes` — or a refusal
  (`:manifest-too-large`) naming the file and the bound.

  **The bound is on the read, not on the file's stated length.**  `File.length` answers
  0 for a FIFO and for most of `/proc`, and a symlink to one of those is a `slurp` that
  never ends; reading a bounded number of bytes and refusing the one past the bound
  needs the file to say nothing true about itself.  Bytes rather than characters, so the
  figure the refusal states is the figure that was read.

  Content the EDN reader cannot parse is refused by name too (`:malformed-manifest`).
  A manifest cut mid-form — the form a crashed writer and a half-copied directory both
  leave — otherwise raises a bare `RuntimeException` (\"EOF while reading\"), which is
  neither a `:type` a caller can discriminate on nor a fact about the file it names.
  Which of the two refusals means \"not a KB\" and which means \"a broken one\" is the
  caller's to decide, and `vaelii.browser.catalog` decides it differently from the loaders."
  [f]
  (let [^java.io.File f (io/file f)
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
                           " bytes — a meta.edn / format.edn / report.edn / catalog.edn"
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

;; The stream names live in `vaelii.impl.io.frames`, shared with the export writer —
;; the two halves of the round trip must agree on the layout, so it is stated once.

;;; ── stream readers ────────────────────────────────────────────────────
;;; The chunked/window nippy framing itself lives in `vaelii.impl.io.frames`, shared
;;; with the export writer and the snapshot sink; what stays here is the dump-specific
;;; policy of choosing a reader from a dump's own `meta.edn` (`stream-reader-for`).

(defn- check-frame-count!
  "Refuse a stream that ended early.  A torn chunk is indistinguishable from a clean EOF — the
  decompressor cannot tell a truncated file from a finished one — so the only witness
  a truncated dump leaves is the count `meta.edn` states, and this is the same
  comparison `replay-index!` makes for the index entries.  Nil `stated` (a dump that
  states no count) checks nothing.

  `n` is what the **stream yielded**, not what got stored: a frame this build refuses
  (below) and a frame that collapses onto a handle already stored both leave the store
  shorter than the dump, and neither is a torn file."
  [what n stated]
  (when (and stated (< (long n) (long stated)))
    (throw (ex-info (str "the dump states " stated " " (name what) " and the stream"
                         " ended after " n " — a torn or truncated dump")
                    {:type :truncated-dump :kind what :read n :stated stated}))))

;;; ── frames this build will not construct ──────────────────────────────────
;;; The structural checks `sentex` runs — NAF closure, quantifier locality, the
;;; aggregate reduction slots — are not the same question as whether the corpus is
;;; loadable, and a dump is not a program being written.  A rule stored by an older
;;; build, or by another engine, can be one this build's checks refuse; there is no
;;; record to store when they do, since the check runs inside the constructor.
;;;
;;; The naming path settled the policy for the other entry point already: a name `assert`
;;; would refuse is stored, counted, and reported, because a store the public entry point
;;; disagrees with is a *fact about that store* rather than a reason to have no store.
;;; The structural entry point gets the same treatment for the same reason, and the argument
;;; is sharper here — one refusal aborting the load discards a finished multi-hour pass
;;; over millions of good frames to punish a record nobody can fix from this end.

(def ^:private empty-refusals
  "A fresh refusal accumulator: frames this build would not construct a sentex from,
  by the `:type` their `ex-info` carries.  `:checked` is filled in from the frame count
  at the end rather than incremented, so it cannot drift from it."
  {:checked 0 :skipped 0 :by-type {}})

(defn- tally-refusal
  "Fold one refused frame into `t`, under the `:type` its refusal was raised with."
  [t refusal-type]
  (-> t
      (update :skipped inc)
      (update :by-type #(update % refusal-type (fnil inc 0)))))

(defn- dump-disagreement
  "The `:type` `e` was raised with, when `e` is a refusal this build **meant** — a check
  saying the dump holds something it will not construct.  Nil when it carries no `:type`,
  which is not a disagreement about the dump but an unlabelled failure inside the loader,
  and the caller rethrows those rather than counting them.  Tolerating an exception
  nobody chose to raise is how a bug becomes a statistic."
  [^clojure.lang.ExceptionInfo e]
  (:type (ex-data e)))

(defn- refusal-line
  "The one line a load prints about `t`, or nil when every frame built — which is the
  common case and deserves no output at all."
  [t]
  (let [{:keys [checked skipped by-type]} t]
    (when (pos? (long skipped))
      (str (format "%,d of %,d frames (%.3f%%) hold sentences this build will not "
                   (long skipped) (long checked)
                   (* 100.0 (/ (double skipped) (double (max 1 checked)))))
           "construct: "
           (str/join ", " (for [[c n] (sort-by val > by-type)]
                            (str (name c) " " (format "%,d" (long n)))))
           " — they are not stored, and anything resting on one is dropped with it"))))

(defn- stream-reader-for
  "The reader for a dump's stream files.  One of ours **states** its framing, because a
  version number already means something else here; a foreign dump's is inferred from
  its own version line — v6+ chunked, v4/v5 single-window.  The inference is for a
  dump that states *nothing*: a `:framing` this build does not know is a declared
  field of the frozen format holding a value from some other build, and guessing a
  reader for it fails later as a decompression error with no `:type` — so it is
  refused up front, the way an unknown `:compression` is.

  The framing itself is `vaelii.impl.io.frames`'; this only chooses which of its two
  readers a dump's own `meta.edn` calls for."
  [meta]
  (case (:framing meta)
    :chunked frames/read-chunked-seq
    :window  frames/read-window-seq
    nil      (if (>= (long (:format-version meta 0)) 6)
               frames/read-chunked-seq frames/read-window-seq)
    (throw (ex-info (str "unknown dump :framing " (pr-str (:framing meta))
                         " — this build reads :chunked and :window")
                    {:type :unknown-framing :framing (:framing meta)}))))

;;; ── meta + gates ──────────────────────────────────────────────────────

(defn read-meta
  "Read a dump's `meta.edn` (the marker + schema) without loading any records — under
  `manifest-bytes`, since a dump directory is whatever an operator copied."
  [dir]
  (let [^java.io.File f (io/file dir frames/meta-file)]
    (when-not (.exists f)
      (throw (ex-info (str "no dump at " (.getPath f) " (missing meta.edn)")
                      {:type :no-dump :dir (str dir)})))
    (read-edn-manifest f)))

(defn- dump-reader-field
  "The `field` of the `:engine-dump` reader map, or a refusal **by name** when the reader
  resolves but declares no such field.  A dump reader offers `{:name :versions :decode-frame
  :replay-belief!}` (docs/foreign.md); a plugin that ships a map missing one is refused with
  `:no-foreign-reader` here rather than dereferenced as nil several frames on — the same
  treatment `frame-decoder`'s `if-let` already gives `:decode-frame`.  `foreign/reader!`
  throws first when nothing reads the kind at all, so this only guards the field-absent case."
  [field]
  (or (field (foreign/reader! :engine-dump))
      (throw (ex-info (str "the :engine-dump foreign reader is on the classpath but its reader"
                           " map declares no " field " — a dump reader offers"
                           " {:name :versions :decode-frame :replay-belief!}"
                           " (see vaelii.impl.foreign)")
                      {:type :no-foreign-reader :kind :engine-dump :missing field}))))

(defn- assert-supported-version!
  "Gate the version against the numbering its own dialect uses — the two overlap, so one
  set would read our v1 as an unsupported foreign v1.  A foreign dump's numbering belongs
  to its reader, so it is asked (and its absence is what refuses the dump)."
  [meta]
  (let [ours      (ours? meta)
        supported (if ours
                    supported-export-versions
                    (dump-reader-field :versions))
        vn        (:format-version meta)]
    (when-not (supported vn)
      (throw (ex-info (str (if ours "export" "foreign") " dump format version " vn
                           " is not supported by this build (supports " supported ")")
                      {:type :unsupported-version :found vn :supported supported})))))

(defn- assert-empty-destination! [kb]
  (let [n (cap/count-sentexes (:records kb))]
    (when (pos? n)
      (throw (ex-info (str "destination KB is not empty (" n " sentexes); import expects "
                           "a fresh KB to avoid id collisions — clear the store first")
                      {:type :not-empty :sentex-count n})))))

;;; ── frame decode ──────────────────────────────────────────────────────

(defn- our-sentence
  "The sentence for a frame **our own writer** produced, as its author wrote it — which
  is what the constructor takes, and is not quite what the frame stores.

  Two things ride beside a rule's `:sentence` rather than in it, and both have to be put
  back or they are lost silently.  The `set/*Rule` wrappers canonicalized into
  `:direction` / `:defeasible` / `:assumption` / `:constraint`, so they go back around it
  (`rules/rewrap`) — handing over the bare sentence would turn every defeasible forward
  rule into a bare bidirectional one.  And the variables were renumbered to `?var0…`,
  with `:varmap` holding the names the author used, so those go back in
  (`sentex/originalize`) — re-canonicalizing the numbered form instead would rebuild the
  rule correctly and leave it displaying as `?var0` forever.  A fact carries neither: its
  `not` is already in its sentence.

  A rule frame carries `:sentence` beside `:antecedent` / `:consequent` (`io.export`
  writes it); one carrying only the two fields is rebuilt from them (`rule-sentence`)."
  [{:keys [sentence antecedent consequent varmap direction defeasible assumption constraint]}]
  (if (some? antecedent)
    (-> (sx/originalize (or sentence (sx/rule-sentence antecedent consequent)) varmap)
        (rules/rewrap direction defeasible assumption constraint))
    sentence))

(defn- frame-decoder
  "A `frame -> {:id :context :sentence :strength …}` decoder for this import.

  A map carrying `:sentence`, or a rule's `:antecedent`, is ours and is decoded here;
  anything else is a foreign
  dialect's and goes to its reader, resolved **once** (a `delay`, not a lookup per
  frame — this runs once per frame in the dump) and possibly not there at all, which is the honest error
  for a build that has finished with that format.

  The discrimination is on the frame rather than on `meta.edn`'s `:dialect`, so a
  declaration cannot be wrong about the bytes beside it and a mixed dump stays readable."
  []
  (let [foreign-decode (delay (:decode-frame (foreign/reader :engine-dump)))]
    (fn [frame]
      (if (and (map? frame) (or (contains? frame :sentence) (contains? frame :antecedent)))
        (assoc frame :sentence (our-sentence frame))
        (if-let [decode @foreign-decode]
          (decode frame)
          (throw (ex-info (str "this build reads only vaelii export dumps — the frame is "
                               "not one, and no foreign reader is present "
                               "(see vaelii.impl.foreign)")
                          {:type :no-foreign-reader :kind :engine-dump})))))))

;;; ── strength ──────────────────────────────────────────────────────────

(defn- strength-class
  "Map a dump's assumption strength onto this build's two-class lattice: `:monotonic`
  survives, everything else (`:default` / `:assumption` / `:uncomputed` / nil) is
  `:default`.  Passed to a foreign replay rather than reimplemented there, so a lattice
  change lands in one place."
  [s]
  (if (= s :monotonic) :monotonic :default))

;;; ── progress ──────────────────────────────────────────────────────────
;;
;; A dump of this size loads for minutes, so the streaming passes report how far in they
;; are.  The report is a **callback**, not a log line, because a caller driving the load
;; from a UI needs the number rather than the text — and because a callback that throws
;; is how that caller **cancels**: the throw propagates out of the pass it interrupted,
;; leaving the KB holding what had already landed (an import is not a transaction).

(defn- ticker
  "A per-frame counter that calls `on-progress` every `every` frames with
  `{:phase :done :total}`.  Returns the tick fn; `(tick!)` counts one frame."
  [on-progress phase total every]
  (let [n (volatile! 0)]
    (fn []
      (let [c (long (vswap! n inc))]
        (when (zero? (rem c (long every)))
          (on-progress {:phase phase :done c :total total}))
        c))))

(def ^:private no-progress (fn [_]))

;;; ── the record passes ─────────────────────────────────────────────────

(defn- embeds-handle?
  "Does `sentence` name another sentex by handle anywhere inside it?  An `exceptWhen`
  meta-sentex does — `(exceptWhen <query> (sentexHandle H))` — and a handle in *content*
  is a reference an id map cannot reach on its own."
  [sentence]
  (boolean (some sx/sentex-handle? (tree-seq sequential? seq sentence))))

(defn- import-sentexes!
  "Stream the sentex frames: decode each to a readable sentence, re-canonicalize through
  `res/kb-sentex`, and store it.  Two dump forms that canonicalize to one canonical form
  dedup to one handle (a local `[sentence context] -> handle` map), so a dump id is never
  assumed to survive 1:1.

  For a dump of **ours** the record is stored at the handle the dump gave it rather than at
  a freshly minted one, which is what makes an id in the dump mean something.  It is safe
  because the destination is empty (`assert-empty-destination!`) and because the counter
  now clears any handle written this way (`p/next-id`).  Two things can still stop a
  handle landing as given, and both are counted rather than hidden: a frame carrying no
  `:id` has none to preserve, and a frame whose canonical form is one already stored
  **collapses** onto that handle — a dedup this build is right to perform and the dump's
  numbering cannot survive.  `:collapsed` is counted in either dialect, since it is a
  fact about the frames rather than about the policy.

  Returns `{:sx-meta {dump-id {:handle h :rule? bool :strength s}} :embedding #{handle}
  :collapsed n :minted n :frames n :refused {…} :fingerprint {…} :naming {…}}` — the source
  of the old→new id map
  and the premise decisions, plus the handles whose stored content names another sentex
  (needing a rewrite once the map is complete, unless every handle was preserved and the
  map is the identity), plus the fingerprint of what was stored and the count of what the
  public entry point would have refused, both accumulated **here** because this is the one pass
  over the records a reader gets.

  A frame whose sentence this build will not construct is **counted in `:refused` and
  skipped**, so it reaches neither the store nor `sx-meta`.  Anything the deduction
  streams hang off it therefore fails to resolve and is dropped by the pass that reads
  them, which is the behaviour those passes already have for a dangling reference.
  `:strength` is the frame's own, unnormalized: the dialects read it differently (in one
  of ours it *is* the premise mark; in a foreign dump its own account of what rests on
  what decides)."
  [kb frames decode ours? tick!]
  (let [records   (:records kb)
        seen      (volatile! {})         ; [sentence context] -> handle
        sx-meta   (volatile! {})
        embed     (volatile! #{})
        collapsed (volatile! 0)
        minted    (volatile! 0)
        frames-n  (volatile! 0)          ; what the stream yielded, for the torn check
        naming    (volatile! nm/empty-tally)
        refused   (volatile! empty-refusals)
        fprint    (fp/accumulator)]
    ;; `:premises? false`: the marks are not the records' own strengths on this path.
    ;; A dump id that collapses onto a handle already stored keeps the **strongest** of
    ;; the strengths that landed there (`mark-premises-by-strength`, once the whole
    ;; stream is read), where the record carries the first frame's — so the mark is an
    ;; aggregate this write cannot know, and the sink is told not to make it.
    ;;
    ;; The frame stream is closed beside the sink (`frames/closer`): `tick!` throws when a
    ;; caller cancels and a duplicate handle throws below, and a frame seq only closes its
    ;; file when it is consumed to the end or raises the failure itself.
    (with-open [^java.io.Closeable sink   (cap/sentex-sink records {:premises? false})
                ^java.io.Closeable _stream (frames/closer frames)]
      (doseq [frame frames]
        (tick!)
        (vswap! frames-n inc)
        (let [fm    (decode frame)
              _     (vswap! naming nm/tally (:sentence fm) (:context fm))
              did   (:id fm)
              ;; born carrying its strength, so the premise pass below has nothing to
              ;; re-store: a premise **is** a sentex whose `:strength` is non-nil, and
              ;; storing it strength-less and marking it after is two record writes per
              ;; premise — 1.14M of them on OpenCyc, the first dead as the second lands.
              ;; **Ours only**: in a foreign dump a frame's `:strength` is not the premise
              ;; mark — that dialect's own account of what rests on what decides, and its
              ;; reader applies it — so carrying it onto the record here would make every
              ;; imported *derivation* a premise.
              ;;
              ;; A sentence this build's structural checks refuse yields no record at all,
              ;; so the frame is counted and skipped rather than taking the load down with
              ;; it.  Only around the construction, and only a refusal carrying a `:type`:
              ;; a failure to *store* is this build's problem rather than the dump's, and
              ;; so is any exception nobody chose to raise.
              rec   (try
                      (cond-> (res/kb-sentex kb (:sentence fm) (:context fm)) ; id nil
                        (and ours? (:strength fm))
                        (assoc :strength (strength-class (:strength fm))))
                      (catch clojure.lang.ExceptionInfo e
                        (if-let [ty (dump-disagreement e)]
                          (do (vswap! refused tally-refusal ty) nil)
                          (throw e))))]
          (when rec
            (let [k [(sx/sentence-of rec) (:context rec)]
                  h (if-let [prior (get @seen k)]
                      (do (vswap! collapsed inc) prior)
                      (let [hh (if (and ours? did)
                                 (do
                                   ;; a handle is an identity, so a second frame claiming
                                   ;; one already stored is a broken dump — and writing it
                                   ;; would destroy the first record with nothing to show
                                   ;; for it.  Equal content never reaches here; `seen`
                                   ;; has already collapsed it.
                                   (when (contains? @sx-meta did)
                                     (throw (ex-info (str "dump names handle " did " twice, "
                                                          "with different content")
                                                     {:type :duplicate-handle :handle did})))
                                   (p/write-record! sink (assoc rec :id did)))
                                 (do (when ours? (vswap! minted inc))
                                     (p/write-record! sink rec)))]
                        (vswap! seen assoc k hh)
                        (fprint hh rec)                  ; only what actually got stored
                        hh))]
              (when (embeds-handle? (sx/sentence-of rec)) (vswap! embed conj h))
              (when did
                (vswap! sx-meta assoc did {:handle   h
                                           :rule?    (some? (:antecedent rec))
                                           :strength (:strength fm)})))))))
    {:sx-meta @sx-meta :embedding @embed :collapsed @collapsed :minted @minted
     :frames @frames-n
     :refused (assoc @refused :checked @frames-n)
     :fingerprint (fprint) :naming @naming}))

(defn- rewrite-embedded-handles!
  "Rewrite the `(sentexHandle <dump-id>)` terms *inside stored content* to the handles
  those records landed at.  A meta-sentex names the rule it qualifies by handle in its
  own sentence, so the id map does not reach it, and a dump id left as it stands would
  name whatever unrelated record this KB has minted at that number — an exception
  silently attached to the wrong rule.  A reference the map cannot resolve is not left
  dangling either: the meta-sentex is dropped, an exception on a rule that is not here
  being an exception on nothing.

  Only a **remapped** import runs this.  When the handles were preserved the id map is
  the identity, so the embedded number already names the record it named in the source
  and there is nothing to rewrite — which is the point of preserving them.

  Returns `{:rewritten n :dropped n :deleted #{handle}}`, and the deleted handles are
  not a statistic.  They are records this import stored and has now removed, while
  `old->new` — built from `sx-meta`, which a delete does not touch — goes on resolving
  their dump ids: every later reference to one lands on a handle the store no longer
  holds.  So the caller takes them out of the map (`forget-deleted`) before anything
  reads it."
  [kb handles old->new]
  (let [records   (:records kb)
        rewritten (volatile! 0)
        deleted   (volatile! (transient #{}))]
    (doseq [h handles :let [rec (p/get-sentex records h)] :when rec]
      (let [resolved (volatile! true)
            sentence (walk/postwalk
                      (fn [x]
                        (if-let [id (sx/handle-id x)]
                          (if-let [n (get old->new id)]
                            (sx/sentex-handle n)
                            (do (vreset! resolved false) x))
                          x))
                      (:sentence rec))]
        (if @resolved
          (do (p/put-sentex records (assoc (res/kb-sentex kb sentence (:context rec))
                                           :id h :strength (:strength rec)))
              (vswap! rewritten inc))
          (do (p/delete-sentex! records h)
              (vswap! deleted conj! h)))))
    (let [gone (persistent! @deleted)]
      {:rewritten @rewritten :dropped (count gone) :deleted gone})))

(defn- forget-deleted
  "`sx-meta` and `old->new` with every dump id whose record `rewrite-embedded-handles!`
  deleted taken out of both, and the set of ids that removes — `{:sx-meta m :old->new m
  :orphaned #{dump-id}}`.

  A meta-sentex is dropped because the rule it qualifies is not in this KB, and the drop
  has to reach the id map or the import trades one dangling reference for another: the
  handle *inside stored content* resolves, and every reference to the dropped record
  itself resolves to a number nothing is stored at.  A justification assembled from one
  rests on nothing, and no reader downstream can tell — a store answers a missing handle
  the way it answers any handle it does not hold.

  Which is the whole of the repair, because failing to resolve is a case both deduction
  readers already handle: `import-justifications!` and a foreign reader's `replay-belief!`
  each drop a justification whose reference comes back nil, and count it.  The id map is
  where a deleted record has to stop existing.

  It reaches `sx-meta` for the same reason one step over: the premise marks are read off
  `sx-meta`, and a deleted handle in there is a premise the store declines to mark
  (`mark-premise` will not mark a handle with no record) while the count reports it as
  one."
  [sx-meta old->new deleted]
  (if (empty? deleted)
    {:sx-meta sx-meta :old->new old->new :orphaned #{}}
    (let [orphaned (into #{}
                         (comp (filter (fn [[_ h]] (contains? deleted h))) (map key))
                         old->new)]
      {:sx-meta  (persistent! (reduce dissoc! (transient sx-meta) orphaned))
       :old->new (persistent! (reduce dissoc! (transient old->new) orphaned))
       :orphaned orphaned})))

(defn- orphan-line
  "The one line a load prints about the meta-sentexes it dropped, or nil when it dropped
  none — which is every import that resolved every embedded handle, and the common case.

  Counted and said out loud for the reason the refusals are: the records are gone from
  the store, the justifications resting on them are gone with them, and an operator who
  reads only `:dropped-justifications` cannot tell which of those two the load did."
  [{:keys [dropped orphaned justifications]}]
  (when (pos? (long dropped))
    (str (format "%,d meta-sentexes name a rule this dump does not carry and are dropped"
                 (long dropped))
         (format ", leaving %,d dump ids naming nothing" (long orphaned))
         (if (pos? (long justifications))
           (format " — %,d justifications rest on one and are dropped with them"
                   (long justifications))
           " — no justification rests on one"))))

;;; ── what rests on what ────────────────────────────────────────────────
;;
;; Our own dump says this directly, which is most of what makes it ours: a justification
;; is a justification rather than something to be classified, and a premise is a sentex
;; whose `:strength` is non-nil rather than a marker record to be recognized.  A foreign
;; dialect's account is read by its own reader (`vaelii.impl.foreign`), which is handed
;; the id map and hands back the same three counts.

(defn- assert-no-naf-justifications!
  "Refuse a dump whose `Justification` frame carries a non-empty `:out`
  (`:naf-justification`), reading the stream for nothing else.

  A `Justification` has no out-list: NAF is re-evaluated rather than stored
  (docs/naf.md), and the relabel reads a justification's antecedents and its rule and
  nothing else — `region-fixpoint`'s semi-naive warrant is that `valid?` is monotone in
  `in`, which a justification invalidated by a datum *entering* is not.  A dump frame is
  a field map, so it can carry an `:out` key, and a non-empty one names
  negation-as-failure antecedents this build has nowhere to put: imported without them,
  the justification would support its conclusion where the exporting KB's did not.
  Refused rather than dropped: a dropped justification takes belief with it just as
  silently.

  **A pre-pass, because a refusal in the middle of a write is not a refusal.**  Read
  from `import-justifications!`' own loop it fired after the whole sentex phase had
  landed and after every preceding frame had been stored — and `import-dump` is not a
  transaction, so the store kept the sentexes and an arbitrary prefix of the
  justifications, with no premise marks and no `recover`.  `assert-empty-destination!`
  then refused the retry until the operator cleared the KB by hand, for a dump this
  build was never going to accept.  The frames come off a file, so they can be read
  before the first write instead, which costs one extra streaming pass over
  `justifications.nippy.stream` and buys a refusal the caller can act on.

  Called by `import-dump` for a dump of ours on the belief path — the only path that
  reads this file at all.

  **The stream is closed here**, refusal or not.  This pass exists to throw out of the
  middle of a walk, and a frame seq only closes its file when it is consumed to the end
  or raises the failure itself — so the one exit this function is written for is exactly
  the one that would leave the descriptor open."
  [frames]
  (try
    (doseq [frame frames]
      (when (seq (:out frame))
        (throw (ex-info (str "the dump names a justification with a non-empty :out "
                             (pr-str (vec (:out frame))) " — a justification here has no"
                             " negation-as-failure antecedent list, so imported without"
                             " it the justification would support its conclusion where"
                             " the exporting KB's did not.  Re-export from a KB whose"
                             " justifications carry no :out, or drop the key from the"
                             " frame")
                        {:type :naf-justification :out (vec (:out frame))
                         :consequence (:consequence frame) :justification (:id frame)}))))
    (finally (frames/close-frames! frames))))

(defn- import-justifications!
  "Stream the `Justification` frames against the old→new id map.  Every handle a
  justification names is remapped — its consequence, its antecedents, and its informant
  when that is a rule handle rather than a label — and one it cannot resolve drops the
  justification rather than rebuilding it against whatever record now sits at that
  number.  A frame listing its rule among the antecedents as well stores the rule once,
  as the informant (`jtms/->just`).

  A frame with a non-empty `:out` is refused, and by
  `assert-no-naf-justifications!` before this phase runs rather than here: the
  refusal has to land before the first record is written, and by the time this loop
  reads a frame the sentexes are stored.

  With `preserve?` the justification keeps its own dump handle as well.  Sentexes and
  justifications are numbered from one counter, so preserving one kind and minting the
  other would leave the minted ones colliding with the handles the other kind is holding
  — and a justification handle is what `core/justification` and the web's justification
  pages are addressed by.

  Antecedents land as a **vector**, which is the form the engine's own write path
  stores and `jtms/graph-just` normalizes to.  They are read as a set — order and
  duplicates are immaterial to `has-justification?` — but storing one would leave an
  imported record spelled differently from an asserted one, and a dump written from an
  imported KB differing byte for byte from the dump it came from.

  Returns `{:stored n :dropped n :dropped-orphaned n :ids {old-handle new-handle}}`; the
  id map is what lets a *justification's* provenance be replayed, since `old->new` covers
  the sentexes only.  `orphaned` is the dump ids `forget-deleted` took out of that map,
  and it splits the drops in two: a dump that names a sentex it does not carry is a fact
  about the dump, and a justification *this import* cost is a fact about the load — the
  same nil at the same call site, and the summary reports them apart.

  The split is on **every** reference that failed, not on any: a frame counts as the
  load's only when each of its unresolved ids is one this load orphaned, which is exactly
  the frame that would have resolved whole had those records stayed.  Counting a frame
  that merely *names* an orphan hands the load every frame the dump had already lost for a
  reason of its own, which on a dump that hangs deductions off sentexes it never carried
  is several times the number the load is answerable for.

  `:frames` is what the **stream yielded**, which is a different number from `:stored`
  and from `:dropped` and is the only one a torn-file check can read: a truncated chunk
  is indistinguishable from a clean EOF, so what `meta.edn` states is the sole witness
  (`check-frame-count!`), and a frame this load dropped for an unresolvable reference is
  not a torn file.

  `jprint` is folded with each justification stored (`fingerprint/justification-hash`),
  the half of a dump reasoning image's records stamp the sentex pass does not take."
  [kb frames old->new orphaned preserve? tick! jprint]
  (let [records (:records kb)
        remap   (fn [id] (if (integer? id) (get old->new id) id))
        ;; the ids that failed to resolve, which the drop below reads to see whose fault
        ;; the drop is; a non-integer informant is a label and always resolves
        lost    (fn [informant antecedents consequence]
                  (into [] (comp (filter integer?) (filter #(nil? (get old->new %))))
                        (cons consequence (cons informant antecedents))))
        stored   (volatile! 0)
        dropped  (volatile! 0)
        orphans  (volatile! 0)
        frames-n (volatile! 0)          ; what the stream yielded, for the torn check
        ids      (volatile! {})]
    ;; the frame stream closed beside the sink (`frames/closer`): `tick!` throws when a
    ;; caller cancels, and a frame seq only closes its file when it is consumed to the end
    ;; or raises the failure itself
    (with-open [^java.io.Closeable sink   (cap/justification-sink records {})
                ^java.io.Closeable _stream (frames/closer frames)]
      (doseq [frame frames]
        (tick!)
        (vswap! frames-n inc)
        (let [{:keys [informant antecedents consequence bindings strength]} frame
              conseq (get old->new consequence)
              antes  (mapv remap antecedents)
              inf    (remap informant)]
          (if (or (nil? conseq) (nil? inf) (some nil? antes))
            (do (vswap! dropped inc)
                (let [gone (lost informant antecedents consequence)]
                  (when (and (seq gone) (every? #(contains? orphaned %) gone))
                    (vswap! orphans inc))))
            (let [jid  (or (when preserve? (:id frame)) (p/next-id records))
                  just (jtms/->just jid inf antes conseq (or bindings {})
                                    (strength-class strength))]
              (p/write-record! sink just)
              (jprint jid just)
              (when-let [did (:id frame)] (vswap! ids assoc did jid))
              (vswap! stored inc))))))
    {:stored @stored :dropped @dropped :dropped-orphaned @orphans :ids @ids
     :frames @frames-n}))

(defn- mark-premises-by-strength
  "Mark the premises of a dump of ours: a premise **is** a sentex whose `:strength` is
  non-nil — the mark rides on the record in both backends, which is why the format needs
  no premise stream.  Aggregated by handle (dedup can merge several dump ids onto one),
  keeping the strongest.  Returns the count."
  [kb sx-meta]
  (let [records   (:records kb)
        by-handle (reduce (fn [acc [_ {:keys [handle strength]}]]
                            (if strength
                              (update acc handle st/max (strength-class strength))
                              acc))
                          {} sx-meta)]
    ;; through `cap/mark-premises`, which on a store that can mark many at once is a
    ;; statement rather than a write per handle.  The aggregate is why this is a *batch*
    ;; and not something the record write could have carried: which strength a handle
    ;; ends at is not known until the whole stream is read.
    (cap/mark-premises records by-handle)
    (count by-handle)))

(def ^:private provenance-chunk
  "Provenance pairs per bulk write.  The stream is read a chunk at a time rather than
  whole, since a dump of a corpus carries one of these per record."
  1000)

(defn- import-provenance-frames!
  "Replay the `provenance.nippy.stream` — `[handle map]` frames, the handle remapped.
  Optional: a dump whose handles carry none writes no file.  Belief never reads
  provenance, so this is annotation only.  Returns the count stored.

  `handles` is the whole old→new map, sentexes **and** justifications: `add-provenance`
  writes under whatever handle it is given, so a frame can name either kind, and one
  this map cannot resolve is dropped rather than written under a number now holding
  something else."
  [kb dir compression read-fn handles]
  (let [^java.io.File f (io/file dir frames/provenance-file)]
    (if-not (.exists f)
      0
      ;; Written a chunk at a time through `cap/put-all-provenance` — one statement per
      ;; chunk on a store that can write many at once, and the same `put-provenance` per
      ;; pair on one that cannot.  The stream stays streaming: a chunk is what is held,
      ;; never the whole file, which on a corpus dump is a provenance map per record.
      (let [records (:records kb)
            n       (volatile! 0)
            ;; bound before the walk, so the file is closed on the way out whether the
            ;; stream ran to its end or a write threw part-way through it
            fs      (read-fn f compression)]
        (try
          (doseq [chunk (partition-all provenance-chunk fs)]
            (let [entries (into []
                                (comp (filter #(and (sequential? %) (= 2 (count %))))
                                      (keep (fn [[did prov]]
                                              (let [h (get handles did)]
                                                (when (and h (map? prov)) [h prov])))))
                                chunk)]
              (when (seq entries)
                (cap/put-all-provenance records entries)
                (vswap! n + (count entries)))))
          (finally (frames/close-frames! fs)))
        @n))))

;;; ── the index: replay it, or rebuild it ───────────────────────────────

(defn- read-index-meta
  "`index/index.edn`, or nil when the dump has no index beside its records.  Absence is
  ordinary — a `:records` dump has none, and so does a `:records+index` export that was
  cancelled before `index.edn` was written, which is why the writer writes it last."
  [dir]
  (let [^java.io.File f (io/file dir frames/index-dir frames/index-meta-file)]
    (when (.exists f)
      ;; The `.exists` guard already ruled out absence, so this catch fires only on a
      ;; CORRUPT index.edn — a different fact from "there wasn't one", and the caller
      ;; turns both into the same silent full rebuild. Say which happened.
      (try (read-edn-manifest f)
           (catch Exception e
             (trove/log! {:level :warn :id ::index-meta-corrupt :error e
                          :msg "index.edn present but unreadable; rebuilding the index"
                          :data {:file (str f)}})
             nil)))))

(defn- index-decision
  "Whether the dumped index may be replayed, as `[:replay]` or `[:rebuild reason]`.

  Three conditions, and each one is a way the entries could describe something other
  than the records now in the store: a **layout** this build does not key its index in
  (which would read as *empty* rather than as wrong), **records** that are not the ones
  the entries were derived from, and **handles** that moved on the way in (a posting is a
  set of handles, so a remap makes every one of them name a ghost).

  The layout and records checks are `snapshot/index-mismatch` — the *same* validity core a
  standalone snapshot image runs, so a dump's index and an image are one check rather than
  two that could drift.  The handle check is the dump's own, ordered ahead of the records
  one because a remapped import fails both — its stored-under fingerprint no longer matches
  the dump's — and `:handles-remapped` is the diagnosis that names the cause."
  [index-meta fingerprint handles-preserved?]
  (cond
    (nil? index-meta)        [:rebuild :absent]
    (not handles-preserved?) [:rebuild :handles-remapped]
    :else (if-let [r (snapshot/index-mismatch index-meta fingerprint)]
            [:rebuild r] [:replay])))

(defn- replay-index!
  "Install the dumped entries into `kb`'s index, or report why not.  Returns nil on
  success and a rebuild reason on failure.

  Installed in bounded batches and **checked at the end** rather than realized first: an
  index dump is several entries per record, so holding one to inspect it would cost more
  heap than the records did.  A half-installed index is not left behind either way — the
  caller's fallback is `reindex`, which clears before it rebuilds — so the check is
  allowed to come after the writes, and what it has to catch is a stream that ends early
  or does not read at all.  It cannot be a checksum of the entries themselves: they are
  the thing being validated, and `index.edn` is what vouches for them.

  The install itself is `snapshot/install-entries!` — the same one the mapped image's
  `load-index!` runs, because a dump's index stream and a snapshot's index section are
  the same install and two copies of it could refuse a different frame or count a
  different number.  The file behind the stream is closed on the way out **however this
  leaves**: a refused frame throws out of the middle of the walk, and the seq only
  auto-closes on a failure it raises itself or on being consumed to the end."
  [kb dir compression read-fn expected]
  (let [frames (volatile! nil)]
    (try
      (let [n (snapshot/install-entries!
               (:index kb)
               (vreset! frames (read-fn (io/file dir frames/index-dir frames/index-entry-file)
                                        compression)))]
        (when-not (= (long n) (long expected))
          (trove/log! {:level :warn :id ::index-short
                       :msg (str "index entry stream holds " n " entries, index.edn says "
                                 expected)})
          :entries-truncated))
      (catch Exception e
        (trove/log! {:level :warn :id ::index-unreadable
                     :msg (str "index entry stream unreadable: " (ex-message e))})
        :entries-truncated)
      (finally (frames/close-frames! @frames)))))

(defn- install-index!
  "Put the index in place: replay the dump's entries when they can be proved to describe
  the records just stored, else rebuild from those records.  Returns
  `{:index :replayed :entries n}` or `{:index :rebuilt :reason r}`.

  A rebuild is logged at `:info` with its reason.  Discarding the cache is always safe,
  which is what makes the fallback unremarkable — but a cache that silently stops being
  used is a cache nobody maintains, so the log line is what makes a regression visible.
  It is also what makes a failed *replay* safe to fall through: `reindex` clears the
  index before rebuilding, so whatever a broken stream managed to install is wiped."
  [kb dir compression read-fn index-meta fingerprint preserved? on-progress]
  (let [[verdict reason] (index-decision index-meta fingerprint preserved?)
        rebuild (fn [r]
                  (trove/log! {:level :info :id ::index-rebuilt
                               :msg  (str "index rebuilt rather than replayed: " (name r))
                               :data {:reason r}})
                  (on-progress {:phase :reindex :done 0 :total nil})
                  (reindex/reindex kb)                    ; clears the index itself
                  {:index :rebuilt :reason r})]
    (if (= :replay verdict)
      (do
        (on-progress {:phase :index-entries :done 0 :total (:entry-count index-meta)})
        (if-let [r (replay-index! kb dir compression read-fn (:entry-count index-meta))]
          (rebuild r)
          (do (trove/log! {:level :info :id ::index-replayed
                           :msg  (str "index replayed: " (:entry-count index-meta) " entries")})
              {:index :replayed :entries (:entry-count index-meta)})))
      (rebuild reason))))

;;; ── records-only (no belief) ──────────────────────────────────────────

(defn- bulk-load-records-only!
  "The `{:belief? false}` inline pass: for each sentex frame, re-canonicalize, store it,
  and index it **in the same pass** — indexing the record already in hand rather than
  storing everything and then re-reading it back through `reindex`, which on the `:disk`
  record store re-pages every record from disk.

  The records go through a `capabilities/sentex-sink`, which is that same `put-sentex` on
  every store the engine ships and a bulk write on one that has one (`COPY`, over
  Postgres).  It can be a *sink* rather than a batched put precisely because of the
  sentence above: the handle is decided here and the sink is told it, so the index build
  never waits for a batch to land.  Wrapped in `with-bulk-writes` so a `:memory`
  index build is one `persistent!` instead of a `swap!` per fact (a no-op on `:disk-log`,
  which runs its own batched WAL path).

  No dedup map / `sx-meta`: each frame is stored once, so frames map 1:1 to handles and
  each is indexed exactly once — identical to `reindex` folding over the live handles
  (the oracle in the engine-dump reader's own tests).  A dump is already deduped by its
  source and this build's ground-fact canonical form matches the stored one (the import-time
  taxonomy is empty, so symmetric arguments stay as stored and comparisons fold
  identically), so a per-frame dedup map would cost gigabytes to catch essentially
  nothing.

  Which is what lets this path preserve handles with no id map at all: with `preserve?`
  each record is stored at its dump `:id` directly, so a handle a sentence *embeds*
  (`(exceptWhen … (sentexHandle H))`) still names the record it named in the source.  A
  frame with no `:id` is minted a handle, and the count of those is what the caller
  reports — a corpus whose frames are unnumbered has no handles to preserve.

  `index?` is what decides whether the inline index build happens at all.  It is the
  fast path and the default, but a dump carrying a *replayable* index has a cheaper one
  still — installing entries beats deriving them — so the caller turns it off when a
  replay looks possible and installs afterwards.  Reports progress every `report-every`
  frames.  Returns `{:sentexes n :frames n :rules n :minted n :refused {…}
  :fingerprint {…} :naming {…}}`, where `:sentexes` is what got stored and `:frames` is
  what the stream yielded — the two differ by the refusals.

  It also **counts** what it does not check.  This path stores names `assert` refuses —
  that is what a bulk path is for — but a store the public entry point disagrees with is a fact
  about that store, and here, with each record already decoded and in hand, is the one
  cheap moment to learn it.  `nm/tally` is counts and classes only; the spellings behind
  them are a separate question (`vaelii.bench.survey naming`).  A sentence this build
  will not *construct* is the same policy one entry point over: counted in `:refused`, skipped,
  and reported."
  [kb frames decode preserve? index? report-every on-progress total]
  (let [records (:records kb)
        index   (:index kb)
        n       (volatile! 0)            ; what got stored
        seen-n  (volatile! 0)            ; what the stream yielded, for the torn check
        rules   (volatile! 0)
        minted  (volatile! 0)
        naming  (volatile! nm/empty-tally)
        refused (volatile! empty-refusals)
        fprint  (fp/accumulator)
        ;; a handle is an identity, so a dump naming one twice with different content
        ;; is a broken dump, and storing the second frame would destroy the first
        ;; record silently — the same refusal `import-sentexes!` makes, kept a BitSet
        ;; (a bit per handle) so the streaming path stays streaming
        ids     (java.util.BitSet.)]
    ;; the frame stream closed beside the sink (`frames/closer`): a duplicate handle
    ;; throws out of the middle of the walk, and a frame seq only closes its file when it
    ;; is consumed to the end or raises the failure itself
    (with-open [^java.io.Closeable sink   (cap/sentex-sink records {:premises? true})
                ^java.io.Closeable _stream (frames/closer frames)]
      (mem/with-bulk-writes (:backend index)
        (doseq [frame frames]
          (vswap! seen-n inc)
          (let [fm  (decode frame)
                _   (vswap! naming nm/tally (:sentence fm) (:context fm))
                ;; born carrying its strength, ours only, exactly as the belief path
                ;; stores it: the premise mark rides on the record, and `recover` is
                ;; what turns this corpus into a believing KB later — a record stored
                ;; strength-less here would recover with **nothing** believed, every
                ;; handle a derivation with no justification to ground it
                ;;
                ;; Counted and skipped when this build's structural checks refuse the
                ;; sentence, exactly as on the belief path — the same entry point, and a bulk
                ;; path is the last place an all-or-nothing refusal pays for itself.
                rec (try
                      (cond-> (res/kb-sentex kb (:sentence fm) (:context fm))
                        (and preserve? (:strength fm))
                        (assoc :strength (strength-class (:strength fm))))
                      (catch clojure.lang.ExceptionInfo e
                        (if-let [ty (dump-disagreement e)]
                          (do (vswap! refused tally-refusal ty) nil)
                          (throw e))))]
            (when rec
              ;; through a `sentex-sink`, which on every store the engine ships is
              ;; `put-sentex` and the premise mark — the loop this was — and on a store
              ;; that bulk-loads is its bulk path.  The handle is decided *here* either
              ;; way, which is what lets the index build below stay inline: a sink is
              ;; told the handle rather than asked for it.  `:premises? true`, since the
              ;; stores keep the premise set as its own roster and `recover` walks it —
              ;; the record already holds the strength, so the mark is the set-add and
              ;; never a second record write.
              (let [h (if (and preserve? (:id fm))
                        (let [did (long (:id fm))]
                          (when (and (<= 0 did) (< did Integer/MAX_VALUE))
                            (when (.get ids (int did))
                              (throw (ex-info (str "dump names handle " did " twice — a"
                                                   " handle-preserving import gives each"
                                                   " record the id the dump names, so two"
                                                   " records cannot claim one")
                                              {:type :duplicate-handle :handle did})))
                            (.set ids (int did)))
                          (p/write-record! sink (assoc rec :id did)))
                        (do (when preserve? (vswap! minted inc))
                            (p/write-record! sink rec)))
                    c (vswap! n inc)]
                (fprint h rec)
                (if index?
                  (when (reindex/index-one! index rec h) (vswap! rules inc))
                  (when (rules/rule? rec) (vswap! rules inc)))
                (when (zero? (mod (long c) (long report-every)))
                  (on-progress {:phase :sentexes :done c :total total})
                  (trove/log! {:level :info :id ::store-progress
                               :msg (str "  loaded " c " sentexes…")}))))))))
    {:sentexes @n :frames @seen-n :rules @rules :minted @minted
     :refused (assoc @refused :checked @seen-n)
     :fingerprint (fprint) :naming @naming}))

(defn- import-records-only!
  "The `{:belief? false}` path: store + index every sentex in one streaming pass, no
  justifications and no TMS — no JTMS node is created.  The corpus is stored and indexed
  (browsable by term / functor / argument / context, `find-sentexes`, counts, `lookup`
  levels 0-1) but not belief-filtered-queryable (`query` / `ask` read the empty TMS).
  This is what lets a corpus far past what `recover`'s per-node relabel scales to still
  be loaded.

  **The premise marks are kept for a dump of ours, and only for one of ours** — the whole
  of the difference, and the reason `:belief? :stored` exists.  Each record of ours is
  born with its dump strength and rostered in `premise-ids`, which adds no work per frame
  and is what a later `recover` rebuilds belief from.  A **foreign** frame's `:strength`
  is not the premise mark — that dialect's own account of what rests on what decides, and
  only its `replay-belief!` reads it — so `preserve?` gates the strength as well as the
  handle, and a foreign records-only import rosters no premise at all.  A later `recover`
  over that store therefore believes **nothing**, and no re-import of the same dump on
  this path will change that.  A foreign corpus that may want belief later wants
  `:stored`, which reads the deduction stream and lands the marks.

  Two of the three replay conditions are known **before** a record is stored — the layout
  the entries are keyed in, and whether this dialect's handles will be preserved — so
  this path decides upfront whether a replay is even possible.  If it is, the inline
  index build is skipped and the entries are installed afterwards; if the fingerprint
  then disagrees (a dump whose index does not match its own records) it falls back to a
  full rebuild, which is the one case that pays for the record walk twice."
  [kb dir meta compression read-fn decode preserve? report-every on-progress]
  (let [index-meta (read-index-meta dir)
        possible?  (and index-meta
                        (= kv/index-layout-version (:index-layout index-meta))
                        preserve?)
        result     (bulk-load-records-only!
                    kb (read-fn (io/file dir frames/sentex-file) compression) decode preserve?
                    (not possible?) report-every on-progress (:sentex-count meta))
        preserved? (and preserve? (zero? (long (:minted result))))
        idx        (if possible?
                     (install-index! kb dir compression read-fn index-meta
                                     (:fingerprint result) preserved? on-progress)
                     {:index :inline})]
    (trove/log! {:level :info :id ::records-loaded
                 :msg (str "loaded " (:sentexes result) " sentexes (no belief), index "
                           (name (:index idx)))})
    ;; the other entry point, reported rather than enforced: a corpus the public entry point disagrees
    ;; with is loadable and worth loading, and the operator who chose this path is the
    ;; one who should hear the number — now, not from a failed experiment later
    (when-let [line (nm/tally-line (:naming result))]
      (trove/log! {:level :warn :id ::naming-disagreement
                   :msg  (str "this corpus and `assert` disagree: " line)
                   :data (:naming result)}))
    (when-let [line (refusal-line (:refused result))]
      (trove/log! {:level :warn :id ::frames-refused
                   :msg  line
                   :data (:refused result)}))
    (merge {:variant           (:variant meta)
            :dialect           (if preserve? :vaelii :engine)
            :handle-policy     (if preserved? :preserved :remapped)
            :belief?           false
            :sentexes          (:sentexes result)
            :frames            (:frames result)
            :rules             (:rules result)
            :justifications        0
            :naming            (:naming result)
            :refused           (:refused result)}
           idx)))

;;; ── the entry point ───────────────────────────────────────────────────

(def ^:private import-opt-keys
  "Every key `import-dump` reads."
  #{:belief? :report-every :on-progress})

(def belief-modes
  "What `:belief?` may be, and what each one loads.

  `true` and `false` are the two ends and `:stored` is the middle, which exists because
  storing what rests on what and *settling* it are separable work and only the second one
  fails to finish at corpus scale.  A dump read `:stored` lands every justification, every
  premise mark and all the provenance, and leaves the network empty for a `recover` that
  is somebody's own job to schedule."
  {true    "records, justifications, premise marks, provenance, index, then recover"
   :stored "the same, minus the recover — belief is stored and not settled"
   false   "records and index only; no justification stream is read"})

(defn- check-import-opts!
  "Refuse an opts key `import-dump` does not read, an unknown `:belief?` value, and a
  non-nil non-map `opts` — before `meta.edn` is even looked at.

  Two quiet failures, and the value check exists for the second.  `:belief?` misspelt
  (`{:beleif? false}`) takes the default, which is `true`, so a corpus chosen for the
  records-only path runs the recovery it was chosen to skip.  And now that the option has
  three values, a misspelt *value* does the same thing more quietly still: anything
  truthy would otherwise mean `true`, so `{:belief? :store}` — one letter off `:stored` —
  would run the recover rather than the load the caller asked for."
  [opts]
  (opts/check! opts import-opt-keys "import-dump"
               (str "An option nothing reads takes the default in silence, which for"
                    " :belief? means running the belief recovery the records-only path"
                    " exists to skip."))
  ;; `:on-progress` is a function (`opts/bound-domains`), so a non-fn one is a bare cast on
  ;; the first frame report — refused here as `:unknown-option`.  `:belief?` is tri-valued,
  ;; not a boolean, and has no row there; its own value check is below
  (opts/check-values! opts "import-dump")
  (when (and (contains? opts :belief?)
             (not (contains? belief-modes (:belief? opts))))
    (throw (ex-info (str "unknown :belief? value " (pr-str (:belief? opts))
                         " — import-dump reads "
                         (str/join ", " (map pr-str (sort-by pr-str (keys belief-modes))))
                         ".  A value nothing recognises would otherwise read as truthy"
                         " and run the recover.")
                    {:type :unknown-option :mismatch :bad-value :option :belief?
                     :value (:belief? opts)
                     :values (vec (sort-by pr-str (keys belief-modes)))}))))

(defn- dump-belief!
  "The belief half of a `{:belief? true}` import: install the dump's reasoning image in place
  of `recover` when the import kept every handle (`kept?`) and the dump carries one, and
  recover otherwise.  The image's records stamp is checked against `sentex-fp` and
  `jprint`, the fingerprints this import took of the sentexes and the justifications it
  landed.  Returns `recovery/recover-with-image`'s map, or `{:reasoning :recovered :reason
  r}` with `r` `:absent` (no image in the dump) or `:handles-remapped`."
  [kb dir kept? sentex-fp jprint]
  (let [bdir (io/file dir ri/dir-name)]
    (cond
      (not kept?)
      (do (recovery/recover kb) {:reasoning :recovered :reason :handles-remapped})

      (not (.exists (io/file bdir "manifest.edn")))
      (do (recovery/recover kb) {:reasoning :recovered :reason :absent})

      :else
      (recovery/recover-with-image kb bdir {:sentexes sentex-fp :justifications (jprint)}))))

(defn import-dump
  "Import a vaelii export dump from `dir` into the (empty) `kb` — one
  `vaelii.impl.io.export` wrote, or one in a foreign dialect this build still carries a
  reader for (`vaelii.impl.foreign`).

  With `{:belief? true}` (the default) it lands in the state the engine's own restart path
  produces: the record store populated from the re-canonicalized records + the
  justifications + premise marks, the index rebuilt (`reindex`), belief recovered
  (`recover`).  A dump carrying a reasoning image (`export!`'s `:belief?`) is installed in
  place of the recover when the import kept every handle and the records it landed, the
  source identity and the belief policies all equal the image's stamp; the summary's
  `:reasoning-image` says which happened (`{:reasoning :installed}` or `{:reasoning
  :recovered :reason r}`).

  With `{:belief? false}` it stores + indexes every sentex but skips what rests on what,
  the premise marks, and `recover` — the whole corpus is browsable / findable / countable
  but not belief-queryable.  This is the path for a corpus past what `recover`'s per-node
  relabel and the in-RAM JTMS scale to (`recover` resettles a region per premise and per
  justification — millions of them would not finish).

  With `{:belief? :stored}` it does everything `true` does **except the `recover`**: every
  justification, premise mark and provenance entry is stored and the index is installed,
  and the network is left empty for a `recover` somebody schedules later.  Two things make
  this its own mode rather than a variant of either end.

  Storing what rests on what and *settling* it are separable work, and only the second
  fails to finish at corpus scale — so a corpus that cannot afford `recover` today should
  not have to discard its justifications forever to say so.  And for a **foreign** dialect
  the records-only path is not a deferral at all: `preserve?` is `(ours? meta)`, so no
  strength is carried onto a record and no premise is rostered, and a later `recover` over
  that store rebuilds belief from nothing.  `:stored` is the only way a foreign corpus can
  be loaded now and believed later.

  What the KB answers in between is exactly what `{:belief? false}` answers — stored-side
  reads work, every believed one is empty — and the browser says so
  ([docs/web.md](../../../../docs/web.md), *Reading a KB that is not finished*).  The
  difference is not in what it answers, it is in what it can become.

  Reads `meta.edn` first and dispatches on it: the version is gated against its own
  dialect's numbering, the destination must be empty, and only the `:records` /
  `:records+index` variants are read.  `:pg-memory` and an unknown variant throw.

  `opts`: `{:belief? true|:stored|false :report-every n :on-progress f}`.  An unknown
  `:belief?` **value** is refused by name, since anything truthy would otherwise mean
  `true` and run the recover.  `:on-progress` is called
  every `report-every` frames with `{:phase :done :total}` — the phases a dump has, in
  order: `:sentexes`, then (on the belief path) `:justifications` for one of ours or
  whatever phase a foreign reader reports, then either `:index-entries` (a replay) or
  `:reindex` (a rebuild).  A callback that **throws** aborts the import where it stands,
  which is how a caller cancels one; the KB is left holding what had already landed,
  since an import is not a transaction.

  **Every refusal of the dump itself lands before the first write**, for that reason —
  the version gate, the empty destination, the variant, and a non-empty `:out` on a
  justification frame (`assert-no-naf-justifications!`), which is read out of the file
  rather than met in the middle of the justification phase.  So a refused dump leaves the
  store exactly as it found it and the retry needs no `clear!`.  What that does not cover
  is a failure the dump cannot be asked about in advance — a cancelled callback, a torn
  stream, a full disk — and there the sentence above still holds.

  The summary reports the `:dialect` read and the `:handle-policy` used —
  `:preserved` (every record is at the handle the dump gave it) or `:remapped` (with
  `:collapsed`, how many frames canonicalized onto a handle already stored) — and what
  became of the index: `{:index :replayed :entries n}` or `{:index :rebuilt :reason r}`
  (`:absent` / `:layout-changed` / `:handles-remapped` / `:records-differ` /
  `:entries-truncated`).  A caller cannot see any of it for itself, and the first two are
  required for the third: an index entry is a posting of handles, so it can only be
  replayed over a `:preserved` import.

  `:naming` is the count of what this import stored that `assert` would have refused —
  `{:checked n :refused n :by-class {…}}`, logged as a warning when it is not zero.
  Neither import path runs the naming check (both build records directly, which is what
  makes a corpus this size loadable at all), so the disagreement between the two entry points is
  closed by *reporting* it: the operator who chose the bulk path learns the number while
  the records go past, rather than from a re-assertion that throws a year later.

  `:refused` is the same account for the entry point one over — `{:checked n :skipped n
  :by-type {…}}`, also logged as a warning.  These are frames whose sentence this build
  will not **construct**: the structural checks live inside the sentex constructor, so
  there is no record to store when one fires, and the frame is skipped rather than taken
  as a reason to abandon the load.  A rule an older build stored, or another engine's,
  can be one a since-widened check refuses; `:sentexes` and `:frames` differ by exactly
  these plus `:collapsed`.

  **A dropped meta-sentex is reported the same way, and so is what it takes with it.**  A
  remapped import drops a meta-sentex whose embedded `(sentexHandle H)` names a rule this
  dump does not carry (`:dropped-meta-sentexes`), which leaves `:orphaned-ids` dump ids
  with no record to resolve to; every reference to one is dropped, and
  `:dropped-justifications-orphaned` is how many justifications that cost — the ones whose
  *every* unresolved reference is such an id, so they would have resolved whole had the
  records stayed.  A subset of `:dropped-justifications`, which also counts the references
  a dump makes to sentexes it never carried.  Reported apart because they are different
  facts: the second is what the dump is like, the first is what this load did to it.

  **Skipping is not repair.** A skipped rule is gone from the store, and every
  justification, provenance entry and meta-sentex naming it fails to resolve and is
  dropped in turn.  What the number buys is that the operator learns which records those
  were from a summary, on a load that finished, instead of from a stack trace eight hours
  into one that did not."
  ([kb dir] (import-dump kb dir {}))
  ([kb dir {:keys [belief? report-every on-progress]
            :or   {belief? true report-every 500000 on-progress no-progress}
            :as   opts}]
   (check-import-opts! opts)
   (let [meta    (read-meta dir)
         variant (:variant meta :records)]
     (assert-supported-version! meta)
     (assert-empty-destination! kb)
     (when-not (#{:records :records+index} variant)
       (throw (ex-info (str "unsupported dump variant " variant
                            " — this importer reads :records / :records+index")
                       {:type :unsupported-variant :variant variant})))
     (let [compression (or (:compression meta) :none)
           read-fn     (stream-reader-for meta)
           decode      (frame-decoder)]
       ;; Declared before the first write, because nothing downstream can work it out by
       ;; reading: a load that skips the recover (`false`, `:stored`) leaves a store
       ;; byte-for-byte identical to one a KB of `assert-inert` sentexes wrote, and the
       ;; KB doing the loading has already had its belief noted clean by `open-kb` over
       ;; the empty destination this load is about to fill.  Said here rather than at
       ;; the end so it holds for the whole load, including one that throws part-way.
       (when-not (true? belief?)
         (kb/note-hazards! kb {:no-belief true}))
       ;; A bulk load accumulates index deltas monotonically, tripping the disk
       ;; durability daemon's dead-ratio compaction trigger repeatedly; each firing
       ;; rewrites the whole (growing) index under the backend lock, stalling the writer.
       ;; Pause auto-compaction for the load and let the daemon compact once afterwards
       ;; (a no-op on `:memory`, which registers no daemon).
       (dur/call-with-compaction-paused
        (fn []
          ;; `false` is the only value that skips the belief phases; `:stored` runs them
          ;; and stops before the recover, which is decided at the one call site below.
          (if (false? belief?)
            (let [summary (import-records-only! kb dir meta compression read-fn decode
                                                (ours? meta) report-every on-progress)]
              (check-frame-count! :sentexes (:frames summary) (:sentex-count meta))
              (trove/log! {:level :info :id ::import-complete
                           :msg  (str "import-dump (records-only) complete: "
                                      (:sentexes summary) " sentexes indexed, no belief")
                           :data summary})
              summary)
            (let [ours?    (ours? meta)
                  tick     (fn [phase total] (ticker on-progress phase total report-every))
                  jprint   (fp/accumulator fp/justification-hash)
                  ;; the last gate that can be decided from the dump alone, and so the
                  ;; last one that can be decided before the first write: a `:out` frame
                  ;; refused from inside the justification loop refused a KB that was
                  ;; already holding every sentex the dump had (`assert-no-naf-justifications!`)
                  _ (when ours?
                      (assert-no-naf-justifications!
                       (read-fn (io/file dir frames/justification-file) compression)))
                  {:keys [sx-meta embedding collapsed minted fingerprint naming frames
                          refused]}
                  (import-sentexes! kb (read-fn (io/file dir frames/sentex-file) compression)
                                    decode ours? (tick :sentexes (:sentex-count meta)))
                  _ (check-frame-count! :sentexes frames (:sentex-count meta))
                  _ (when-let [line (nm/tally-line naming)]
                      (trove/log! {:level :warn :id ::naming-disagreement
                                   :msg  (str "this corpus and `assert` disagree: " line)
                                   :data naming}))
                  _ (when-let [line (refusal-line refused)]
                      (trove/log! {:level :warn :id ::frames-refused
                                   :msg  line
                                   :data refused}))
                  old->new (into {} (map (fn [[did m]] [did (:handle m)])) sx-meta)
                  ;; every record landed where the dump said, so the id map is the
                  ;; identity and there is nothing to remap or to rewrite
                  kept?    (and ours? (zero? (long collapsed)) (zero? (long minted)))
                  ;; before anything reads a handle out of stored content
                  rewrite  (if kept?
                             {:rewritten 0 :dropped 0 :deleted #{}}
                             (rewrite-embedded-handles! kb embedding old->new))
                  ;; ...and before anything reads the id map again, since the pass above
                  ;; deleted records the map still names.  The two shadow the maps they
                  ;; are derived from, so no reader below can reach a dump id whose record
                  ;; this import has removed.
                  {:keys [sx-meta old->new orphaned]}
                  (forget-deleted sx-meta old->new (:deleted rewrite))
                  {:keys [premises provenance dropped dropped-orphaned]}
                  (if ours?
                    ;; ours says it directly: justifications are justifications, and a
                    ;; premise is a sentex carrying a strength
                    (let [{:keys [dropped dropped-orphaned ids frames]}
                          (import-justifications!
                           kb (read-fn (io/file dir frames/justification-file) compression) old->new
                           orphaned kept?
                           (tick :justifications (:justification-count meta))
                           jprint)
                          ;; the same witness the sentex stream gets, and the stream that
                          ;; most needs it: a torn justification file is indistinguishable from a clean EOF,
                          ;; and what it loses is belief — a KB that recovers to fewer
                          ;; conclusions than it was exported with, silently
                          _ (check-frame-count! :justifications frames
                                                (:justification-count meta))]
                      {:premises   (mark-premises-by-strength kb sx-meta)
                       ;; both kinds' handles, since a provenance frame can name either
                       ;; and the two draw from one counter, so nothing collides
                       :provenance (import-provenance-frames!
                                    kb dir compression read-fn (merge old->new ids))
                       :dropped    dropped
                       :dropped-orphaned dropped-orphaned})
                    ;; a foreign dialect's account, read by its own reader
                    ((dump-reader-field :replay-belief!)
                     kb {:dir dir :compression compression :read-fn read-fn :meta meta
                         :sx-meta sx-meta :old->new old->new :orphaned orphaned
                         :ticker tick :strength-class strength-class}))
                  _ (when-let [line (orphan-line {:dropped (:dropped rewrite)
                                                  :orphaned (count orphaned)
                                                  :justifications (or dropped-orphaned 0)})]
                      (trove/log! {:level :warn :id ::meta-sentexes-dropped
                                   :msg  line
                                   :data {:dropped-meta-sentexes (:dropped rewrite)
                                          :orphaned-ids (count orphaned)
                                          :dropped-justifications-orphaned
                                          (or dropped-orphaned 0)}}))]
              ;; put the index in place — the dump's own entries when they can be proved
              ;; to describe these records, else rebuilt from them — and then recover the
              ;; JTMS + taxonomy and settle belief.  Recovery reads the *records*, so
              ;; whichever way the index arrived it is the same restart a durable KB makes.
              ;;
              ;; `:stored` stops here, and the boundary is this one call.  Everything above it
              ;; is a write to the store; `recover` is the only step that builds in-memory
              ;; state, so skipping it leaves a store a later `recover` reads exactly as it
              ;; reads one a restart finds — which is what makes the settling schedulable
              ;; rather than a condition of the load.
              (let [idx (install-index! kb dir compression read-fn (read-index-meta dir)
                                        fingerprint kept? on-progress)
                    img (when (true? belief?)
                          (dump-belief! kb dir (and ours? kept?) fingerprint jprint))]
                (let [summary (merge
                               {:variant            variant
                                :dialect            (if ours? :vaelii :engine)
                                :handle-policy      (if kept? :preserved :remapped)
                                :collapsed          collapsed
                                :belief?            belief?
                                :reasoning-image    img
                                :sentexes           (cap/count-sentexes (:records kb))
                                :frames             frames
                                :justifications     (cap/count-justifications (:records kb))
                                :premises           premises
                                :provenance-entries provenance
                                :dropped-justifications dropped
                                :dropped-justifications-orphaned (or dropped-orphaned 0)
                                :rewritten-handles  (:rewritten rewrite)
                                :dropped-meta-sentexes (:dropped rewrite)
                                :orphaned-ids       (count orphaned)
                                :naming             naming
                                :refused            refused}
                               idx)]
                  (trove/log! {:level :info :id ::import-complete
                               :msg   (str "import-dump complete: " (:sentexes summary)
                                           " sentexes, " (:justifications summary)
                                           " justifications, index " (name (:index summary))
                                           (when-not (true? belief?)
                                             " — belief stored and NOT settled; run recover"))
                               :data  summary})
                  summary))))))))))
