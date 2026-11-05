;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.import
  "Import a vaelii export dump, a directory of record streams, into a KB, landing in the state
  the engine's own restart path (`reindex` / `recover`) produces. `meta.edn` is the marker
  and schema, and every other file is a nippy stream. Every sentence is re-canonicalized
  through `res/kb-sentex`; handles are preserved for a dump of ours; the dumped index is
  replayed only when it is proved to fit, and the summary says which happened and why. A frame
  that is not of our dialect goes to a foreign reader (`vaelii.impl.foreign`). Out of scope:
  the `:pg-memory` variant. See docs/storage.md, \"Importing a dump\"."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [taoensso.trove :as trove]
            [vaelii.impl.assert-entry :as entry]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.snapshot :as snapshot]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as ri]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
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

(defn read-edn-manifest
  "The EDN manifest in `f`, read under the manifest byte bound — `dfiles/read-edn-manifest`,
  which sits in `vaelii.impl.disk.files` so that the store sentinels `open-kb` reads go
  through the same reader."
  [f]
  (dfiles/read-edn-manifest f))

;; The stream names live in `vaelii.impl.io.frames`, shared with the export writer —
;; the two halves of the round trip must agree on the layout, so it is stated once.

;;; ── stream readers ────────────────────────────────────────────────────
;;; The chunked and single-stream nippy framing itself lives in `vaelii.impl.io.frames`, shared
;;; with the export writer and the snapshot sink; what stays here is the dump-specific
;;; policy of choosing a reader from a dump's own `meta.edn` (`stream-reader-for`).

(defn- check-frame-count!
  "Refuse a stream that ended early (`:truncated-dump`). A torn chunk is indistinguishable from
  a clean EOF, so the count `meta.edn` states is the only witness. `n` is what the stream
  yielded, not what got stored. Nil `stated` checks nothing."
  [what n stated]
  (when (and stated (< (long n) (long stated)))
    (throw (ex-info (str "the dump states " stated " " (name what) " and the stream"
                         " ended after " n " — a torn or truncated dump")
                    {:type :truncated-dump :kind what :read n :stated stated}))))

;;; ── frames this build will not construct ──────────────────────────────────
;;; A frame the constructor refuses is skipped and counted in `:refused`, and the load
;;; carries on (docs/naming.md, "Whose invariants: the two policies").

;;; ── what `assert` refuses and a frame carries ─────────────────────────
;;; A name `assert` refuses is stored and counted in `:naming`; a record that would answer
;;; wrongly is skipped and counted in `:refused`; an `(ist Ctx S)` is stored as S in Ctx
;;; (docs/naming.md, "Whose invariants: the two policies").

(defn- as-asserted
  "The decoded frame `fm` with an `(ist Ctx S)` sentence replaced by S and its context by
  Ctx, through any depth of nesting — the sentex `assert` stores for it.  A malformed
  `ist` is left in place for `storable-sentexes` to refuse."
  [fm]
  (if-let [[ctx s] (entry/ist-parts (:sentence fm))]
    (recur (assoc fm :sentence s :context ctx))
    fm))

(defn- storable-sentexes
  "The sentexes `sentence` builds in `context`, or the typed refusal `assert` raises for a
  record that would answer wrongly (the note above).  Every throw carries a `:type`, so
  the frame loops count it in `:refused` and skip the frame.

  One sentex, except for a rule `assert` stores as several (`rules/expand-rule`: an `or`
  antecedent, an `and` consequent), which is one sentex per form in `assert`'s order.
  Every form is checked before any is returned, so a refusal skips the whole frame, as
  `assert` refuses the whole rule.  A rule with an inline `exceptWhen` is not expanded."
  [kb sentence context]
  (when (and (sequential? sentence) (= sx/ist-functor (first sentence)))
    (let [p (entry/ist-shape-problem sentence)]
      (throw (ex-info (:message p) (dissoc p :message)))))
  (when (or (not (symbol? context)) (nm/query-context? context))
    (throw (ex-info (str (pr-str context) " is not a context a sentex is stored in: a"
                         " stored context is a symbol, and not a query context")
                    {:type :shape :context context})))
  (when-let [p (or (sx/connective-problem sentence) (checks/term-shape-problem sentence))]
    (throw (ex-info (:message p) (dissoc p :message))))
  ;; `entry/assert-one`'s test for a rule; the shape checks run on each stored form
  ;; before the constructor, as `assert` runs them
  (let [rule? (rules/rule-sentence? (rules/inner-rule sentence))
        forms (if (and rule? (nil? (first (rules/split-exceptWhen sentence))))
                (rules/expand-rule sentence)
                [sentence])]
    (let [[exc inner] (rules/split-exceptWhen sentence)]
      (when-let [p (and exc (not (sx/sentex-handle? inner)) (rules/exceptWhen-not-a-rule exc inner))]
        (throw (ex-info (:message p) (dissoc p :message)))))
    (when rule? (run! checks/check-rule-shape forms))
    ;; a nil taxonomy skips the arms that read stored content, which a later frame can hold
    (when-let [ps (and (not rule?) (seq (special/wff-problems nil sentence context)))]
      (throw (ex-info (str "not well-formed: " (str/join "; " ps))
                      {:type :not-well-formed :sentence sentence})))
    (mapv (fn [form]
            (let [rec (res/kb-sentex kb form context)]
              (when-not (sx/exceptWhen-meta? form)
                (checks/check-sentex-ground rec form context))
              rec))
          forms)))

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

(def ^:dynamic *wrap-reader*
  "A fn from the stream reader `stream-reader-for` chooses to the reader the import reads
  every stream file through, or nil for the chosen reader itself.  A reader takes `[file
  compression]` and answers the file's frames.  The test fixtures bind it to answer the
  frames of a dump they restore many times from a vector thawed once per JVM
  (`vaelii.test-util/restore!`)."
  nil)

(defn- stream-reader-for
  "The reader for a dump's stream files. Our own dumps state their framing; a foreign dump's
  is inferred from its version line (v6+ chunked, v4/v5 single-stream). A `:framing` this
  build does not know is refused up front, as an unknown `:compression` is."
  [meta]
  (case (:framing meta)
    :chunked frames/read-chunked-seq
    :window  frames/read-single-stream-seq
    nil      (if (>= (long (:format-version meta 0)) 6)
               frames/read-chunked-seq frames/read-single-stream-seq)
    (throw (ex-info (str "unknown dump :framing " (pr-str (:framing meta))
                         " — this build reads :chunked and :window")
                    {:type :unknown-framing :framing (:framing meta)}))))

(defn- closing-every-stream
  "`(f read-fn')` — `read-fn'` being `read-fn` that records the close function of every
  stream it opens (`frames/stream-closer`) — and every recorded stream closed when `f`
  returns or throws.  This is how the streams a foreign reader's `:replay-belief!` opens
  through the `:read-fn` it is handed are closed: the reader need not close them, and must
  not read one after it returns (docs/foreign.md).  The records hold each stream and not
  its seq, so the frames a walk has passed stay collectable."
  [read-fn f]
  (let [closes (java.util.concurrent.ConcurrentLinkedQueue.)]
    (try
      (f (fn [file compression]
           (let [frames (read-fn file compression)]
             (some->> (frames/stream-closer frames) (.add closes))
             frames)))
      (finally
        (doseq [close closes]
          (try (close)
               (catch Throwable t
                 (trove/log! {:level :warn :id ::stream-not-closed
                              :msg (str "import-dump could not close a stream the foreign"
                                        " reader opened: " (.getMessage t))}))))))))

;;; ── meta + checks ─────────────────────────────────────────────────────

(defn read-meta
  "Read a dump's `meta.edn` (the marker + schema) without loading any records — under
  `dfiles/manifest-bytes`, since a dump directory is whatever an operator copied."
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
  "Check the version against the numbering its own dialect uses — the two overlap, so one
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

(defn check-dump!
  "Refuse a dump `meta` describes that this build does not read: a format version outside
  its dialect's numbering (`:unsupported-version`), and a variant other than `:records` /
  `:records+index` (`:unsupported-variant`).  Returns the variant."
  [meta]
  (assert-supported-version! meta)
  (let [variant (:variant meta :records)]
    (when-not (#{:records :records+index} variant)
      (throw (ex-info (str "unsupported dump variant " variant
                           " — this importer reads :records / :records+index")
                      {:type :unsupported-variant :variant variant})))
    variant))

(defn- assert-empty-destination! [kb]
  (let [n (cap/count-sentexes (:records kb))]
    (when (pos? n)
      (throw (ex-info (str "destination KB is not empty (" n " sentexes); import expects "
                           "a fresh KB to avoid id collisions — clear the store first, or,"
                           " to keep this KB's writes over a newer dump, open it as a fork"
                           " ({:backend :overlay :base … :overlay …}) and import with"
                           " :rebase? true")
                      {:type :not-empty :sentex-count n})))))

;;; ── frame decode ──────────────────────────────────────────────────────

(defn- our-sentence
  "The sentence for a frame our own writer produced, as its author wrote it. A rule's
  `set/*Rule` wrappers (`:engines` / `:defeasible` / `:effect`, or the `:direction` /
  `:assumption` / `:constraint` fields read through `sx/fielded-rule-slots`) go back around
  it (`rules/rewrap-sentex`), and its `:varmap` names go back in (`sentex/originalize`). A
  fact carries neither. A rule frame carrying only `:antecedent` and `:consequent` is rebuilt
  from them (`rule-sentence`)."
  [{:keys [sentence antecedent consequent varmap engines defeasible effect
           direction assumption constraint]}]
  (if (some? antecedent)
    (let [[engines effect] (if (some? effect)
                             [engines effect]
                             (sx/fielded-rule-slots direction assumption constraint))]
      (rules/rewrap-sentex (sx/originalize (or sentence (sx/rule-sentence antecedent consequent))
                                           varmap)
                           {:engines engines :defeasible defeasible :effect effect}))
    sentence))

(defn- frame-decoder
  "A `frame -> {:id :context :sentence :strength …}` decoder for this import. A map carrying
  `:sentence`, or a `RuleSentex`'s fields (an `:antecedent` beside a `:varmap`), is ours;
  anything else goes to the foreign reader, resolved once in a `delay`, and the import
  refuses with `:no-foreign-reader` when it is absent. An `:antecedent` alone does not make
  a frame ours. The discrimination is on the frame, not on `meta.edn`'s `:dialect`."
  []
  (let [foreign-decode (delay (:decode-frame (foreign/reader :engine-dump)))]
    (fn [frame]
      (if (and (map? frame)
               (or (contains? frame :sentence)
                   (and (some? (:antecedent frame)) (contains? frame :varmap))))
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
;; The streaming passes report through a callback, not a log line, and a callback that throws
;; cancels the import: the throw leaves the KB holding what had landed.

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
  "Stream the sentex frames: decode each, re-canonicalize through `res/kb-sentex` and store
  it. Two forms that canonicalize to one dedup to one handle (a local `[sentence context] ->
  handle` map). For a dump of ours the record is stored at its dump handle; a frame with no
  `:id`, or one that collapses onto a stored handle, is counted (`:collapsed` in either
  dialect). A frame `assert` would expand (`storable-sentexes`) maps its dump id to its first
  form's handle, and its further forms are stored after the stream and returned as
  `:expansions` for `mark-expanded-premises`.

  Returns `{:sx-meta {dump-id {:handle h :rule? bool :strength s}} :embedding [handle]
  :collapsed n :minted n :expanded {:frames n :records n} :expansions [...] :frames n
  :refused {…} :fingerprint {…} :naming {…}}`. `:embedding` lists the handles whose stored
  content names another sentex. `:fingerprint` and `:naming` are accumulated on this one
  pass. A frame the constructor will not build, or `assert` refuses, is counted in `:refused`
  and skipped, so it reaches neither the store nor `sx-meta`. `:strength` is the frame's own,
  unnormalized."
  [kb frames decode ours? tick! total]
  (let [records   (:records kb)
        seen      (volatile! {})         ; [sentence context] -> handle
        sx-meta   (volatile! {})
        embed     (volatile! [])         ; in the order stored, a handle once
        collapsed (volatile! 0)
        minted    (volatile! 0)
        frames-n  (volatile! 0)          ; what the stream yielded, for the torn check
        naming    (volatile! nm/empty-tally)
        refused   (volatile! empty-refusals)
        expanded  (volatile! {:frames 0 :records 0})
        extras    (volatile! [])         ; [first-form-handle record] per further form
        fprint    (fp/accumulator)]
    ;; The sink marks each record that carries a strength, which only ours do, at its first
    ;; frame's. A dump id that collapses onto a stored handle keeps the strongest strength, which
    ;; `mark-premises-by-strength` re-marks once the whole stream is read, so a store whose mark
    ;; is a column does not write every premise row twice.
    ;;
    ;; The frame stream is closed beside the sink (`frames/closer`): `tick!` throws on cancel and
    ;; a duplicate handle throws below, and a frame seq only closes its file when consumed.
    (with-open [^java.io.Closeable sink   (cap/sentex-sink records {:premises? (boolean ours?)})
                ^java.io.Closeable _stream (frames/closer frames)
                r                          (progress/start ::store-sentexes
                                                           "import: store the sentexes" total)]
      (let [store!
            ;; `rec` stored at dump id `did` (ours only), collapsed onto the handle its
            ;; canonical form already holds, or minted, and counted in `:minted` when
            ;; `frame?`; returns the handle
            (fn [rec did frame?]
              (let [k [(sx/sentence-of rec) (:context rec)]
                    h (if-let [prior (get @seen k)]
                        (do (vswap! collapsed inc) prior)
                        (let [hh (if (and ours? did)
                                   (do
                                     ;; a handle is an identity, so a second frame claiming one already stored is a broken dump;
                                     ;; equal content never reaches here (`seen` has collapsed it).
                                     (when (contains? @sx-meta did)
                                       (throw (ex-info (str "dump names handle " did " twice, "
                                                            "with different content")
                                                       {:type :duplicate-handle :handle did})))
                                     (p/write-record! sink (assoc rec :id did)))
                                   (do (when (and ours? frame?) (vswap! minted inc))
                                       (p/write-record! sink rec)))]
                          (vswap! seen assoc k hh)
                          (fprint hh rec)                ; only what actually got stored
                          ;; here, not for a collapse: its handle is listed already
                          (when (embeds-handle? (sx/sentence-of rec)) (vswap! embed conj hh))
                          hh))]
                h))]
        (doseq [frame frames]
          (tick!)
          (progress/tick! r)
          (vswap! frames-n inc)
          (let [fm    (as-asserted (decode frame))
                _     (vswap! naming nm/tally (:sentence fm) (:context fm))
                did   (:id fm)
                ;; born carrying its strength, so the premise pass has nothing to re-store. Ours only: a
                ;; foreign frame's `:strength` is not the premise mark.
                ;;
                ;; A sentence this build's structural checks refuse yields no record, so the frame is counted
                ;; and skipped, around the construction only and for a refusal carrying a `:type`.
                recs  (try
                        (cond->> (storable-sentexes kb (:sentence fm) (:context fm)) ; id nil
                          (and ours? (:strength fm))
                          (mapv #(assoc % :strength (strength-class (:strength fm)))))
                        (catch clojure.lang.ExceptionInfo e
                          (if-let [ty (dump-disagreement e)]
                            (do (vswap! refused tally-refusal ty) nil)
                            (throw e))))]
            (when-let [[rec & more] (seq recs)]
              (let [h (store! rec did true)]
                (when more
                  (vswap! expanded #(-> % (update :frames inc) (update :records + (count recs))))
                  (vswap! extras into (map (fn [r] [h r])) more))
                (when did
                  (vswap! sx-meta assoc did {:handle   h
                                             :rule?    (some? (:antecedent rec))
                                             :strength (:strength fm)}))))))
        ;; An expanded frame's other forms are stored after the stream, so the handles they
        ;; are minted never take a dump id a later frame claims.
        (vreset! extras (mapv (fn [[h rec]] [h (store! rec nil false)]) @extras))))
    {:sx-meta @sx-meta :embedding @embed :collapsed @collapsed :minted @minted
     :expanded @expanded :expansions @extras :frames @frames-n
     :refused (assoc @refused :checked @frames-n)
     :fingerprint (fprint) :naming @naming}))

(defn- rewrite-embedded-handles!
  "Rewrite the `(sentexHandle <dump-id>)` terms inside stored content to the handles those
  records landed at, for a remapped import only. A reference the map cannot resolve drops
  the meta-sentex. A rewritten record whose canonical form an earlier record of this pass
  holds is deleted and merged onto it (`follow-merged`). Returns `{:rewritten n :dropped n
  :deleted #{handle} :merged {handle survivor}}`; the caller takes the deleted handles out of
  the id map (`forget-deleted`)."
  [kb handles old->new]
  (let [records   (:records kb)
        rewritten (volatile! 0)
        deleted   (volatile! (transient #{}))
        held      (volatile! (transient {}))    ; [sentence context] -> the handle holding it
        merged    (volatile! (transient {}))]
    ;; in the order the sentex pass stored them, so the survivor of a merge is the record
    ;; stored first, as it is for a collapse there
    (with-open [r (progress/start ::rewrite-embedded-handles
                                  "import: rewrite the embedded handles"
                                  (count handles))]
      (doseq [h handles :let [rec (p/get-sentex records h)] :when rec]
        (progress/tick! r)
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
            (let [built (res/kb-sentex kb sentence (:context rec))
                  k     [(sx/sentence-of built) (:context built)]]
              (if-let [survivor (get @held k)]
                (do (p/delete-sentex! records h)
                    (vswap! merged assoc! h survivor))
                (do (p/put-sentex records (assoc built :id h :strength (:strength rec)))
                    (vswap! held assoc! k h)
                    (vswap! rewritten inc))))
            (do (p/delete-sentex! records h)
                (vswap! deleted conj! h))))))
    (let [gone (persistent! @deleted)]
      {:rewritten @rewritten :dropped (count gone) :deleted gone
       :merged (persistent! @merged)})))

(defn- follow-merged
  "`sx-meta` and `old->new` with every handle `rewrite-embedded-handles!` merged away
  replaced by the handle it merged onto — `{:sx-meta m :old->new m}`.  Unlike a dropped
  meta-sentex, a merged one still exists, at its survivor's handle, so a dump id that
  named it goes on resolving: a justification resting on it rests on the survivor, and
  its premise mark joins the survivor's, the strongest kept (`mark-premises-by-strength`)."
  [sx-meta old->new merged]
  (if (empty? merged)
    {:sx-meta sx-meta :old->new old->new}
    (let [moved (into [] (comp (filter (fn [[_ h]] (contains? merged h))) (map key)) old->new)]
      {:sx-meta  (reduce (fn [m did] (update-in m [did :handle] merged)) sx-meta moved)
       :old->new (reduce (fn [m did] (update m did merged)) old->new moved)})))

(defn- forget-deleted
  "`sx-meta` and `old->new` with every dump id whose record `rewrite-embedded-handles!` deleted
  taken out of both, and the set of ids that removes: `{:sx-meta m :old->new m :orphaned
  #{dump-id}}`. A reference that fails to resolve is dropped and counted by
  `import-justifications!` and a foreign reader's `replay-belief!`, and the premise marks
  read `sx-meta`."
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
;; Our own dump states justifications and premises directly. A foreign dialect's account is
;; read by its own reader (`vaelii.impl.foreign`), which is handed the id map.

(defn- assert-no-naf-justifications!
  "Refuse a dump whose `Justification` frame carries a non-empty `:out`
  (`:naf-justification`), reading the stream for nothing else. NAF is re-evaluated, not
  stored (docs/naf.md), and dropping the frame would take belief with it silently. A
  pre-pass, because a refusal in the middle of a write leaves the sentexes stored and blocks
  the retry. Called by `land-belief-records!` for a dump of ours. The stream is closed here,
  refusal or not."
  [frames total]
  (with-open [_ (frames/closer frames)
              r (progress/start ::check-justifications
                                "import: check the justifications" total)]
    (doseq [frame frames]
      (progress/tick! r)
      (when (seq (:out frame))
        (throw (ex-info (str "the dump names a justification with a non-empty :out "
                             (pr-str (vec (:out frame))) " — a justification here has no"
                             " negation-as-failure antecedent list, so imported without"
                             " it the justification would support its conclusion where"
                             " the exporting KB's did not.  Re-export from a KB whose"
                             " justifications carry no :out, or drop the key from the"
                             " frame")
                        {:type :naf-justification :out (vec (:out frame))
                         :consequence (:consequence frame) :justification (:id frame)}))))))

(defn- import-justifications!
  "Stream the `Justification` frames against the old->new id map. Every handle a
  justification names (consequence, antecedents, and a rule-handle informant) is remapped,
  and one it cannot resolve drops the justification. A frame listing its rule among the
  antecedents stores it once, as the informant (`jtms/->just`). With `preserve?` the
  justification keeps its dump handle. Antecedents land as a vector. A non-empty `:out` is
  refused earlier, by `assert-no-naf-justifications!`.

  Returns `{:stored n :dropped n :dropped-orphaned n :ids {old-handle new-handle}}`. The id
  map lets a justification's provenance replay. `:dropped-orphaned` counts the frames whose
  every unresolved id `forget-deleted` took out. `:frames` is what the stream yielded, the
  number `check-frame-count!` reads. `jprint` is folded with each justification stored
  (`fingerprint/justification-hash`)."
  [kb frames old->new orphaned preserve? tick! jprint total]
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
                ^java.io.Closeable _stream (frames/closer frames)
                r                          (progress/start ::store-justifications
                                                           "import: store the justifications"
                                                           total)]
      (doseq [frame frames]
        (tick!)
        (progress/tick! r)
        (vswap! frames-n inc)
        (let [{:keys [informant antecedents consequence bindings strength subsumptions]} frame
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
                                    (strength-class strength) (some->> subsumptions seq (into #{})))]
              (p/write-record! sink just)
              (jprint jid just)
              (when-let [did (:id frame)] (vswap! ids assoc did jid))
              (vswap! stored inc))))))
    {:stored @stored :dropped @dropped :dropped-orphaned @orphans :ids @ids
     :frames @frames-n}))

(defn- mark-premises-by-strength
  "Mark the premises of a dump of ours: a premise is a sentex whose `:strength` is non-nil.
  Aggregated by handle, keeping the strongest. Returns the count. Only a handle whose
  aggregate differs from what its record was written with is marked here; the sink marked the
  rest (`import-sentexes!`)."
  [kb sx-meta]
  (let [records   (:records kb)
        by-handle (reduce (fn [acc [_ {:keys [handle strength]}]]
                            (if strength
                              (update acc handle st/max (strength-class strength))
                              acc))
                          {} sx-meta)
        written   (fn [h]
                    (let [{:keys [handle strength]} (get sx-meta h)]
                      (when (and strength (= h handle)) (strength-class strength))))
        stale     (into {} (remove (fn [[h s]] (= s (written h)))) by-handle)]
    ;; through `cap/mark-premises`, a statement and not a write per handle. A batch because the
    ;; strength a handle ends at is not known until the whole stream is read; a dump with no
    ;; collapse makes no batch write.
    (when (seq stale) (cap/mark-premises records stale))
    (count by-handle)))

(defn- mark-expanded-premises
  "Mark each further form of an expanded frame (`expansions`, `[[first-handle handle] …]`)
  a premise at the strength its first form's handle holds after the premise pass, keeping
  the stronger where the form collapsed onto a premise already marked.  `assert` stores
  every form of one rule at one strength.  Returns the count marked."
  [kb expansions]
  (let [records   (:records kb)
        by-handle (reduce (fn [acc [h eh]]
                            (if-let [s (p/premise-strength records h)]
                              (let [prior (or (get acc eh) (p/premise-strength records eh))]
                                (assoc acc eh (if prior (st/max s prior) s)))
                              acc))
                          {} expansions)]
    ;; an import that expanded no frame makes no batch write
    (when (seq by-handle) (cap/mark-premises records by-handle))
    (count by-handle)))

(def ^:private provenance-chunk
  "Provenance pairs per bulk write.  The stream is read a chunk at a time rather than
  whole, since a dump of a corpus carries one of these per record."
  1000)

(defn- import-provenance-frames!
  "Replay the `provenance.nippy.stream` `[handle map]` frames, the handle remapped. Optional.
  `handles` is the whole old->new map, sentexes and justifications; a frame it cannot
  resolve is dropped. With `drop-principal?` a frame's `:principal` is dropped. Returns the
  count stored."
  [kb dir compression read-fn handles total drop-principal?]
  (let [^java.io.File f (io/file dir frames/provenance-file)]
    (if-not (.exists f)
      0
      ;; Written a chunk at a time through `cap/put-all-provenance`; a chunk is what is held,
      ;; never the whole file.
      (let [records (:records kb)
            n       (volatile! 0)
            ;; closed on the way out whether the stream ran to its end or a write threw
            ;; part-way through it, by a closer that holds the file and not the frames
            fs      (read-fn f compression)]
        (with-open [_ (frames/closer fs)
                    r (progress/start ::store-provenance
                                      "import: store the provenance" total)]
          (doseq [chunk (partition-all provenance-chunk fs)]
            (progress/tick! r (count chunk))
            (let [entries (into []
                                (comp (filter #(and (sequential? %) (= 2 (count %))))
                                      (keep (fn [[did prov]]
                                              (let [h (get handles did)]
                                                (when (and h (map? prov))
                                                  [h (cond-> prov
                                                       drop-principal? (dissoc :principal))])))))
                                chunk)]
              (when (seq entries)
                (cap/put-all-provenance records entries)
                (vswap! n + (count entries))))))
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
  "Whether the dumped index may be replayed, as `[:replay]` or `[:rebuild reason]`. Layout and
  records are `snapshot/index-mismatch`, the check a mapped image runs; the handle check is
  the dump's own and runs ahead of the records one, so a remapped import is diagnosed
  `:handles-remapped`."
  [index-meta fingerprint handles-preserved?]
  (cond
    (nil? index-meta)        [:rebuild :absent]
    (not handles-preserved?) [:rebuild :handles-remapped]
    :else (if-let [r (snapshot/index-mismatch index-meta fingerprint)]
            [:rebuild r] [:replay])))

(defn- replay-index!
  "Install the dumped entries into `kb`'s index, or report why not: nil on success, else a
  rebuild reason. Installed in bounded batches through `snapshot/install-entries!` and
  checked at the end for a stream that ends early or does not read. The file behind the
  stream is closed however this leaves. `records-only?` leaves out the families the stored
  justifications derive (`kv/justification-family-entry?`); the count checked is the
  stream's."
  [kb dir compression read-fn expected records-only?]
  (let [read-n (volatile! 0)]
    (try
      (let [stream (read-fn (io/file dir frames/index-dir frames/index-entry-file) compression)]
        ;; the closer holds the file and not the seq, so the entries installed stay
        ;; collectable: a dump of a large KB holds more entries than the heap does
        (with-open [_ (frames/closer stream)]
          (let [n (snapshot/install-entries!
                   (:index kb)
                   (sequence (comp (map #(do (vswap! read-n inc) %))
                                   (remove #(and records-only? (kv/justification-family-entry? %))))
                             stream)
                   expected)
                n (if records-only? @read-n n)]
            (when-not (= (long n) (long expected))
              (trove/log! {:level :warn :id ::index-short
                           :msg (str "index entry stream holds " n " entries, index.edn says "
                                     expected)})
              :entries-truncated))))
      (catch Exception e
        (trove/log! {:level :warn :id ::index-unreadable
                     :msg (str "index entry stream unreadable: " (ex-message e))})
        :entries-truncated))))

(defn- install-index!
  "Put the index in place: replay the dump's entries when they fit the records just stored,
  else rebuild from those records. Returns `{:index :replayed :entries n}` or `{:index
  :rebuilt :reason r}`. A rebuild is logged at `:info` with its reason, and `reindex` clears
  the index first, so a failed replay is wiped. `records-only?` is `replay-index!`'s."
  [kb dir compression read-fn index-meta fingerprint preserved? on-progress records-only?]
  (let [[verdict reason] (index-decision index-meta fingerprint preserved?)
        rebuild (fn [r]
                  (trove/log! {:level :info :id ::index-rebuilt
                               :msg  (str "import: index rebuilt rather than replayed: " (name r))
                               :data {:reason r}})
                  (on-progress {:phase :reindex :done 0 :total nil})
                  (reindex/reindex kb)                    ; clears the index itself
                  {:index :rebuilt :reason r})]
    (if (= :replay verdict)
      (do
        (on-progress {:phase :index-entries :done 0 :total (:entry-count index-meta)})
        (if-let [r (replay-index! kb dir compression read-fn (:entry-count index-meta)
                                  records-only?)]
          (rebuild r)
          (do (trove/log! {:level :info :id ::index-replayed
                           :msg  (format "import: index replayed, %,d entries" (long (:entry-count index-meta)))})
              {:index :replayed :entries (:entry-count index-meta)})))
      (rebuild reason))))

;;; ── records-only (no belief) ──────────────────────────────────────────

(defn- bulk-load-records-only!
  "The `{:belief? false}` inline pass: for each sentex frame, re-canonicalize, store and index
  the record in the same pass. Records go through a `capabilities/sentex-sink` inside
  `with-bulk-writes`. No dedup map and no `sx-meta`: frames map 1:1 to handles, and with
  `preserve?` each record is stored at its dump `:id`. A frame with no `:id` is minted a
  handle, and the count is reported. `index?` false skips the inline index build, when the
  caller will replay the dump's index. Reports progress every `report-every` frames. Returns
  `{:sentexes n :frames n :rules n :minted n :expanded {:frames n :records n} :refused {…}
  :fingerprint {…} :naming {…}}`; `:sentexes` is what got stored and `:frames` what the
  stream yielded. `:naming` folds `nm/tally` over the stored records, and `:refused` counts
  the frames the constructor will not build and the records `storable-sentexes` refuses
  (docs/naming.md, \"Whose invariants: the two policies\")."
  [kb frames decode preserve? index? report-every on-progress total]
  (let [records (:records kb)
        index   (:index kb)
        n       (volatile! 0)            ; what got stored
        seen-n  (volatile! 0)            ; what the stream yielded, for the torn check
        rules   (volatile! 0)
        minted  (volatile! 0)
        naming  (volatile! nm/empty-tally)
        refused (volatile! empty-refusals)
        expanded (volatile! {:frames 0 :records 0})
        extras  (volatile! [])            ; an expanded frame's further forms
        fprint  (fp/accumulator)
        ;; a dump naming a handle twice with different content is a broken dump; the same refusal
        ;; `import-sentexes!` makes, kept in a BitSet so the streaming path stays streaming
        ids     (java.util.BitSet.)]
    ;; the frame stream closed beside the sink (`frames/closer`): a duplicate handle
    ;; throws out of the middle of the walk, and a frame seq only closes its file when it
    ;; is consumed to the end or raises the failure itself
    (with-open [^java.io.Closeable sink   (cap/sentex-sink records {:premises? true})
                ^java.io.Closeable _stream (frames/closer frames)
                r                          (progress/start ::bulk-store-sentexes
                                                           (if index?
                                                             "import: store and index the sentexes"
                                                             "import: store the sentexes")
                                                           total)]
      (mem/with-bulk-writes (:backend index)
        (let [;; through a `sentex-sink`, which on every store the engine ships is
              ;; `put-sentex` and the premise mark, or the store's bulk path. The handle is decided here,
              ;; so the index build below stays inline. `:premises? true`: the record already holds the
              ;; strength, so the mark is the set-add and never a second record write. `frame?` is false
              ;; for an expanded frame's further forms, which are not counted in `:minted`.
              store!
              (fn [rec did frame?]
                (let [h (if (and preserve? did)
                          (let [did (long did)]
                            (when (and (<= 0 did) (< did Integer/MAX_VALUE))
                              (when (.get ids (int did))
                                (throw (ex-info (str "dump names handle " did " twice — a"
                                                     " handle-preserving import gives each"
                                                     " record the id the dump names, so two"
                                                     " records cannot claim one")
                                                {:type :duplicate-handle :handle did})))
                              (.set ids (int did)))
                            (p/write-record! sink (assoc rec :id did)))
                          (do (when (and preserve? frame?) (vswap! minted inc))
                              (p/write-record! sink rec)))
                      c (vswap! n inc)]
                  (fprint h rec)
                  (if index?
                    (when (reindex/index-one! index rec h) (vswap! rules inc))
                    (when (rules/rule? rec) (vswap! rules inc)))
                  (when (zero? (mod (long c) (long report-every)))
                    (on-progress {:phase :sentexes :done c :total total}))))]
          (doseq [frame frames]
            (progress/tick! r)
            (vswap! seen-n inc)
            (let [fm   (as-asserted (decode frame))
                  _    (vswap! naming nm/tally (:sentence fm) (:context fm))
                  ;; born carrying its strength, ours only, as on the belief path: a record stored
                  ;; strength-less here would recover with nothing believed. Counted and skipped when this
                  ;; build's structural checks refuse the sentence.
                  recs (try
                         (cond->> (storable-sentexes kb (:sentence fm) (:context fm))
                           (and preserve? (:strength fm))
                           (mapv #(assoc % :strength (strength-class (:strength fm)))))
                         (catch clojure.lang.ExceptionInfo e
                           (if-let [ty (dump-disagreement e)]
                             (do (vswap! refused tally-refusal ty) nil)
                             (throw e))))]
              (when-let [[rec & more] (seq recs)]
                (store! rec (:id fm) true)
                (when more
                  (vswap! expanded #(-> % (update :frames inc) (update :records + (count recs))))
                  (vswap! extras into more)))))
          ;; An expanded frame's further forms are stored after the stream, so the handles
          ;; they are minted never take a dump id a later frame claims.
          (run! #(store! % nil false) @extras))))
    {:sentexes @n :frames @seen-n :rules @rules :minted @minted :expanded @expanded
     :refused (assoc @refused :checked @seen-n)
     :fingerprint (fprint) :naming @naming}))

(defn- import-records-only!
  "The `{:belief? false}` path: store and index every sentex in one streaming pass, with no
  justifications and no TMS. The premise marks are kept for a dump of ours and only for one
  of ours: a foreign frame's `:strength` is not the premise mark, so a foreign records-only
  import records no premise and a later `recover` believes nothing (`:belief? :stored` is the
  route for a foreign corpus). This path decides upfront whether a replay is possible from the
  layout and `preserve?`; a fingerprint mismatch afterwards falls back to a full rebuild."
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
                                     (:fingerprint result) preserved? on-progress true)
                     ;; the inline pass indexed each record; the supporter families are
                     ;; posted from the stored declarations once every record is in
                     (do (special/post-taxonomy-supporters! kb) {:index :inline}))]
    (trove/log! {:level :info :id ::records-loaded
                 :msg (format "import: loaded %,d sentexes (no belief), index %s"
                              (long (:sentexes result)) (name (:index idx)))})
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
            :expanded          (:expanded result)
            :rules             (:rules result)
            :justifications        0
            :naming            (:naming result)
            :refused           (:refused result)}
           idx)))

;;; ── the entry point ───────────────────────────────────────────────────

(def ^:private import-opt-keys
  "Every key `import-dump` reads."
  #{:belief? :report-every :on-progress :drop-principal? :reasoners})

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

(defn check-import-opts!
  "Refuse an opts key `import-dump` does not read, an unknown `:belief?` value, and a non-nil
  non-map `opts`, before `meta.edn` is looked at. A misspelt `:belief?` key or value would
  otherwise take the default and run the recover the caller meant to skip."
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
                     :values (vec (sort-by pr-str (keys belief-modes)))})))
  (when (and (contains? opts :reasoners) (not= :stored (:reasoners opts)))
    (throw (ex-info (str "unknown :reasoners value " (pr-str (:reasoners opts))
                         " — import-dump reads :stored, which registers the dump's set")
                    {:type :unknown-option :mismatch :bad-value :option :reasoners
                     :value (:reasoners opts) :values [:stored]}))))

(defn dump-reasoners
  "The reasoners `kb` registers once the dump `meta` describes has landed: nil when `meta`
  records no set or records `kb`'s own, and the dump's set under `:reasoners :stored` when
  it holds every name `kb` registered.  Any other pair is refused (`:reasoner-mismatch`);
  `import-dump` asks before the first write, and `vaelii.core/import!` registers the
  answer after the recover."
  [kb meta dir {want :reasoners}]
  (when-let [dumped (some-> (:reasoners meta) set)]
    (let [have (kb/reasoners-of kb)]
      (cond
        (= dumped have) nil
        (and (= :stored want) (every? dumped have)) dumped
        :else (throw (kb/reasoner-mismatch
                      (str "the dump at " dir) dumped have
                      (str "Register " (pr-str (vec (sort dumped)))
                           " on the destination first, or import with :reasoners"
                           " :stored to register the dump's set.")))))))

(def ^:private content-refusals
  "The `:type`s of the refusals of a dump's own content that a frame decides in the middle of
  a record stream, after the frames before it are stored: `:duplicate-handle`,
  `:no-foreign-reader` (also a foreign reader map missing a field the import reads),
  `:bad-foreign-manifest` and `:disallowed-class` (`vaelii.impl.io.thaw`). A torn stream
  (`:truncated-dump`) is not here."
  #{:duplicate-handle :no-foreign-reader :bad-foreign-manifest :disallowed-class})

(defn- clearing-on-refusal
  "Call `f`, the phase of an import that writes the records. When it throws a refusal in
  `content-refusals`, empty `kb`'s record store and index, put back the `:no-belief` hazard
  `hazards` holds, and rethrow; any other throw is rethrown with the store as it stands.
  `import-dump` refuses a destination holding a sentex, so the wipe removes only what this
  import wrote. A wipe that fails is added to the refusal as suppressed."
  [kb hazards f]
  (try
    (f)
    (catch clojure.lang.ExceptionInfo e
      (when (contains? content-refusals (:type (ex-data e)))
        (try
          (p/clear-records! (:records kb))
          (p/clear-index! (:index kb))
          ;; the stores moved without going past a per-sentex choke point, as at
          ;; `core/clear!`, so the change clock is bumped here
          (observe/note-change)
          (swap! (:unrecovered kb) #(merge (dissoc % :no-belief) hazards))
          (catch Throwable t (.addSuppressed e t))))
      (throw e))
    ;; the records arrived past `kb/create-sentex`, or left
    (finally (kb/forget-mint-rules! kb) (kb/forget-lazy-rules! kb))))

(defn- land-belief-records!
  "The writes of a `{:belief? true|:stored}` import, in order: the sentex pass, the
  embedded-handle rewrite, the justification and provenance passes and the premise marks
  for a dump of ours, or the foreign reader's `replay-belief!` for one that is not.
  Everything after this in `import-dump` is the index install and the recover.

  A foreign reader's `replay-belief!` is looked up before the first write, since the
  reader map is in hand and a map without one refuses the dump whatever its frames hold.
  Returns what the summary reads."
  [kb dir meta compression read-fn decode ours? tick jprint drop-principal?]
  (let [replay-belief! (when-not ours? (dump-reader-field :replay-belief!))
        ;; the last check decidable from the dump alone, so the last before the first write: a `:out`
        ;; frame refused inside the justification loop would refuse a KB already holding every sentex
        ;; (`assert-no-naf-justifications!`)
        _ (when ours?
            (assert-no-naf-justifications!
             (read-fn (io/file dir frames/justification-file) compression)
             (:justification-count meta)))
        {:keys [sx-meta embedding collapsed minted expanded expansions fingerprint naming
                frames refused]}
        (import-sentexes! kb (read-fn (io/file dir frames/sentex-file) compression)
                          decode ours? (tick :sentexes (:sentex-count meta))
                          (:sentex-count meta))
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
        ;; every record landed where the dump said, so the id map is the identity and
        ;; there is nothing to remap or to rewrite
        kept?    (and ours? (zero? (long collapsed)) (zero? (long minted)))
        ;; before anything reads a handle out of stored content
        rewrite  (if kept?
                   {:rewritten 0 :dropped 0 :deleted #{}}
                   (rewrite-embedded-handles! kb embedding old->new))
        ;; ...and before anything reads the id map again, since the pass above deleted
        ;; records the map still names.  The two shadow the maps they are derived from, so
        ;; no reader below can reach a dump id whose record this import has removed.
        {:keys [sx-meta old->new orphaned]}
        (forget-deleted sx-meta old->new (:deleted rewrite))
        ;; a merged record is not gone: its dump ids name the survivor from here on
        {:keys [sx-meta old->new]} (follow-merged sx-meta old->new (:merged rewrite))
        collapsed (+ (long collapsed) (count (:merged rewrite)))
        {:keys [premises provenance dropped dropped-orphaned]}
        (if ours?
          ;; ours says it directly: justifications are justifications, and a premise is a
          ;; sentex carrying a strength
          (let [{:keys [dropped dropped-orphaned ids frames]}
                (import-justifications!
                 kb (read-fn (io/file dir frames/justification-file) compression) old->new
                 orphaned kept?
                 (tick :justifications (:justification-count meta))
                 jprint (:justification-count meta))
                ;; the same witness the sentex stream gets, and the stream that most needs
                ;; it: a torn justification file is indistinguishable from a clean EOF, and
                ;; what it loses is belief — a KB that recovers to fewer conclusions than it
                ;; was exported with, silently
                _ (check-frame-count! :justifications frames (:justification-count meta))]
            {:premises   (mark-premises-by-strength kb sx-meta)
             ;; both kinds' handles, since a provenance frame can name either and the two
             ;; draw from one counter, so nothing collides
             :provenance (import-provenance-frames!
                          kb dir compression read-fn (merge old->new ids)
                          (:provenance-count meta) drop-principal?)
             :dropped    dropped
             :dropped-orphaned dropped-orphaned})
          ;; a foreign dialect's account, read by its own reader
          (closing-every-stream
           read-fn
           (fn [read-fn]
             (replay-belief!
              kb {:dir dir :compression compression :read-fn read-fn :meta meta
                  :sx-meta sx-meta :old->new old->new :orphaned orphaned
                  :ticker tick :strength-class strength-class}))))
        ;; after either dialect's premise pass, which marks a frame's first form only
        premises (+ (long (or premises 0)) (long (mark-expanded-premises kb expansions)))]
    (when-let [line (orphan-line {:dropped (:dropped rewrite)
                                  :orphaned (count orphaned)
                                  :justifications (or dropped-orphaned 0)})]
      (trove/log! {:level :warn :id ::meta-sentexes-dropped
                   :msg  line
                   :data {:dropped-meta-sentexes (:dropped rewrite)
                          :orphaned-ids (count orphaned)
                          :dropped-justifications-orphaned (or dropped-orphaned 0)}}))
    {:collapsed collapsed :expanded expanded :fingerprint fingerprint :naming naming
     :frames frames
     :refused refused :kept? kept? :rewrite rewrite :orphaned orphaned
     :premises premises :provenance provenance :dropped dropped
     :dropped-orphaned dropped-orphaned}))

(defn- dump-belief!
  "The belief half of a `{:belief? true}` import: install the dump's reasoning image in place
  of `recover` when the import kept every handle (`kept?`) and the dump carries one, and
  recover otherwise.  The image's records fingerprint is checked against `sentex-fp` and
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
  "Import a vaelii export dump from `dir` into the empty `kb`: one `vaelii.impl.io.export`
  wrote, or a foreign dialect this build has a reader for (`vaelii.impl.foreign`). Reads
  `meta.edn` first; the version is checked against its dialect's numbering and the
  destination must be empty (`:pg-memory` and an unknown variant throw).

  `opts`: `{:belief? true|:stored|false :report-every n :on-progress f :drop-principal?
  bool}`. `:belief? true` (the default) lands in the state the restart path produces,
  installing a dump's reasoning image in place of `recover` when every handle was kept and
  the records, source identity and belief policies equal its manifest; `{:reasoning
  :installed}` or `{:reasoning :recovered :reason r}` says which. `false` stores and indexes
  every sentex and skips justifications, premise marks and `recover`. `:stored` does
  everything `true` does except `recover`. An unknown `:belief?` value is refused by name.
  `:drop-principal? true` lands provenance without `:principal`. `:on-progress` is called
  every `report-every` frames with `{:phase :done :total}`; a callback that throws cancels
  the import where it stands, and the KB keeps what landed.

  A dump refused for its own content leaves the store as it found it (the refusals before the
  first write, and `content-refusals` through `clearing-on-refusal`).

  The summary reports `:dialect`, `:handle-policy` (`:preserved`, or `:remapped` with
  `:collapsed`), `:index` (`{:index :replayed :entries n}` or `{:index :rebuilt :reason r}`),
  `:naming` (what `assert` would have refused, `{:checked n :refused n :by-class {…}}`),
  `:refused` (`{:checked n :skipped n :by-type {…}}`, frames the constructor will not build
  or whose record would answer wrongly), `:expanded`, `:dropped-meta-sentexes`,
  `:orphaned-ids`, `:dropped-justifications` and `:dropped-justifications-orphaned`.
  Skipping is not repair: whatever names a skipped rule is dropped in turn. See
  docs/storage.md, \"Importing a dump\"."
  ([kb dir] (import-dump kb dir {}))
  ([kb dir {:keys [belief? report-every on-progress drop-principal?]
            :or   {belief? true report-every 500000 on-progress no-progress}
            :as   opts}]
   (check-import-opts! opts)
   (let [meta    (read-meta dir)
         variant (check-dump! meta)]
     (assert-empty-destination! kb)
     (dump-reasoners kb meta dir opts)
     (let [compression (or (:compression meta) :none)
           read-fn     (cond-> (stream-reader-for meta) *wrap-reader* (*wrap-reader*))
           decode      (frame-decoder)
           ;; what the KB declared before this import declares its own, which a refusal
           ;; of the dump's content puts back (`clearing-on-refusal`)
           hazards     (select-keys @(:unrecovered kb) [:no-belief])]
       ;; Declared before the first write: a load that skips the recover (`false`, `:stored`)
       ;; leaves a store identical to one of `assert-inert` sentexes, and `open-kb` has already noted
       ;; the empty destination's belief clean. Said here so it holds when the load throws part-way.
       (when-not (true? belief?)
         (kb/note-hazards! kb {:no-belief true}))
       ;; A bulk load trips the disk durability daemon's dead-ratio compaction repeatedly, each
       ;; rewriting the growing index under the backend lock. Pause auto-compaction for the load;
       ;; the daemon compacts once afterwards (a no-op on `:memory`).
       (dur/call-with-compaction-paused
        (fn []
          ;; `false` is the only value that skips the belief phases; `:stored` runs them
          ;; and stops before the recover, which is decided at the one call site below.
          (if (false? belief?)
            (let [summary (clearing-on-refusal
                           kb hazards
                           #(import-records-only! kb dir meta compression read-fn decode
                                                  (ours? meta) report-every on-progress))]
              (check-frame-count! :sentexes (:frames summary) (:sentex-count meta))
              (trove/log! {:level :info :id ::import-complete
                           :msg  (format "import: done, %,d sentexes indexed, no belief"
                                         (long (:sentexes summary)))
                           :data summary})
              summary)
            (let [ours?  (ours? meta)
                  tick   (fn [phase total] (ticker on-progress phase total report-every))
                  jprint (fp/accumulator fp/justification-hash)
                  {:keys [collapsed expanded fingerprint naming frames refused kept? rewrite
                          orphaned premises provenance dropped dropped-orphaned]}
                  (clearing-on-refusal
                   kb hazards
                   #(land-belief-records! kb dir meta compression read-fn decode ours?
                                          tick jprint drop-principal?))]
              ;; put the index in place, the dump's own entries when they fit these records, else rebuilt
              ;; from them, and then recover the JTMS and taxonomy and settle belief. `:stored` stops here:
              ;; `recover` is the only step that builds in-memory state, so a later `recover` reads the
              ;; store as a restart would.
              (let [idx (install-index! kb dir compression read-fn (read-index-meta dir)
                                        fingerprint kept? on-progress false)
                    img (when (true? belief?)
                          (dump-belief! kb dir (and ours? kept?) fingerprint jprint))]
                (let [summary (merge
                               {:variant            variant
                                :dialect            (if ours? :vaelii :engine)
                                :handle-policy      (if kept? :preserved :remapped)
                                :collapsed          collapsed
                                :expanded           expanded
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
                               :msg   (str (format "import: done, %,d sentexes, %,d justifications, index "
                                                   (long (:sentexes summary)) (long (:justifications summary)))
                                           (name (:index summary))
                                           (when-not (true? belief?)
                                             " — belief stored and NOT settled; run recover"))
                               :data  summary})
                  summary))))))))))
