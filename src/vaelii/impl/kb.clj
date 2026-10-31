;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.kb
  "The KB record, its constructor, and the ground floor of retrieval: find/create
  sentexes, the belief-filtered `sentexes-matching`, and the equality-closure goal
  rewriting.  Bottom of the engine stack (kb <- checks <- special <- integrate <- chain <-
  settle <- vaelii.core): it reads the storage protocols, the taxonomy, the JTMS and the
  matchers, never assertion, chaining or settling.  See docs/namespaces.md."
  (:refer-clojure :exclude [isa?])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.config :as config]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.dense-jtms :as dense-jtms]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.disk.index-snapshot :as snapshot]
            [vaelii.impl.except :as exc]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.kb :as kb-types]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [vaelii.impl.columnar ColumnarIndexStore]
           [vaelii.impl.dense_jtms DenseTms]
           [vaelii.impl.dense_kv TieredKvBackend]
           [vaelii.impl.kv KvIndexStore]
           [vaelii.impl.memory MemoryKvBackend MemoryRecordStore]))

;; ---- storage selection: two independent axes ------------------------------
;;
;; The records are the ground truth and the question there is durability; the index is derived
;; (`reindex` rebuilds it through the protocols) and the question there is representation.  The axes
;; are `:records` (`:memory` / `:disk`) and `:index` (`:memory` / `:dense` / `:columnar` /
;; `:disk-log`); `:backend` names a pair, spelled `<records>-<index>`, and every legal pair has a name.

(def ^:private backend-modes
  "The `:backend` sugar: each name expands to a `{:records :index}` pair, read
  `<records>-<index>` (`:disk-memory` is durable records with the derived index in RAM,
  rebuilt on open).  `:memory` is the one pair named for the single store on both axes.
  `:disk-log` is durable records under the log index (a RAM map with a write-ahead log,
  `vaelii.impl.disk.kv`).  `:disk-snapshot` is `:columnar` plus the promise that an open maps
  `<dir>/index/` when the image still describes the records; any doubt reindexes and warns.
  Adapter axes (`:sqlite`, `:pg`) resolve lazily.  RAM records with the log index or the image
  are refused (`backend-axes`).  docs/storage.md, Backend selection."
  {:memory          {:records :memory :index :memory}
   :memory-dense    {:records :memory :index :dense}
   :memory-columnar {:records :memory :index :columnar}
   :disk-memory     {:records :disk   :index :memory}
   :disk-dense      {:records :disk   :index :dense}
   :disk-columnar   {:records :disk   :index :columnar}
   :disk-snapshot   {:records :disk   :index :snapshot}
   :disk-log        {:records :disk   :index :disk-log}
   :sqlite          {:records :sqlite :index :memory}
   :pg-memory       {:records :pg     :index :memory}
   :pg-disk-log     {:records :pg     :index :disk-log}
   :pg-snapshot     {:records :pg     :index :snapshot}
   ;; a fork: both halves decorate whatever the frozen base resolved to, so `:overlay` is
   ;; a *decorator* selection rather than a store — see the `:base` / `:overlay` opts
   :overlay         {:records :overlay :index :overlay}})

(def backend-names
  "Every `:backend` name, sorted — `backend-modes` is past the size at which a map
  literal keeps its order, so the list is sorted rather than claiming one.  Public for
  `opt-keys`' reason — it is the answer to \"is this a real backend?\", and a caller who
  can ask does not have to find out from a refusal — and because the list has readers
  outside this process: the suite's configuration list (`scripts/lib/suite-configs.sh`),
  the parity test (`backend_parity_test`) and docs/storage.md's table each cover it, and
  a name none of them knows about is a backend that ships untested and undocumented.
  Those three hold themselves to this vector, each naming what it leaves out and why."
  (vec (sort (keys backend-modes))))

;; ---- the two axis vocabularies -------------------------------------------
;;
;; One row per axis, holding what is said about an axis and never what opens it: the arms are
;; `record-arms` / `index-arms` at the bottom of this namespace, and `check-backends!` joins the two
;; at load, so an axis declared here and openable nowhere is a build failure.

(def ^:private record-axes
  "Every record axis, one row: `:durable?` (outlive the JVM); `:persisted-index?` (may a durable
    index half sit over them; narrower than `:durable?`, since `:sqlite` has no shared lifecycle
    with index files); `:image?` (may the mapped index image sit over them: the store implements
    `p/ImageFingerprinting`, and `:persisted-index?` holds, `check-backends!`); `:adapter` and
    `:ctor` (the sibling carrying the store, resolved lazily by `adapter-ctor`); `:decorator?`
    (`:overlay`, resolved by `open-kb`; every axis function refuses it)."
  {:memory  {:durable? false :persisted-index? false :image? false}
   :disk    {:durable? true  :persisted-index? true  :image? true}
   :sqlite  {:durable? true  :persisted-index? false :image? false :adapter "com.vaelii/sqlite"
             :ctor 'vaelii.sqlite.record-store/sqlite-record-store}
   :pg      {:durable? true  :persisted-index? true  :image? true  :adapter "com.vaelii/postgres"
             :ctor 'vaelii.postgres.record-store/pg-record-store}
   :overlay {:decorator? true}})

(def ^:private durable-under-log-index
  "The record axes a persisted index half may sit over: `record-axes`' `:persisted-index?`
  as a set.  `:disk` shares the index's directory and lifecycle; `:pg` is on a server, so
  a local index file is the only one its records can have (docs/storage.md).  A `:disk-log`
  index over records that vanish at JVM exit would be read as truth on the next open; an
  image over them is caught by its fingerprint (`:records-differ`) at the cost of a rebuild,
  and is refused anyway."
  (into #{} (comp (filter (comp :persisted-index? val)) (map key)) record-axes))

(def ^:private image-record-axes
  "The record axes the mapped image pairs with — `record-axes`' `:image?` rows, as a set."
  (into #{} (comp (filter (comp :image? val)) (map key)) record-axes))

(def ^:private index-axes
  "Every index axis, one row.  `:durable?`: does the index open already populated; only
    `:disk-log` answers true, and `:snapshot` answers false because the mapped image is an
    attempt on the way into the rebuild.  `:pairs-with`: the record axes this index may sit
    over, derived from `record-axes` (`:image?` for `:snapshot`, `:persisted-index?` for
    `:disk-log`) and spliced into `backend-axes`' refusal, with `:why` as its ending.
    `:decorator?` as in `record-axes`.  A row with `:pairs-with` is checked twice: for
    `:persisted-index?` records, then by the axis's own set."
  {:memory   {:durable? false}
   :dense    {:durable? false}
   :columnar {:durable? false}
   :snapshot {:durable?   false
              :pairs-with image-record-axes
              :why        "an image carries a fingerprint of the records it was built from, so over a store that empties at JVM exit every open discards it and reindexes — the representation the name asks for is one this pairing can never hold"}
   :disk-log {:durable?   true
              :pairs-with durable-under-log-index
              :why        "persisting the derived half over a store that empties at JVM exit leaves index files describing records that are gone, and the next open answers every query out of them believing nothing is wrong"}
   :overlay  {:decorator? true}})

(defn- axis-prose
  "A seq of axis keywords as a refusal spells them: `:memory, :disk, :sqlite or :pg`.
  Derived rather than written beside the axis table, because a hand-written twin of a set
  is a sentence free to describe a pairing the pairing check does not make.  Order is the caller's — a
  list reads in its own order and a set is sorted on the way in."
  [axes]
  (let [v (vec axes)]
    (if (< (count v) 2)
      (str/join (map pr-str v))
      (str (str/join ", " (map pr-str (butlast v))) " or " (pr-str (last v))))))

(def ^:private durable-index-axes
  "The index axes that need a `durable-under-log-index` record axis under them, and for
  each the prose pairing and the sentence saying why — both spliced into `backend-axes`'
  refusal.  Read off `index-axes`' `:pairs-with` / `:why`.

  Both name `:disk` and `:pg` today; `:snapshot`'s set is the `:image?` rows, so an axis
  that may persist an index and answers no records fingerprint is refused it here."
  (into {} (comp (filter (comp :pairs-with val))
                 (map (fn [[kind {:keys [pairs-with why]}]]
                        [kind {:with (axis-prose (sort pairs-with)) :why why}])))
        index-axes))

(def ^:private reserved-backend-names
  "Names `open-kb` refuses outright, and the pairing to take instead.  `:disk` and `:pg-disk`
  read as both halves out of core, which no pairing here is: the log index holds its whole
  key-value map in RAM and the log buys durability, not residency (`vaelii.impl.disk.kv`).
  Refused and not aliased, since an index axis names a directory layout and a name answering
  to two of them opens a layout its caller did not ask for."
  {:disk    :disk-log
   :pg-disk :pg-disk-log})

(defn backend-axes
  "The `{:records :index}` selection for `opts`: the `:backend` sugar expanded, with an
  explicit `:records` / `:index` opt overriding its half.  Public so a harness asking which
  two stores an opts map names reads the table `open-kb` does.  Refuses (naming the pairing
  to take instead): the `:disk-log` index over non-durable records (`durable-under-log-index`),
  the `:snapshot` index over a store with no records fingerprint (`image-record-axes`),
  `:overlay` on one axis alone, and the reserved names (`reserved-backend-names`)."
  [{:keys [backend records index] :or {backend :memory}}]
  (when-let [want (reserved-backend-names backend)]
    (throw (ex-info (str "unknown KB backend " (pr-str backend) " — the durable-index pairing is "
                         "spelled " (pr-str want) ", durable records under a write-ahead-logged "
                         "index whose key->value map is in RAM.  The log buys durability and not "
                         "residency; the name says which.")
                    {:type :unknown-backend :mismatch :reserved-name
                     :axis :backend :kind backend :backend backend :instead want})))
  (when (= :disk index)
    (throw (ex-info (str "unknown index backend :disk — the write-ahead-logged index is "
                         ":disk-log.  It holds the whole key->value map in RAM and logs its "
                         "mutations, so the log buys durability and not residency; the name "
                         "says which.")
                    {:type :unknown-backend :mismatch :reserved-name
                     :axis :index :kind index :index index :instead :disk-log})))
  (let [pair (or (backend-modes backend)
                 (throw (ex-info (str "unknown KB backend " (pr-str backend) " — want one of "
                                      (pr-str (vec (sort (keys backend-modes))))
                                      ", or the :records / :index opts")
                                 {:type :unknown-backend :mismatch :unknown-name
                                  :axis :backend :kind backend :backend backend})))
        axes {:records (or records (:records pair))
              :index   (or index   (:index pair))}]
    (when (not= (= :overlay (:records axes)) (= :overlay (:index axes)))
      (let [half (if (= :overlay (:records axes)) :index :records)]
        (throw (ex-info (str "a fork is :overlay on both axes, and this selection is "
                             (pr-str (:records axes)) " records under an "
                             (pr-str (:index axes)) " index.  The fork's records and its index "
                             "decorate one base together; either half alone reads the base "
                             "through one store and not the other.  Spell the fork "
                             "{:backend :overlay :base … :overlay …}, or set " half
                             " :overlay.")
                        {:type :unknown-backend :mismatch :illegal-pair
                         :axis half :kind (get axes half) :instead :overlay
                         :records (:records axes) :index (:index axes)}))))
    (when-let [{:keys [with why]} (and (not (durable-under-log-index (:records axes)))
                                       (durable-index-axes (:index axes)))]
      (throw (ex-info (str "the " (:index axes) " index needs durable records — " with " — and these are "
                           (pr-str (:records axes)) ".  An index is derived from the records, so "
                           why ".  `:sqlite` records already live in a directory, and a durable index "
                           "beside them is this pairing without its shared lifecycle: take :disk-log or "
                           ":disk-snapshot for that.  Otherwise take a derived index (`:memory`, `:dense`, "
                           "`:columnar`), rebuilt on open.")
                      {:type :unknown-backend :mismatch :illegal-pair
                       :axis :index :kind (:index axes)
                       :records (:records axes) :index (:index axes)})))
    axes))

(defn durable-dirs
  "The canonical directories `open-kb` over `opts` would take an exclusive lock on: the
  records/index directory (`:disk` records or a `:disk-log` index) and, for a durable fork,
  the fork's own writable directory.  `core/open-kb` releases the ones this call newly opened
  when a throw after the stores resolve would leave a lock held.  Empty for an all-in-RAM KB.
  Pure over `opts`; malformed opts answer empty, and the construction throws the refusal."
  [opts]
  (try
    (let [{rkind :records ikind :index} (backend-axes opts)
          ov      (:overlay opts)
          {ovr :records} (when ov (backend-axes ov))]
      (into []
            (distinct)
            (concat
             (when (or (= :disk rkind) (= :disk-log ikind) (= :snapshot ikind))
               [(disk/canonical-dir (disk/disk-dir opts))])
             (when (= :disk ovr)
               [(disk/canonical-dir (disk/disk-dir ov))]))))
    (catch Throwable _ [])))

(defn release-index-space!
  "Forget the RAM derived index a disk-backed KB held under `space` — the dir-keyed
  derived-index state in the three RAM index backends.  `core/close!` calls this with the
  `:index-space` the KB recorded when it opened, so a process opening durable KBs in a loop
  does not keep one derived index per directory it has finished with.  The space belongs to
  at most one of the three backends and the others no-op, so the caller needs no record of
  which held it.  A no-op for nil — an all-in-RAM KB keeps its space (its store, not a
  derived cache) and a durable-index KB's index is released with its directory."
  [space]
  (boolean
   (when space
     (or (mem/drop-index-space! space)
         (dense/drop-index-space! space)
         (columnar/drop-state-space! space)))))

(defn release-engine-space!
  "Drop the private in-RAM space `space` (`mem/engine-space`) from every RAM registry: the
  records and their handle counter, the index, and a fork's bookkeeping
  (`mount/meta-kv`).  `core/close!` calls this with the KB's `:engine-space`.  A no-op for
  nil."
  [space]
  (when space
    (mem/drop-record-space! space)
    (release-index-space! space)
    (mem/drop-index-space! (mount/meta-space space))
    nil))

(defn- adapter-ctor
  "The record-store constructor of the sibling adapter carrying `records` (`record-axes`'
  `:ctor`), resolved **lazily**, so the SSPL engine never loads a driver unless a KB
  selects that axis.  Throws `:missing-adapter` naming the coordinate when the adapter is
  not on the classpath, and when loading it fails on a namespace it requires, which is
  what a `checkouts/` link without the adapter's dependencies causes."
  [records]
  (let [{:keys [adapter ctor]} (record-axes records)
        sibling (name (symbol adapter))
        refuse (fn [found cause]
                 (throw (ex-info (str "the " records " record backend needs the vaelii-" sibling
                                      " adapter (" adapter ") on the classpath with its "
                                      "dependencies" found " — an Apache-2.0 sibling the engine "
                                      "does not depend on, so add it to your project as a "
                                      "dependency (in this repository, `lein with-profile "
                                      "+with-" sibling "`).")
                                 {:type :missing-adapter :records records :coordinate adapter}
                                 cause)))]
    (try (requiring-resolve ctor)
         (catch java.io.FileNotFoundException _
           (refuse "" nil))
         (catch clojure.lang.Compiler$CompilerException e
           (let [cause (.getCause e)]
             (if (instance? java.io.FileNotFoundException cause)
               (refuse (str "; loading it failed (" (.getMessage cause) ")") e)
               (throw e)))))))

(defn- pg-spec
  "The `:pg` opt as a db-spec map.  A string is a JDBC URL, which is the spelling an
  environment variable arrives in; a map is a next.jdbc db-spec, plus the adapter's own
  keys (`:schema` and the cache sizes), and is passed through untouched."
  [pg]
  (if (string? pg) {:jdbcUrl pg} pg))

(def ^:private record-arms
  "The arms half of `record-axes`: axis -> `(fn [opts] record-store)`.  `:memory` keys the
  in-RAM store by `:space`; `:disk` opens only the records in a directory (`:dir`, else from
  the space number), shared per directory (`vaelii.impl.disk.backend`); `:sqlite` and `:pg`
  resolve sibling adapters lazily.  `:overlay` has no arm: `open-kb` resolves it."
  {:memory (fn [{:keys [space] :or {space 0}}] (mem/memory-record-store {:space space}))
   :disk   (fn [opts] (disk/records-for (disk/disk-dir opts)))
   ;; a single file under the KB's directory; ensure the directory exists (SQLite
   ;; creates the file, not its parent), the way the disk backend makes its own dir.
   :sqlite (fn [opts]
             (let [dir (disk/disk-dir opts)]
               (.mkdirs (java.io.File. ^String dir))
               ((adapter-ctor :sqlite) {:dbtype "sqlite" :dbname (str dir "/records.sqlite")})))
   ;; the database is named by the caller and nothing here derives one: a KB that
   ;; silently took a default server is a KB whose records are somewhere nobody said
   :pg     (fn [opts] ((adapter-ctor :pg) (pg-spec (:pg opts))))})

(defn- record-store-for
  "The `RecordStore` for the record axis, opened by its `record-arms` arm.

  A name outside `record-arms` is refused naming the accepted names.  `:overlay` reaching here means a
  base or an overlay half was itself declared `:overlay`, and a stack of forks is
  deliberately not built (docs/overlay.md)."
  [kind opts]
  (if-let [arm (record-arms kind)]
    (arm opts)
    (throw (ex-info (str "unknown record backend " (pr-str kind) " — want "
                         (axis-prose (keys record-arms))
                         (when (= :overlay kind)
                           " (an :overlay half cannot itself be an overlay)"))
                    {:type :unknown-backend :mismatch :unknown-name
                     :axis :records :kind kind :records kind}))))

(def ^:private jdbc-pg-url
  ;; jdbc:postgresql://host[:port]/dbname[?params] — enough to canonicalize the two
  ;; spellings of one database against each other.
  #"(?i)jdbc:postgres(?:ql)?://([^:/?]+)(?::(\d+))?/([^?]+)(?:\?.*)?")

(defn- pg-identity
  "What two `:pg` opts agree on to be the same record store: the server, the database and the
  schema.  Canonical and not literal: a JDBC URL and the `:dbtype`/`:host`/`:dbname`
  spelling of one database key alike, and so do a stated `:port 5432` and an omitted one.
  A literal key splits one database into two index spaces, and two KBs then mint two handles
  for one sentence."
  [pg]
  (let [m       (if (string? pg) {:jdbcUrl pg} pg)
        [_ h p d] (some->> (:jdbcUrl m) (re-matches jdbc-pg-url))
        host    (str/lower-case (str (or h (:host m) "localhost")))
        port    (or (some-> (or p (:port m)) str str/trim parse-long) 5432)
        dbname  (str (or d (:dbname m)))
        schema  (some-> (:schema m) name)]
    [host port dbname schema]))

(def ^:private record-space-arms
  "Axis -> `(fn [opts] key)`: what a derived (in-RAM) index's shared state is keyed by over
  records on this axis.  A derived index is shared exactly when its records are: the `:space`
  number for RAM records, the directory for `:disk` and `:sqlite`'s file, the database for
  `:pg`.  The tag discriminates the axis, so `:sqlite` and `:disk` records in one directory
  get separate indexes."
  {:memory (fn [{:keys [space] :or {space 0}}] space)
   :disk   (fn [opts] [:disk (disk/canonical-dir (disk/disk-dir opts))])
   :sqlite (fn [opts] [:sqlite (disk/canonical-dir (disk/disk-dir opts))])
   :pg     (fn [opts] [:pg (pg-identity (:pg opts))])})

(defn- derived-index-space
  "The key a derived index's shared state is held under for records on `record-kind`,
  from that axis's `record-space-arms` arm.  Why it exists, and why the key carries the
  axis tag, is that map's docstring."
  [record-kind opts]
  (if-let [arm (record-space-arms record-kind)]
    (arm opts)
    (throw (ex-info (str "no derived-index key for record backend " (pr-str record-kind)
                         " — want " (axis-prose (keys record-space-arms)))
                    {:type :unknown-backend :mismatch :unknown-name
                     :axis :records :kind record-kind :records record-kind}))))

(def ^:private index-arms
  "The arms half of `index-axes`: axis -> `(fn [opts space] index-store)`, where `space` is a
  delay on `derived-index-space`.  `:memory`, `:dense`, `:columnar` and `:snapshot` are
  derived-only and open empty, so a KB pairing one with durable records reindexes before it
  can answer.  `:disk-log` opens populated and does not force the delay.  Whether the store
  opens populated is `index-axes`' `:durable?`, read off the selection and not the store type, which `:snapshot` and `:columnar` share."
  {:memory   (fn [_opts space] (mem/memory-index-store  {:space @space}))
   :dense    (fn [_opts space] (dense/dense-index-store {:space @space}))
   :columnar (fn [_opts space] (columnar/columnar-index-store {:space @space}))
   :snapshot (fn [_opts space] (columnar/columnar-index-store {:space @space}))
   :disk-log (fn [opts _space] (disk/index-for (disk/disk-dir opts)))})

(defn- index-store-for
  "`[index-store durable?]` for the index axis, opened by its `index-arms` arm and flagged
  from `index-axes`."
  [kind record-kind opts]
  (if-let [arm (index-arms kind)]
    [(arm opts (delay (derived-index-space record-kind opts)))
     (boolean (:durable? (index-axes kind)))]
    (throw (ex-info (str "unknown index backend " (pr-str kind) " — want "
                         (axis-prose (keys index-arms))
                         (when (= :overlay kind)
                           " (an :overlay half cannot itself be an overlay)"))
                    {:type :unknown-backend :mismatch :unknown-name
                     :axis :index :kind kind :index kind}))))

;; ---- the two halves, joined at load ---------------------------------------

(defn- declared-axes
  "The axes of `table` that name a store — every row but the `:decorator?` one, which is
  `open-kb`'s to resolve and has no arm anywhere."
  [table]
  (into #{} (comp (remove (comp :decorator? val)) (map key)) table))

(defn- refuse-table! [mismatch msg data]
  (throw (ex-info msg (merge {:type :bad-table-entry :mismatch mismatch} data))))

(defn- check-arms!
  "Every axis on `table` has an arm in `arms`, and every arm answers to an axis."
  [what table arms arms-name]
  (let [declared (declared-axes table)
        armed    (set (keys arms))]
    (doseq [k (sort (remove armed declared))]
      (refuse-table! :unarmed-axis
                     (str what " axis " k " is declared and has no arm in `" arms-name
                          "` — `open-kb` would refuse it by name at the first KB that"
                          " selected it, which is a backend that exists in the table and"
                          " nowhere else.")
                     {:axis k :arms arms-name}))
    (doseq [k (sort (remove declared armed))]
      (refuse-table! :undeclared-arm
                     (str "`" arms-name "` opens " what " axis " k ", which no row"
                          " declares — so nothing says whether it is durable, what index"
                          " may sit over it, or which adapter carries it, and every check"
                          " that reads those fields reads nil.")
                     {:axis k :arms arms-name}))))

(defn- check-backends!
  "Refuse at load a backend table that does not agree with itself, under `:bad-table-entry`
  discriminated by `:mismatch`.  Rules: every `backend-modes` row names axes something
  opens; every named pair passes the pairing checks; a reserved name points at a pairing
  that exists; an `:image?` row may persist an index; every legal pair over the core axes
  has a name (adapter axes are outside that rule).  Takes the tables as arguments so a test
  can drive it over tables that disagree, and derives its sets from them."
  [{:keys [record-axes index-axes record-arms record-space-arms index-arms
           backend-modes reserved-backend-names]}]
  (check-arms! "record" record-axes record-arms "record-arms")
  (check-arms! "record" record-axes record-space-arms "record-space-arms")
  (check-arms! "index"  index-axes  index-arms  "index-arms")
  (let [images (into #{} (comp (filter (comp :image? val)) (map key)) record-axes)
        durable-under-log-index (into #{} (comp (filter (comp :persisted-index? val)) (map key))
                                      record-axes)]
    (when-let [loose (seq (remove durable-under-log-index images))]
      (refuse-table! :image-axis
                     (str "record axes " (pr-str (vec (sort loose))) " carry `:image?` and"
                          " not `:persisted-index?` — an image is files beside the records,"
                          " so an axis that may not persist an index cannot hold one.")
                     {:axes (set loose)}))
    (doseq [[nm {:keys [records index]}] (sort-by key backend-modes)]
      (when-not (contains? record-axes records)
        (refuse-table! :unknown-axis
                       (str "backend " nm " names record axis " records
                            ", which no row declares")
                       {:backend nm :records records}))
      (when-not (contains? index-axes index)
        (refuse-table! :unknown-axis
                       (str "backend " nm " names index axis " index
                            ", which no row declares")
                       {:backend nm :index index}))
      (when-let [pairs (:pairs-with (index-axes index))]
        (when-not (and (durable-under-log-index records) (pairs records))
          (refuse-table! :illegal-pair
                         (str "backend " nm " names " records " records under the " index
                              " index, and `backend-axes` refuses that pair — a name for a"
                              " selection the pairing checks reject is sugar that cannot be"
                              " opened,"
                              " and the refusal a caller meets never mentions the name they"
                              " used.")
                         {:backend nm :records records :index index}))))
    (doseq [[nm instead] (sort-by key reserved-backend-names)]
      (when-not (contains? backend-modes instead)
        (refuse-table! :reserved-name
                       (str "reserved name " nm " sends a caller to " instead
                            ", which is not a backend — a refusal whose remedy is a second"
                            " refusal.")
                       {:backend nm :instead instead})))
    (let [core     (into #{} (comp (remove (comp #(or (:decorator? %) (:adapter %)) val))
                                   (map key))
                         record-axes)
          named    (into #{} (map (juxt :records :index)) (vals backend-modes))
          legal    (for [r (sort core)
                         i (sort (declared-axes index-axes))
                         :let [pairs (:pairs-with (index-axes i))]
                         :when (or (nil? pairs)
                                   (and (durable-under-log-index r) (pairs r)))]
                     [r i])
          unnamed  (remove named legal)]
      (when (seq unnamed)
        (refuse-table! :unnamed-pair
                       (str "these pairs over the core record axes are legal and have no"
                            " `:backend` name: " (pr-str (vec unnamed))
                            " — the two opts are for overriding a half, not for reaching a"
                            " corner the table left out, and a caller who has to spell a"
                            " pair on the axes cannot be told which pairs exist.")
                       {:pairs (vec unnamed)})))
    nil))

;; At load, as `predicates/check-facets` and `config/check-switches!` run at theirs: a
;; half-declared backend is a build failure rather than a name that refuses at the first
;; open somebody tries.
(def ^:private backend-tables
  "The seven halves `check-backends!` joins, as one value — the live tables at the load
  call below, and the thing a test varies one row of.  Named rather than passed inline
  because both readers have to be the same seven: a test assembling its own map is free
  to check a table the engine does not have."
  {:record-axes            record-axes
   :index-axes             index-axes
   :record-arms            record-arms
   :record-space-arms      record-space-arms
   :index-arms             index-arms
   :backend-modes          backend-modes
   :reserved-backend-names reserved-backend-names})

(check-backends! backend-tables)

;; ---- forks: an overlay over a frozen base ---------------------------------
;; `:overlay` decorates whatever each axis resolves to, so `open-kb` resolves it itself.  A base
;; arrives open (`:base-stores`, from `core/fork`) or as opts naming it (`:base`), which opens the
;; base's stores here and so must not be a directory this process already holds.

(defn- check-not-forked!
  "Refuse a base that is itself a fork, returning it.  `open-kb`'s axis functions catch
  the opts spelling — an `:overlay` half declared `:overlay` reaches `record-store-for`
  and throws — but `:base-stores` names no backend at all, so a live fork's stores handed
  in that way arrive as an ordinary pair.  That is the road `core/fork` takes, so
  `(fork (fork base))` is the shape this refuses (docs/overlay.md)."
  [stores]
  (if (mount/forked? stores)
    (throw (ex-info (str "a fork's base cannot itself be a fork — multi-level stacks "
                         "(base -> fork -> fork) are refused rather than half-supported.  "
                         "Fork the base this one was taken over, or keep working in the "
                         "fork you have.")
                    {:type :stacked-fork}))
    stores))

(defn- check-base-index-layout!
  "Hold a durable base index to the same key-layout sentinel `open-kb` holds its own to.

  `open-kb`'s layout check reads the *fork's* directory, so a base opened by `:base` opts
  slips past it and the fork mounts an index whose keys moved — a populated-looking count
  over queries that answer nothing.  Elsewhere the layout check repairs a stale index by
  clearing it, rebuilding it from the records and writing a new sentinel.  That repair is
  a **write to the base**, which a read-only mount may not make, so this refuses instead
  and names the one place the rebuild can happen."
  [index-kind base index-store]
  (when (= :disk-log index-kind)
    (let [root (str (disk/disk-dir base) "/index")]
      (when (and (.isDirectory (java.io.File. ^String root))
                 (= :stale (dfiles/index-layout-decision
                            root kv/index-layout-version
                            (pos? (long (reads/stored-count-at index-store []))))))
        (throw (ex-info (str "the durable index at " root " was written under another key "
                             "layout — every read whose key shape moved would miss.  A fork "
                             "mounts its base read-only and cannot rebuild it: open that "
                             "directory as a KB first, which clears and rebuilds the index, "
                             "then mount the fork over it.")
                        {:type :stale-index-layout :dir root})))))
  index-store)

(defn- written-state
  "The object `store` writes to, which every open of that store shares.  A RAM store is a
  new instance per open over its space's one state (`vaelii.impl.memory`'s registry), so
  for those this is the state; any other store is shared per store (a `:disk` directory's
  per canonical path) and is its own key."
  [store]
  (condp instance? store
    MemoryRecordStore  (:state store)
    ColumnarIndexStore (:trie store)
    KvIndexStore       (let [b (:backend store)]
                         (if (or (instance? MemoryKvBackend b) (instance? TieredKvBackend b))
                           (:state b)
                           b))
    store))

(defn- resolve-base
  "The `{:records :index}` pair a fork mounts over, frozen by the mount itself."
  [{:keys [base base-stores]}]
  (cond
    ;; only this arm needs the fork check: an `:overlay` half in the `:base` opts below
    ;; never reaches a store, since `record-store-for` refuses the name outright
    base-stores (check-not-forked! base-stores)
    base        (let [{rk :records ik :index} (backend-axes base)]
                  {:records (record-store-for rk base)
                   :index   (check-base-index-layout!
                             ik base (first (index-store-for ik rk base)))})
    :else (throw (ex-info (str "an :overlay backend needs a base — pass :base (the opts "
                               "naming it) or :base-stores (already-open stores)")
                          {:type :no-base}))))

(defn- create-tms
  "The truth-maintenance network `:tms` selects: `:dense` (default) is the
  bitmap/primitive-map representation (`vaelii.impl.dense-jtms`); `:reference` is the
  atom over one persistent map.  The two are proven to answer identically by
  `jtms_dense_oracle_test`, so the choice is resident cost, not belief: dense holds the
  network in ~3.8× less RAM at corpus scale (docs/density.md, Phase 3) at no wall cost,
  which is why the engine — built for KBs that must fit a single large node — defaults
  to it.  `:reference` stays the simpler baseline a caller can select."
  [kind]
  (case kind
    :reference (jtms/create-tms)
    :dense     (dense-jtms/create-dense-tms)
    (throw (ex-info (str "unknown TMS " (pr-str kind) " — want :reference or :dense")
                    {:type :unknown-backend :mismatch :unknown-name
                     :axis :tms :kind kind :tms kind}))))

(def opt-keys
  "Every key `open-kb` reads.  Public because it is the answer to \"is this a real
  option?\", and a caller that can ask does not have to find out from a wrong answer."
  #{:backend :records :index :space :dir :pg :tms :recover?
    :naming :base :base-stores :overlay :oplog? :reasoners})

(defn- check-constraints-opt!
  "Refuse `:constraints` with the reading that replaces it.  No `open-kb` option chooses
  whether a definitional clash is refused: the KB stores the clash, `settle` decides it,
  and `conflicts` reports one whose members are all `:monotonic` (docs/nmtms.md, \"What
  a refusal may rest on\").  The ex-data is `check-opts!`'s for an unknown key."
  [opts]
  (when (and (map? opts) (contains? opts :constraints))
    (throw (ex-info (str ":constraints is not an open-kb option: a definitional clash is"
                         " stored, decided and reported, and never refused.  Drop the"
                         " option, and read (conflicts kb) for a clash whose members are"
                         " all :monotonic")
                    {:type :unknown-option :mismatch :unknown-key :unknown [:constraints]
                     :options (vec (sort opt-keys))}))))

(defn- check-opts!
  "Refuse a key `open-kb` does not read: a misspelt `:space` leaves the KB on the default
  space in silence, and two KBs meant to be apart then share one store.  `where` names the
  map, since a fork's `:base` and `:overlay` carry opts of their own.  Goes through
  `opts/check!`, which also refuses a non-map `opts` with `:unknown-option`."
  ([opts where] (check-opts! opts opt-keys where))
  ([opts ks where]
   (opts/check! opts ks where
                (str "An option nothing reads takes the default in silence,"
                     " which for a store number means sharing a store."))))

(defn- store-space?
  "Is `space` a value `:space` names a store with?  A whole number 0 or more, or a keyword,
  a symbol or a vector (a private space: an ephemeral `fork`, a `kb-diff` side, `sync/premises`,
  a test's `gensym`).  Refused: a string (`\"3\"` and `3` share `space-3` and key separate RAM
  stores), nil, a negative or fractional number, a big integer, and a map or set (two equal
  ones can print in two orders)."
  [space]
  (or (nat-int? space) (keyword? space) (symbol? space) (vector? space)))

(defn- store-dir?
  "Is `dir` a value `:dir` names a directory with?  A string or a `java.io.File`, and not
  blank: a blank path resolves against the JVM's working directory, so the store would
  land wherever the process was started."
  [dir]
  (cond
    (string? dir)             (not (str/blank? dir))
    (instance? java.io.File dir) (not (str/blank? (.getPath ^java.io.File dir)))
    :else                     false))

(defn- base-stores?
  "Is `stores` the `{:records :index}` pair of open stores `resolve-base` mounts — a
  `RecordStore` and an `IndexStore`, as `core/fork` hands over from a live KB?"
  [stores]
  (and (map? stores)
       (satisfies? p/RecordStore (:records stores))
       (satisfies? p/IndexStore (:index stores))))

(defn- check-store-values!
  "Refuse a `:space`, `:dir` or `:base-stores` whose value names no store, returning `opts`.
  Runs after `check-opts!` and `check-mount-opts!`.  Unchecked, a value outside its domain
  opens a store other than the one it spells (a string `:space`, a blank `:dir`) or throws a
  bare `IllegalArgumentException`.  A present nil is refused, as `:naming nil` and `:pg nil`
  are.  `:unknown-option` with `:mismatch :bad-value`, `:option` and `:value`."
  [opts where]
  (doseq [[k ok? want] [[:space store-space?
                         "a whole number 0 or more (or a keyword, a symbol or a vector, for a private space)"]
                        [:dir store-dir? "a non-blank path string or a java.io.File"]
                        [:base-stores base-stores?
                         "the {:records :index} pair of open stores a live KB holds (fork passes it)"]]]
    (when (contains? opts k)
      (let [v (get opts k)]
        (when-not (ok? v)
          (throw (ex-info (str where " " k " must be " want ", got " (pr-str v))
                          {:type :unknown-option :mismatch :bad-value :option k :value v}))))))
  opts)

;; How many in-RAM KBs this process has opened on the **default** space without naming
;; it — read by `note-default-ram-space!` below.  `defonce` so a REPL reload does not
;; forget, which is the session the count exists for.
(defonce ^:private default-ram-space-opens (atom 0))

(defn- note-default-ram-space!
  "Warn the second time a KB opens on the default space without naming it.  The space
  number names the store and defaults to 0, so `(open-kb {})` twice in one process is one
  store behind two KB values with two belief graphs; a disk open naming neither `:dir` nor
  `:space` resolves to the default directory's `space-0` the same way.  A warning and never
  a refusal, since sharing a space is how `recover` and the suite's fixtures work; naming
  the number silences it."
  [opts rkind]
  (when (and (#{:memory :disk} rkind)
             (not (contains? opts :space))
             (not (contains? opts :dir))
             (= 2 (swap! default-ram-space-opens inc)))
    (trove/log! {:level :warn :id ::default-ram-space-reused
                 :msg (str "a second KB opened on the default space (:space 0) "
                           "— the number names the store, so this KB and the earlier "
                           "one are two belief graphs over one set of records, and a "
                           "write through either is invisible to the other until it is "
                           "recovered.  Give this KB its own space ({:space 2}), or "
                           "name 0 to say the sharing is meant and silence this.")
                 :data {:space 0}})))

(defn- check-mount-opts!
  "Refuse a mount or durability key nothing in this axis selection reads.  `:base` /
  `:base-stores` / `:overlay` are read when an axis is `:overlay`; `:dir` when a half is `:disk`,
  the index is `:snapshot`, or the records are `:sqlite`; on RAM stores it would name a
  directory nothing writes.  `:pg` is required for `:pg` records (no default server) and is
  refused on any other records axis.  A fork's top-level `:dir` names nothing; its writable
  half's directory is in the `:overlay` sub-map, checked on its own axes.  `where` names the
  opts map, as in `check-opts!`."
  [opts {rkind :records ikind :index} where]
  (when-not (or (= :overlay rkind) (= :overlay ikind))
    (when-let [given (seq (filterv #(contains? opts %) [:base :base-stores :overlay]))]
      (throw (ex-info (str where " was given " (str/join ", " (map pr-str given))
                           " but neither axis is :overlay, so nothing would be mounted"
                           " — the KB opens plain and every read of the base answers"
                           " empty.  A fork is spelled {:backend :overlay :base …} (or"
                           " :records :overlay :index :overlay); drop the key if no fork"
                           " was meant.")
                      {:type :unknown-option :mismatch :conflict :unknown (vec given)
                       :records rkind :index ikind}))))
  (when-not (or (= :disk rkind) (#{:disk-log :snapshot} ikind) (= :sqlite rkind))
    (when (contains? opts :dir)
      (throw (ex-info (str where " was given :dir " (pr-str (:dir opts))
                           " but no half is :disk, :snapshot or :sqlite, so nothing writes there — the"
                           " store lives in RAM and is gone at JVM exit, the opposite of what"
                           " naming a directory asks for.  Want durability?"
                           " {:backend :disk-log} (or :disk-memory / :disk-dense /"
                           " :disk-columnar / :sqlite / :pg-memory).")
                      {:type :unknown-option :mismatch :conflict :unknown [:dir]
                       :records rkind :index ikind}))))
  (if (= :pg rkind)
    (let [pg (:pg opts)]
      (when-not (or (and (map? pg) (seq pg)) (and (string? pg) (seq pg)))
        ;; A present nil, an empty map and a bare DataSource name no database or one that cannot be
        ;; identified, and `:or` does not fire on a present nil.
        (throw (ex-info (str where " needs :pg to name a database: a next.jdbc db-spec"
                             " ({:dbtype \"postgresql\" :host … :dbname …}, optionally"
                             " :schema) or a JDBC URL string, got " (pr-str pg)
                             ".  Nothing here derives a server, and an index is keyed by"
                             " which database its records are in — so a KB that took one by"
                             " default would hold its records somewhere nobody said, and one"
                             " whose database cannot be named cannot be keyed apart from"
                             " another's.")
                        {:type :unknown-option :mismatch :missing-companion :missing [:pg]
                         :records rkind :index ikind})))
      ;; The durable index is files on this host describing records on a server, and nothing in a
      ;; directory says which server, so no default directory is derived (`disk-dir` would share one
      ;; between two KBs over two databases, and the coverage check compares counts only).
      (when (and (#{:disk-log :snapshot} ikind) (not (contains? opts :dir)))
        (throw (ex-info (str where " selected " (if (= :snapshot ikind) ":pg-snapshot" ":pg-disk-log")
                             " but named no :dir.  The durable index"
                             " lives on this host and describes records on a server, so the"
                             " directory belongs to a database rather than falling out of a"
                             " space number — and a derived default is one two KBs over two"
                             " databases would share, each answering out of the other's"
                             " index.  Name the directory, or take :pg-memory, whose index"
                             " is in RAM and rebuilt on open.")
                        {:type :unknown-option :mismatch :missing-companion :missing [:dir]
                         :records rkind :index ikind}))))
    (when (contains? opts :pg)
      (throw (ex-info (str where " was given :pg but its records are " (pr-str rkind)
                           ", so nothing connects to that database — the KB opens on the"
                           " store its records axis names and every write lands there"
                           " instead.  Want Postgres records? {:backend :pg-memory :pg …}"
                           " (or :pg-disk-log or :pg-snapshot, which add a local durable index).")
                      {:type :unknown-option :mismatch :conflict :unknown [:pg]
                       :records rkind :index ikind})))))

(defn- check-naming!
  "Refuse a `:naming` setting `nm/policies` does not name, returning it.  Beside
  `check-opts!` because it is the same failure at one level down — an option read but not
  understood — and for the same reason: a KB that silently took `:strict` when it was
  told something else refuses content the caller expected to land."
  [policy]
  (if (contains? nm/policies policy)
    policy
    (throw (ex-info (str "unknown :naming policy " (pr-str policy) " — open-kb reads "
                         (str/join ", " (map pr-str (sort (keys nm/policies)))))
                    {:type :unknown-option :mismatch :bad-value :naming policy
                     :options (vec (sort (keys nm/policies)))}))))

(def recover-modes
  "What `:recover?` may say:
        :auto / true  rebuild the TMS and taxonomy at construction (over a derived index, the
                      index first); an image written under other engine source is declined
        :warn         leave them empty and log that the store holds records nothing can answer
        false         leave them empty, in silence
        :background   as :auto, but an image declined only for engine source is installed and
                      belief is rebuilt on a daemon thread; writes are refused until then
        :trust        as :auto, but such an image is installed and kept; no rebuild runs (default)"
  {:auto :auto, true :auto, :background :background, :trust :trust, :warn :warn,
   false false})

(defn- check-recover!
  "`:recover?` as one of `recover-modes`, or a refusal.  Beside `check-naming!` for the
  same reason and against a sharper failure: the dispatch tests for `:auto` and reads
  everything else as the warn branch, so an unrecognized truthy value — `:yes`,
  `:recover`, `\"auto\"` — hands back a KB whose TMS and taxonomy are empty over a store
  that is not.  Every query then answers nothing, which is the opposite of what the
  caller asked for and is a wrong answer rather than an error."
  [recover?]
  (if (contains? recover-modes recover?)
    (get recover-modes recover?)
    (throw (ex-info (str "unknown :recover? setting " (pr-str recover?)
                         " — open-kb reads :auto (or true), :background, :trust, :warn,"
                         " and false"
                         ;; `:or` does not fire on a key that is present holding nil, so
                         ;; a caller threading an optional through lands here rather than
                         ;; on the default, and the bare list of accepted values reads as if it should not
                         (when (nil? recover?)
                           (str ".  An explicit nil is not the default: omit the key"
                                " for :trust, or pass false to open in silence")))
                    {:type :unknown-option :mismatch :bad-value :recover? recover?
                     :options [:auto true :background :trust :warn false]}))))

;; ---- the operation log -----------------------------------------------------

(def oplog-modes
  "What `:oplog?` may say, and the fsync mode each one means (`vaelii.impl.oplog`): `true`
  and `:each` fsync each operation's frame before the operation runs, `:tick` leaves the
  frame to the durability daemon's tick, `false` attaches no log."
  {true :each, :each :each, :tick :tick, false nil})

(defn oplog-mode
  "The fsync mode `opts`' `:oplog?` asks for, nil for no log, or a refusal
  (`:unknown-option`): a value `oplog-modes` does not name, a log on a backend other than
  `:disk-snapshot` or `:pg-snapshot`, or a log with a `:recover?` other than `:trust` or
  `:auto`.  A log restores into a built KB or rebuilds one, so it has no reading for a KB
  left unrecovered or rebuilt in the background."
  [opts]
  (let [v (:oplog? opts false)]
    (when-not (contains? oplog-modes v)
      (throw (ex-info (str "unknown :oplog? setting " (pr-str v)
                           " — open-kb reads true (or :each), :tick, and false")
                      {:type :unknown-option :mismatch :bad-value :oplog? v
                       :options [true :each :tick false]})))
    (when-let [mode (oplog-modes v)]
      (let [{rkind :records ikind :index} (backend-axes opts)]
        (when-not (and (#{:disk :pg} rkind) (= :snapshot ikind))
          (throw (ex-info (str "open-kb was given :oplog? " (pr-str v) " over records "
                               (pr-str rkind) " and index " (pr-str ikind) " — an"
                               " operation log restores into the images a :snapshot index"
                               " keeps, so it is read on {:backend :disk-snapshot} and"
                               " {:backend :pg-snapshot} only")
                          {:type :unknown-option :mismatch :conflict :unknown [:oplog?]
                           :records rkind :index ikind})))
        (when-not (#{:trust :auto true} (:recover? opts :trust))
          (throw (ex-info (str "open-kb was given :oplog? " (pr-str v) " with :recover? "
                               (pr-str (:recover? opts)) " — an open with an operation log"
                               " restores belief or rebuilds it, so it takes :recover?"
                               " :trust or :auto")
                          {:type :unknown-option :mismatch :conflict :unknown [:oplog? :recover?]
                           :records rkind :index ikind})))
        mode))))

;; ---- the write side of an unbuilt derived state --------------------------
;;
;; No belief is an empty TMS over a full record store; no index is the derived index opening empty
;; over the same records.  A KB can hold either without the other, so they are reported separately,
;; each naming its own repair.  Both are declared where the KB came to hold what it holds (`open-kb`,
;; `note-hazards!`) and not probed for.  See docs/storage.md, "Why a write into an unrecovered KB is
;; refused".

(defn note-hazards!
  "Record which of `{:no-belief :no-index}` hold for this KB: `{:no-belief false}` from
  `core/recover`, `{:no-index false}` from `core/reindex`, whatever it finds from `open-kb`.
  A key it does not mention is left as it was.  Returns `kb`.  An importer that lands records
  and skips the recover (`:belief? false`, `:belief? :stored`) declares `{:no-belief true}`
  here, since the store is indistinguishable from one of `assert-inert` sentexes."
  [kb hazards] (swap! (:unrecovered kb) into hazards) kb)

(defn stop-rebuild!
  "Stop the belief rebuild running for `kb` (`vaelii.impl.recovery`), and return nil once
  it has stopped.  A no-op when none runs.  The rebuild files its stop function under
  `:stop-rebuild` in the `:unrecovered` atom, beside the `:stale-belief` hazard it
  raises and the `:install-pending` marker `read-copy` reads.  `write-hazards` reads only
  the boolean entries there, less `:announced?` and `:install-pending`."
  [kb]
  (when-let [stop! (:stop-rebuild @(:unrecovered kb))] (stop!))
  nil)

(defn read-copy
  "`kb`, or, while a background rebuild's install is pending (`vaelii.impl.recovery`), a
  copy of `kb` whose `:reasoning` volatile holds the `Reasoning` value `kb` holds now and is
  never reset.  The rebuild files `:install-pending` in the `:unrecovered` atom before the
  open returns, and the install retires it after replacing `kb`'s belief.
  `vaelii.core`'s public reads run against the copy, so a read that takes the network and
  then the taxonomy takes both from one belief, even when the install lands between the
  two.  Answers `kb` itself for a `kb` that is not a KB."
  [kb]
  (if-let [u (:unrecovered kb)]
    (if (:install-pending @u) (assoc kb :reasoning (volatile! (reasoning/of kb))) kb)
    kb))

(defn rebase-read-lock
  "The read side of the rebase lock of fork `kb`'s record store
  (`overlay.store/excluding-readers`), or nil for a KB that is no fork."
  ^java.util.concurrent.locks.Lock [kb]
  (when-let [^java.util.concurrent.locks.ReentrantReadWriteLock l (:rebase-lock (:records kb))]
    (.readLock l)))

(defmacro reading
  "Run `body` holding `kb`'s `rebase-read-lock`, when it has one (docs/overlay.md)."
  [kb & body]
  `(let [l# (rebase-read-lock ~kb)]
     (when l# (.lock ^java.util.concurrent.locks.Lock l#))
     (try ~@body (finally (when l# (.unlock ^java.util.concurrent.locks.Lock l#))))))

(defn write-hazards
  "What makes a write into this KB wrong, as a map of the hazards that hold:
  `{:no-belief true}`, `{:no-index true}`, both, or `{}`.  The write entry points read it
  (`core/check-writable!`); reads do not.  It reports what was declared (`open-kb` over a
  populated store, a loader through `note-hazards!`) and infers nothing.  A standing hazard
  reads as absent while the store is empty, and the read does not retire it:
  `discharge-over-empty-store!` does.  The healthy answer reads the atom and no store."
  [kb]
  ;; `:install-pending` marks a pending install for `read-copy`, and `:unsupported` is the
  ;; open's report of the records nothing supports (`recovery/note-unsupported!`); neither
  ;; is a write hazard
  (let [held (into {} (filter (comp true? val))
                   (dissoc @(:unrecovered kb) :announced? :install-pending :unsupported))]
    (cond
      (empty? held)                                   {}
      (some? (cap/some-sentex-id (:records kb)))      held
      :else                                           {})))

(defn discharge-over-empty-store!
  "Retire a standing hazard when a write entry point is about to write into an empty store,
  and answer whether one was retired.  An importer writes around the write entry points, so
  its declaration stands for the whole load; anything that emptied the store and then asserts
  builds the network as it goes.  The rule lives here because any holder of the store can call
  `p/clear-records!`.  Costs a map read on a KB with no hazard standing."
  [kb]
  ;; `:install-pending` marks a pending install for `read-copy`; it is no write hazard
  (let [held (into {} (filter (comp true? val))
                   (dissoc @(:unrecovered kb) :announced? :install-pending))]
    (boolean
     (when (and (seq held) (nil? (cap/some-sentex-id (:records kb))))
       (note-hazards! kb {:no-belief false :no-index false})
       true))))

(defn announce-once!
  "True the first time it is called for `kb`, false afterwards — so the write-side escape
  says what it is giving up once per KB rather than once per assert."
  [kb]
  (not (:announced? (first (swap-vals! (:unrecovered kb) assoc :announced? true)))))

(defn- snapshot-mode?
  "Is this KB one the mapped index image is for?  `:index :snapshot` is the whole test:
  `backend-axes` has already held it to records with a fingerprint (`image-record-axes`).  The
  platform read (`index-snapshot/enabled?`) throws instead of answering false for a backend
  this platform cannot serve."
  [_rkind ikind]
  (and (= :snapshot ikind) (snapshot/enabled?)))

(defn- register-index-snapshot!
  "Arrange for `dir`'s index image to be written when the directory closes.  Registered
  for every KB in snapshot mode, not only one that read an image: a KB that *rebuilt* its
  index is precisely the one worth snapshotting afterwards, and a freshly loaded one has
  no image to have read."
  [dir istore rstore]
  ;; the cadence clock starts here, saying there is no image yet; `map-index-snapshot!` corrects it
  ;; when one maps.
  (snapshot/note-no-image! dir)
  (disk/register-index-snapshot!
   dir (fn [] (snapshot/save! dir istore #(p/index-fingerprint rstore)))))

(defn- map-index-snapshot!
  "Try to map `dir`'s index image into `istore` instead of rebuilding it — the decision
  map (`{:index :mapped}` or `{:index :rebuild :reason r}`)."
  [dir istore rstore]
  (snapshot/load! dir istore #(p/index-fingerprint rstore)))

(defn empty-reasoning
  "The reasoning state a KB opens with, all of it empty, as one `Reasoning` value
  (`vaelii.impl.types.reasoning`): the belief network of kind `tms`, the taxonomy, and every
  atom a recover or a settle fills.  `open-kb` builds a KB holding one, and `rebuild-kb`
  builds a second KB over the same stores holding another, so a field added to `Reasoning`
  and here starts empty in both."
  [tms]
  ;; by name rather than positionally: every field is an atom, so a miscount would hand one
  ;; subsystem another's state unnoticed.
  (reasoning/map->Reasoning
   {:tms     (create-tms tms)
    :taxonomy (tax/create-taxonomy)
    :program   (atom nil)
    :violations (atom [])
    :recheck   (atom {})
    ;; `{rule-handle -> #{refusal} | :overflow}`: the firings `chain/place-conseq` declined to place
    ;; because a re-checkable block condition already held (docs/exceptions.md, "A refused firing is
    ;; remembered as bindings").  Derived state beside `jtms/blocked`, never labelled.  `:kinds` names
    ;; the handles holding a `:lift` entry (`special/kind-entries`).
    :refused   (atom {})
    :settle-stats (atom {:iterations 0 :passes 0 :histogram {}})
    :chain-stats  (atom {:runs 0 :last nil})
    ;; the read-decided families' candidates (`decide/note-candidate!`), kept at the store and removal
    ;; choke points and rebuilt by `recover`, and the inherited clashes each settle re-finds
    ;; (`inherited/install-inherited!`).  A held atom (`observe/hold-atom!`).
    :nogood-candidates (observe/held-atom {})
    ;; the arity family's length entries (`vaelii.impl.decide.arity`), a weighted LRU
    ;; the family makes on its first read
    :arity-lengths (atom nil)
    ;; The inherited clashes `discovery/preserving-nogoods` found, keyed on the stored claim with what
    ;; each was read under (`discovery/preserving-entries`), so a standing report survives an unrelated
    ;; assert.  The other side of an inherited clash is not a sentex, so the key is one handle.
    :preserved-clashes (atom {})
    ;; the mint withdrawal's two queues, described beside the `Reasoning`
    ;; record
    :mint-queues (atom {})
    ;; the inert rules the mints are justified under, described beside the
    ;; `Reasoning` record
    :mint-rules (atom {:gen 0})
    :lazy-rules (atom {:gen 0})
    ;; the datums whose supersession entry the write path's reconciles
    ;; moved since the last settle, each with its entry before the first
    ;; move, for the settle to publish (`special/take-supersession-moves!`)
    :supersessions (atom nil)
    ;; `#{pred}`: the predicates whose permuting marks moved since the last settle
    ;; (`special/note-permuting-moves!`), for `chain/reconcile-spellings!`; `[:reifiable f]` for a function
    ;; whose reifiable mark moved, for `chain/reconcile-reified!`.  Empty at rest.
    :respell   (atom #{})
    ;; `{:pending {handle #{context}} :whole #{handle} :scoped {handle #{[sub super]}} :extra [[datum
    ;; reason]] :region #{datum} :moved #{handle}}`: the handles a visibility `except` began or stopped
    ;; hiding since the last settle (`special/note-except-move!`, `special/except-move-sweeps`,
    ;; `special/except-move-region`).  Empty at rest.
    :except-moves (atom {})
    :qcn       (caches/tallied (atom {}) [:R3])
    ;; the join baselines, beside the network cache and never inside it (docs/qcn.md,
    ;; "The network is resident, and the clock is what makes that sound")
    :qcn-joined (atom {})
    :matches   (caches/tallied (atom {}) [:R1])
    ;; one shape, not a map of keyed entries: every entry in it is
    ;; retired by the same clock move, so the clock value belongs to the map
    ;; (`provers/closure-hit`)
    :closures  (caches/tallied (atom {}) [:R2])}))

(defn- forward-walk
  "`[hit seen]`: `seen` grown by the forward closure of `starts` over the justifications
  resting on them (`jtms/dependents`), and the first handle the walk met that `supports?`
  answers true for, where it stops, or nil."
  [tms supports? seen starts]
  (loop [seen (transient seen), stack (vec starts)]
    (if-let [d (peek stack)]
      (let [stack (pop stack)]
        (cond (contains? seen d) (recur seen stack)
              (supports? d)      [d (persistent! seen)]
              :else (recur (conj! seen d)
                           (into stack (comp (keep #(jtms/justification tms %)) (map :consequence))
                                 (jtms/dependents tms d)))))
      [nil (persistent! seen)])))

(defn- rests-on?
  "Does justification `j` rest on handle `d`: an antecedent, or the rule that informs it,
  which `jtms/dependents` lists it under as well."
  [j d]
  (or (some #(= d %) (:antecedents j)) (= d (:informant j))))

(defn- rests-on-seen?
  "Does a justification concluding `d` rest on a handle of `seen`: an antecedent, or the
  rule that informs it, which `jtms/dependents` lists it under as well."
  [tms seen d]
  (some (fn [jid]
          (when-let [j (jtms/justification tms jid)]
            (or (some #(contains? seen %) (:antecedents j))
                (let [inf (:informant j)] (and (integer? inf) (contains? seen inf))))))
        (jtms/supports tms d)))

(defn- reach-witness
  "`[handles jids]`: a path of the forward walk from a handle of `targets` to `hit`, with
  `handles` from the target to `hit` and `jids` the justifications between them, each
  resting on the handle before it and concluding the one after.  Searched breadth-first
  backward from `hit`, over the justifications concluding a handle (`jtms/supports`), to
  the handles of `seen` and `targets`; nil when none leads to a target."
  [tms targets seen hit]
  (let [step (fn [x on]
               (for [jid (jtms/supports tms x)
                     :let [j (jtms/justification tms jid)]
                     :when j
                     a (cons (:informant j) (:antecedents j))
                     :when (and (integer? a) (not (contains? on a))
                                (or (contains? seen a) (contains? targets a)))]
                 [a [jid x]]))
        {:keys [found tree]} (graph/bfs-tree [[hit nil]] step #(contains? targets %))]
    (when found
      (loop [x found, hs [x], js []]
        (if-let [[jid c] (tree x)] (recur c (conj hs c) (conj js jid)) [hs js])))))

(defn- witness-holds?
  "Is `[handles jids]` (`reach-witness`) a path of the forward walk from `targets` now:
  its first handle a target, each justification present, resting on the handle before it
  and concluding the one after, and its last handle one `supports?` answers true for."
  [tms supports? targets [hs js]]
  (and (contains? targets (first hs))
       (every? (fn [i]
                 (when-let [j (jtms/justification tms (nth js i))]
                   (and (= (nth hs (inc i)) (:consequence j)) (rests-on? j (nth hs i)))))
               (range (count js)))
       (boolean (supports? (peek hs)))))

(def ^:private reach-moved-cap
  "How many handles the reach memo's `:moved` may hold before `note-reach-touched!` drops
  the entry: past it the walk from the targets is the cheaper read."
  65536)

(defn- reach-entry-current?
  "Does memo entry `e` describe the network `tms` and the index `idx`, and does what it
  has not read of the touched sets lie in `:moved` and in what `jtms/touched-since`
  answers for its mark: no reset since the mark (generation `g`, the current one), or
  each since fed to it (`:fed`, `note-reach-touched!`)."
  [e tms idx g]
  (and e g
       (identical? tms (:tms e)) (identical? idx (:idx e))
       (let [eg (first (:mark e))]
         (or (= g eg) (= (:fed e) (dec (long g)))))))

(defn- reach-targets
  "The handles the entries name, as a set."
  [entries]
  (into #{} (mapcat (comp deref val)) entries))

(defn- held-forward-reach
  "The forward walk of `supporter-reaches?`, held across writes in `memo`
  (`[:taxonomy :supporter-reach]`, `note-reach-touched!`).  A walk that met no supporter is
  kept as the handles it read (`:seen`), the targets it walked from and a mark of the touched
  sets; the next read walks on from the handles touched since.  A removal only shrinks the
  closure, so `:seen` stays a superset.  A walk that met one is kept as a path (`:witness`,
  `reach-witness`) checked by `witness-holds?`.  A stored `except` or `defeat` that may have
  moved (`exc/frame-write-count`) re-reads the targets."
  [kb tms rel supports? entries memo]
  (let [idx    (:index kb)
        k      [rel (mapv key entries)]
        mark   (jtms/touch-mark-if-kept tms)
        g      (first mark)
        writes (exc/frame-write-count)
        e      (some-> memo deref (get k))
        tl     (caches/tally-of memo :T12)
        held   (fn [targets w]
                 {:tms tms :idx idx :writes writes :targets targets :witness w})
        put!   (fn [e' when-e]
                 (swap! memo (fn [m] (if (or (= ::any when-e) (identical? when-e (get m k)))
                                       (if e' (assoc m k e') (dissoc m k))
                                       m))))
        fresh  (fn []
                 (let [targets    (reach-targets entries)
                       [hit seen] (forward-walk tms supports? #{} targets)]
                   (when memo
                     (put! (cond hit  (some->> (reach-witness tms targets seen hit) (held targets))
                                 mark {:tms tms :idx idx :writes writes :targets targets
                                       :seen seen :mark mark :moved #{}})
                           ::any))
                   (some? hit)))
        same?  (and memo e (identical? tms (:tms e)) (identical? idx (:idx e)))
        targets-now (fn [] (if (= writes (:writes e)) (:targets e) (reach-targets entries)))]
    (cond
      (and same? (:witness e))
      (let [targets (targets-now)]
        (if (witness-holds? tms supports? targets (:witness e))
          (do (caches/hit tl)
              (when-not (= writes (:writes e))
                (put! (assoc e :writes writes :targets targets) e))
              true)
          (caches/recomputed tl (fresh))))

      (not (and same? (reach-entry-current? e tms idx g)))
      (caches/recomputed tl (fresh))

      :else
      (let [targets (targets-now)
            cand    (into (:moved e) (jtms/touched-since tms (:mark e)))
            step    (fn [[_ seen :as acc] d]
                      (cond (contains? seen d)
                            (if (supports? d) (reduced [d seen]) acc)
                            (rests-on-seen? tms seen d)
                            (let [[h seen] (forward-walk tms supports? seen [d])]
                              (if h (reduced [h seen]) [nil seen]))
                            :else acc))
            [hit seen] (reduce step [nil (:seen e)] cand)
            [hit seen] (if (or hit (identical? targets (:targets e)))
                         [hit seen]
                         (forward-walk tms supports? seen (remove (:targets e) targets)))]
        (if hit
          ;; `seen` holds every handle the closure from the targets reaches, so a path to
          ;; `hit` lies in it; one through a handle a removal cut off is not a path now
          (caches/recomputed tl (if-let [w (reach-witness tms targets seen hit)]
                                  (do (put! (held targets w) e) true)
                                  (fresh)))
          (do (caches/hit tl)
              (put! (assoc e :seen seen :mark mark :moved #{} :fed nil :writes writes :targets targets) e)
              false))))))

(defn note-reach-touched!
  "Fold into each entry of the reach memo (`held-forward-reach`) the handles the touched
  sets recorded since its mark, before `settle/settle-finish` empties them and outdates
  the mark, and note the generation fed.  An entry the touched sets have already
  outdated unfed, or whose handles to read grow past `reach-moved-cap`, is dropped: its
  next read walks from the targets.  A witness path reads no touched set and stays."
  [kb]
  (when-let [memo (:supporter-reach @(reasoning/taxonomy kb))]
    (when (seq @memo)
      (let [tms  (reasoning/tms kb)
            g    (first (jtms/touch-mark-if-kept tms))]
        (swap! memo
               (fn [m]
                 (reduce-kv (fn [m k e]
                              (let [eg (first (:mark e))]
                                (cond
                                  (:witness e) m
                                  (and g (identical? tms (:tms e))
                                       (or (= g eg) (= (:fed e) (dec (long g)))))
                                  (let [t (jtms/touched-since tms (:mark e))]
                                    (if (> (+ (count t) (count (:moved e))) (long reach-moved-cap))
                                      (dissoc m k)
                                      (assoc m k (assoc e :moved (into (:moved e) t) :fed g))))
                                  :else (dissoc m k))))
                            m m)))))))

(defn supporter-reaches?
  "Does a stored supporter of a relation rest on a target of the supporter entries `named`
  (`exc/supporter-entries`), the placed defeats' targets counted only with `defeats?`: the
  taxonomy's reach callback (`tax/install-supporter-visibility!`).  `sups` summarizes the
  supporters: `:rel`, `:supports?`, `:count`, `:handles`.  A stored `except` or `defeat`
  naming a supporter answers true off one count read per functor.  Otherwise the walk goes
  forward from the targets or up each supporter's support (`exc/support`), whichever side is
  smaller, stopping at the first hit.  `memo` holds the forward walk across writes
  (`held-forward-reach`)."
  ([kb named sups defeats?] (supporter-reaches? kb named sups defeats? nil))
  ([kb named sups defeats? memo]
   (let [idx     (:index kb)
         rel     (:rel sups)
         genlCx? (= :genlCx rel)
         entries (into [] (remove #(and (or genlCx? (not defeats?)) (= sx/defeat-functor (key %)))) named)]
     (cond
       (some #(pos? (reads/stored-count-named-supporters-global idx rel (key %))) entries) true
       genlCx? (exc/genlCx-excepted? kb sups)
       :else
       (let [tms       (reasoning/tms kb)
             supports? (:supports? sups)
             n         (transduce (map #(reads/stored-count-with-functor idx (key %))) + 0 entries)]
         (cond
           (zero? n) false
           (<= n (long (:count sups)))
           (held-forward-reach kb tms rel supports? entries memo)
           :else
           (let [named? (fn [h] (some #(reads/stored-naming? idx (key %) h) entries))]
             (boolean (some (fn [h] (some named? (exc/support tms h (constantly false))))
                            ((:handles sups)))))))))))

(defn- attach-visibility!
  "Install the taxonomy's visibility callbacks and its supporter-sentence read
  (`tax/install-supporter-visibility!`) and `kb`'s index store (`tax/install-index!`) on
  the `Reasoning` value `b`, which `kb` holds.  The callbacks read a copy of `kb` whose
  `:reasoning` volatile holds `b` and is never reset, so they read `b`'s network and
  stored `except`s even after an install replaces `kb`'s belief."
  [kb b]
  (tax/install-index! (:taxonomy b) (:index kb))
  (let [copy  (assoc kb :reasoning (volatile! b))
        reach (caches/tallied (atom {}) [:T12])]
    (swap! (:taxonomy b) assoc :supporter-reach reach)
    ;; Both read live under a settle's hold (`observe/live`): the closures they decide
    ;; are memoized where the writer reads them, so they describe the network the writer
    ;; holds now, and a reader beside a settle reads the taxonomy as the writer moves it.
    (tax/install-supporter-visibility! (:taxonomy b)
                                       #(observe/live (exc/supporter-entries copy))
                                       (fn [handle context]
                                         (observe/live (res/supporter-believed? copy handle context)))
                                       #(observe/live (exc/except-entries copy))
                                       (fn [handle context]
                                         (observe/live (res/supporter-believed? copy handle context false)))
                                       (fn [entries sv defeats?] (observe/live (supporter-reaches? copy entries sv defeats? reach)))
                                       (fn [handle] (some-> (p/get-sentex (:records copy) handle) sx/sentence-of)))))

;; ---- the KB before the write ------------------------------------------------------
;; While a write record is open (`observe/*write-record*`), `prior-kb` reads `kb` as it stood when the
;; record opened (docs/nmtms.md, "The published set").

(defn- prior-records
  "The record store `recs` as it stood before the writes the open write record recorded
  on it, or on the store it logs to (`:inner`): a read-only `RecordStore` answering
  `get-sentex`, `get-justification` and `get-provenance`, or `recs` itself when the record
  holds none."
  [recs]
  (if-let [rec (or (observe/kept recs) (some-> (:inner recs) observe/kept))]
    (let [at (fn [kind id read] (let [k [kind id]] (if (contains? rec k) (get rec k) (read))))
          no (fn [m] (throw (UnsupportedOperationException. (str "the records before the write take no " m))))]
      (reify p/RecordStore
        (get-sentex [_ id] (at :sentex id #(p/get-sentex recs id)))
        (get-justification [_ id] (at :justification id #(p/get-justification recs id)))
        (get-provenance [_ id] (p/get-provenance recs id))
        (put-sentex [_ _] (no 'put-sentex))
        (delete-sentex! [_ _] (no 'delete-sentex!))
        (put-justification [_ _] (no 'put-justification))
        (delete-justification! [_ _] (no 'delete-justification!))
        (next-id [_] (no 'next-id))
        (put-provenance [_ _ _] (no 'put-provenance))
        (delete-provenance! [_ _] (no 'delete-provenance!))
        (sentex-ids [_] (no 'sentex-ids))
        (justification-ids [_] (no 'justification-ids))
        (mark-premise [_ _ _] (no 'mark-premise))
        (unmark-premise! [_ _] (no 'unmark-premise!))
        (premise-ids [_] (no 'premise-ids))
        (premise-strength [_ _] (no 'premise-strength))
        (clear-records! [_] (no 'clear-records!))))
    recs))

(defn recorded-sentexes
  "The handles whose records the open write record holds a before-value of, on `kb`'s
  record store or the store it logs to: the sentexes the write stored, deleted or
  respelled.  Empty with no record open."
  [kb]
  (let [recs (:records kb)]
    (if-let [rec (or (observe/kept recs) (some-> (:inner recs) observe/kept))]
      (into #{} (keep (fn [[kind id]] (when (= :sentex kind) id))) (keys rec))
      #{})))

(defn- prior-index
  "The index store `idx` as it stood before the writes the open write record recorded on
  it.  An `IndexStore` of another type answers as it stands."
  [idx]
  (cond (instance? KvIndexStore idx)       (kv/prior-index idx)
        (instance? ColumnarIndexStore idx) (columnar/prior-index idx)
        :else                              idx))

(defn- prior-tms
  "The network `tms` as it stood before the writes the open write record recorded on it."
  [tms]
  (if (instance? DenseTms tms)
    (dense-jtms/before-network tms)
    (jtms/before-network tms)))

(defn prior-kb
  "`kb` as it stood when the open write record opened (`observe/*write-record*`): its
  records, index, network, taxonomy and nogood candidates before the writes the record
  holds, with every cache empty and the taxonomy's visibility callbacks reading the copy.
  Read-only; a caller reads it with `observe/*write-record*` unbound."
  [kb]
  (let [b     (reasoning/of kb)
        idx   (prior-index (:index kb))
        cands (:nogood-candidates b)
        b'    (assoc b
                     :tms (prior-tms (:tms b))
                     :taxonomy (tax/before-copy (:taxonomy b))
                     :nogood-candidates (observe/held-atom (or (observe/recorded cands) @cands))
                     :arity-lengths (atom nil)
                     :qcn (caches/tallied (atom {}) [:R3])
                     :qcn-joined (atom {})
                     :matches (caches/tallied (atom {}) [:R1])
                     :closures (caches/tallied (atom {}) [:R2]))
        pk    (assoc kb :records (prior-records (:records kb)) :index idx :reasoning (volatile! b'))]
    (attach-visibility! pk b')
    pk))

(def rebuild-shared
  "The KB fields a rebuild KB (`rebuild-kb`) takes from the KB it rebuilds: the two
  stores, and the configuration the stores are read under.  Every KB field other than
  `:reasoning` is in exactly one of `rebuild-shared` and `rebuild-own`, `:reasoning` holds a
  new `empty-reasoning`, and `background_rebuild_test` fails on a field in none of them."
  [:records :index :provers :reasoners :solver :naming])

(def rebuild-own
  "The KB fields a rebuild KB holds for itself.  `:dir`, `:snapshot-dir`, `:index-space`
  and `:engine-space` are nil, so a close, an image write and a space release stay the
  open KB's.  `:oplog` is nil, so the rebuild logs no operation.  `:feed` and
  `:unrecovered` are new, so no listener hears the rebuild's settles and the rebuild's
  hazards are its own."
  [:dir :snapshot-dir :index-space :oplog :feed :unrecovered :engine-space])

(defn rebuild-kb
  "A second KB over `kb`'s stores, for rebuilding `kb`'s belief beside `kb`
  (`vaelii.impl.recovery`).  It takes the `rebuild-shared` fields from `kb`, a new empty
  `empty-reasoning` under `:reasoning`, and fresh `rebuild-own` fields.  A field named in none
  of these is not copied, so a field added to the KB reaches a rebuild only once one of
  them names it.  `wrap-records`, when given, is applied to `kb`'s record store, and the
  rebuild KB reads and writes through the store it returns."
  ([kb] (rebuild-kb kb identity))
  ([kb wrap-records]
   (let [r (kb-types/map->KB (merge (select-keys kb rebuild-shared)
                                    {:records     (wrap-records (:records kb))
                                     :feed        (feed/create-feed)
                                     :unrecovered (atom {})
                                     :reasoning   (volatile! (empty-reasoning :dense))}))]
     (attach-visibility! r (reasoning/of r))
     r)))

(def ^:dynamic *background-belief?*
  "True while `open-kb` recovers a KB opened with `:recover? :background`.
  `vaelii.impl.recovery/recover` reads it: an image declined only for its engine source is
  then installed, and belief is rebuilt behind it."
  false)

(def ^:dynamic *trust-source?*
  "True while `open-kb` recovers a KB opened with `:recover? :trust`.
  `vaelii.impl.recovery/recover` reads it: an image declined only for its engine source is
  then installed and kept, with no rebuild behind it."
  false)

(defn- with-recorded-pg
  "`opts`, with `:pg` read off the directory's records identity when the records are `:pg`,
  `:dir` is given and `:pg` is not.  A `:pg-disk-log` or `:pg-snapshot` directory names the
  server, database and schema its index was built against (`index/records.edn`, written
  by the identity check in `open-kb`), so the directory alone is enough to reopen it, as a
  `:disk` directory is.  The credentials are the server's defaults: `PGUSER`, else the OS
  user, and `PGPASSWORD` when it is set.  An explicit `:pg` is used as given, and a
  directory with no records identity is left to `check-mount-opts!`, which refuses the open."
  [opts]
  (if (or (contains? opts :pg) (not (:dir opts)) (not= :pg (:records (backend-axes opts))))
    opts
    (if-let [[host port dbname schema]
             (dfiles/records-identity (str (disk/disk-dir opts) "/index"))]
      (let [env #(some-> (System/getenv %) str/trim not-empty)]
        (assoc opts :pg (cond-> {:dbtype "postgresql" :host host :port port :dbname dbname
                                 :user   (or (env "PGUSER") (System/getProperty "user.name"))}
                          schema              (assoc :schema schema)
                          (env "PGPASSWORD") (assoc :password (env "PGPASSWORD")))))
      opts)))

(defn- reasoners-at
  "The reasoner set recorded where `at` names (`reasoner-locus`), or nil when none is."
  [{:keys [dir space] :as at}]
  (cond dir (dfiles/recorded-reasoners dir)
        at  (mem/recorded-reasoners space)))

(defn- record-reasoners-at!
  "Record `names` as the reasoner set where `at` names.  A no-op for a nil `at`."
  [{:keys [dir space] :as at} names]
  (cond dir (dfiles/write-reasoners! dir names)
        at  (mem/record-reasoners! space names)))

(defn- reasoner-locus
  "Where a store records its reasoner set: `{:dir d}` for a store with a directory,
  `{:space s}` for records in RAM, which the memory registry holds for the life of the
  JVM, and nil for records on a server opened with no `:dir`, which record none."
  [{:keys [space] :or {space 0}} rkind ovr ov-opts kb-dir]
  (cond
    (= :memory rkind)                         {:space space}
    (and (= :overlay rkind) (= :memory ovr)) {:space (:space ov-opts 0)}
    kb-dir                                    {:dir kb-dir}))

(defn- base-reasoner-locus
  "`reasoner-locus` of the base a fork mounts by `:base` opts, or nil."
  [{:keys [base]}]
  (when (map? base)
    (let [{brk :records bik :index} (backend-axes base)]
      (cond
        (= :memory brk) {:space (:space base 0)}
        (or (= :disk brk) (#{:disk-log :snapshot} bik))
        {:dir (disk/canonical-dir (disk/disk-dir base))}))))

(defn- check-reasoners-opt!
  "Refuse a `:reasoners` value other than `:stored` or a collection of reasoner names."
  [v]
  (if (or (= :stored v) (and (coll? v) (not (map? v))))
    (when (coll? v) (run! provers/check-reasoner-name! v))
    (throw (ex-info (str "unknown :reasoners value " (pr-str v)
                         " — want :stored or a collection of reasoner names")
                    {:type :unknown-option :mismatch :bad-value :option :reasoners
                     :value v :known (provers/reasoner-names)}))))

(defn reasoner-mismatch
  "The `:reasoner-mismatch` refusal: `where` records the set `stored`, and the caller
  names `requested`."
  [where stored requested fix]
  (let [s (vec (sort stored)) r (vec (sort requested))]
    (ex-info (str where " records the reasoner set " (pr-str s) " and this call names "
                  (pr-str r) ".  A KB registering another set derives other beliefs from"
                  " the same records.  " fix)
             {:type :reasoner-mismatch :stored s :requested r})))

(defn- open-reasoners!
  "The reasoner names a KB opened with `opts` registers, recorded at `own` when they are
  not what `own` records.  `:reasoners :stored` takes the set `own` records, else the one
  the base records; a collection of names must equal that recorded set when there is one,
  and is refused (`:reasoner-mismatch`) when it is not.  An absent `:reasoners` names no
  reasoner."
  [opts own base]
  (let [want   (:reasoners opts [])
        own-s  (reasoners-at own)
        stored (or own-s (reasoners-at base))
        names  (if (= :stored want) (or stored #{}) (set want))]
    (when (and stored (not= stored names))
      (throw (reasoner-mismatch
              (str "the store at " (or (:dir own) (:dir base) (str "space " (pr-str (:space own)))))
              stored names
              (str "Open with :reasoners " (pr-str (vec (sort stored)))
                   ", or :reasoners :stored to take the recorded set."))))
    (when (and own (not= (or own-s #{}) names))
      (record-reasoners-at! own names))
    names))

(defn reasoners-of
  "The names of the shipped reasoners `kb` registered through `open-kb`'s `:reasoners`
  or `add-reasoner`, as a set."
  [kb]
  (or (some-> (:reasoners kb) :names deref) #{}))

(defn register-reasoners!
  "Register on `kb` the prover of each reasoner in `names` whose prover value is not
  registered yet, without recording anything.  `open-kb` and `fork` call it once recovery
  has run, which is where a caller's own `add-reasoner` call lands."
  [kb names]
  (let [want (mapv provers/reasoner names)]
    (swap! (:provers kb) (fn [have] (into have (remove (set have)) want)))
    kb))

(defn record-reasoners!
  "Replace `kb`'s recorded reasoner names with `names`, in the KB and in its store."
  [kb names]
  (let [{held :names at :at} (:reasoners kb)
        s                    (set names)]
    (reset! held s)
    (record-reasoners-at! at s)
    kb))

(defn add-reasoners!
  "Register the reasoners in `names` on `kb` and record the union in its store.  Every
  name is resolved before anything is registered, so a bad name registers none."
  [kb names]
  (run! provers/check-reasoner-name! names)
  (register-reasoners! kb names)
  (record-reasoners! kb (into (reasoners-of kb) names)))

(defn open-kb
  "Construct a KB: the implementation behind `vaelii.core/open-kb`, which owns the
  user-facing docstring.  `:backend` (`:memory` default) names a record/index pair, or
  `:records` / `:index` select the axes; `:tms` (`:dense` default, or `:reference`) selects the
  truth-maintenance representation.  `recover-fn` and `reindex-fn` (`core/reindex`: rebuild
  the index from the records, then recover) are injected because they run the engine stack
  above this namespace."
  ;; A recovering mode is the default because under `:warn` a reopened store hands back a KB whose
  ;; `isa?` answers false and whose queries answer `[]`, with one `:warn` log as the only signal.  The
  ;; default is `:trust` and not `:auto` so that a commit to belief-deriving code does not turn the next
  ;; open of every store into a full recover; rebuilding belief under a new build is a caller's decision
  ;; (`:auto`, `recover`, `lein cli upgrade`).
  [{:keys [space recover? tms naming]
    :or   {space 0 recover? :trust tms :dense naming :strict}
    :as   opts}
   recover-fn reindex-fn]
  ;; The build's switches come first: a wrong value is still reportable as a typo here (`config/check!`).
  (config/check!)
  ;; once per JVM: a chaining run refuses over a nearly full heap (docs/caches.md, "The
  ;; heap mark")
  (when (config/heap-mark?) (caches/arm-heap-mark!))
  (check-constraints-opt! opts)
  (check-opts! opts "open-kb")
  (check-naming! naming)
  (when (contains? opts :reasoners) (check-reasoners-opt! (:reasoners opts)))
  (doseq [half [:base :overlay]]
    (when-let [sub (get opts half)]
      ;; the reasoner set is the whole KB's, named at the top level
      (check-opts! sub (disj opt-keys :reasoners) (str half))
      (check-mount-opts! sub (backend-axes sub) (str half))
      (check-store-values! sub (str half))))
  ;; A fork's own writable half needs `mount/meta-kv`, which a server has not.  Refused here, before
  ;; `open-kb` builds the overlay's record store and index half, because a throw after that leaves a
  ;; connection pool registered and the directory's exclusive lock held for the life of the JVM.
  (when-let [ov (:overlay opts)]
    (when (= :pg (:records (backend-axes ov)))
      (throw (ex-info (str "a fork's own records cannot be :pg — an overlay keeps tombstones "
                           "and released premise marks beside its records, and that "
                           "bookkeeping is written for :memory and :disk.  Fork onto one of "
                           "those; a :pg KB can still be the frozen base.")
                      {:type :unknown-backend :mismatch :illegal-position
                       :axis :records :kind :pg :records :pg :half :overlay}))))
  (let [opts                          (with-recorded-pg opts)
        recover?                      (check-recover! recover?)
        {rkind :records ikind :index} (backend-axes opts)
        _                             (check-mount-opts! opts {:records rkind :index ikind}
                                                         "open-kb")
        _                             (check-store-values! opts "open-kb")
        _                             (note-default-ram-space! opts rkind)
        overlay?                      (or (= :overlay rkind) (= :overlay ikind))
        ov-opts                       (:overlay opts {})
        {ovr :records ovi :index}     (when overlay? (backend-axes ov-opts))
        ;; A fork's own half and its base resolving to one store (one `:disk` directory, one memory space)
        ;; turns base immutability off silently: `FrozenRecords` guards only calls routed through it.  Refused
        ;; on the descriptors when the base arrives as opts, before `resolve-base` opens it, and on
        ;; `written-state` when it arrives as `:base-stores`.
        _ (when (and overlay? (map? (:base opts)))
            (let [b            (:base opts)
                  {brk :records} (backend-axes b)
                  same? (cond
                          (and (= :disk brk) (= :disk ovr))
                          (= (disk/canonical-dir (disk/disk-dir b))
                             (disk/canonical-dir (disk/disk-dir ov-opts)))
                          (and (= :memory brk) (= :memory ovr))
                          (= (:space b 0) (:space ov-opts 0))
                          :else false)]
              (when same?
                (throw (ex-info (str "the fork's own half and its base name one store — "
                                     (if (= :disk brk)
                                       (str "both are :disk at "
                                            (disk/canonical-dir (disk/disk-dir b)))
                                       (str "both are :memory in space " (:space b 0)))
                                     ", and a fork cannot write its own base.  Give the"
                                     " fork's own half its own "
                                     (if (= :disk brk) ":dir" ":space") " under :overlay")
                                {:type :base-is-overlay})))))
        base       (when overlay? (resolve-base opts))
        own-rstore (when (= :overlay rkind) (record-store-for ovr ov-opts))
        own-istore (when (= :overlay ikind) (first (index-store-for ovi ovr ov-opts)))
        same-rstore? (and own-rstore
                          (identical? (written-state own-rstore) (written-state (:records base))))
        _ (when (or same-rstore?
                    (and own-istore
                         (identical? (written-state own-istore) (written-state (:index base)))))
            (throw (ex-info (str "the fork's own half and its base resolve to one store —"
                                 " the "
                                 (if same-rstore? "records" "index")
                                 " half of the fork is the store its base mounts, and a"
                                 " fork cannot write its own base.  Open that half on its"
                                 " own :dir or :space under :overlay, or pass"
                                 " :base-stores from a different KB")
                            {:type :base-is-overlay})))
        rstore  (if (= :overlay rkind)
                  (mount/mount-records own-rstore
                                       (:records base)
                                       (mount/meta-kv ovr ov-opts)
                                       own-istore
                                       ;; the opts a base refresh reopens the base from
                                       ;; (`vaelii.impl.overlay.rebase`); nil when it
                                       ;; arrived open, as another KB's stores
                                       (when-not (:base-stores opts) (:base opts)))
                  (record-store-for rkind opts))
        [istore index-durable?]
        (if (= :overlay ikind)
          ;; A fork's merged index opens populated exactly when its base's did; the trie's root count
          ;; answers in O(1).
          (let [merged (mount/mount-index own-istore (:index base))]
            [merged (pos? (long (reads/stored-count-at merged [])))])
          (index-store-for ikind rkind opts))
        snapshot? (snapshot-mode? rkind ikind)
        ;; The images carry what the record store answers, so a store that answers nothing (an adapter older
        ;; than the protocol) is refused before anything is written.  Over server records the image
        ;; directory's single-writer lock is taken here.
        _ (when snapshot?
            (when-not (satisfies? p/ImageFingerprinting rstore)
              (when (instance? java.io.Closeable rstore) (.close ^java.io.Closeable rstore))
              (throw (ex-info (str "the :snapshot index needs a record store that"
                                   " fingerprints its records for images"
                                   " (vaelii.impl.protocols/ImageFingerprinting), and the "
                                   (pr-str rkind) " store on the classpath does not — take a"
                                   " newer adapter, or :pg-disk-log")
                              {:type :missing-adapter :records rkind
                               :coordinate (:adapter (record-axes rkind))})))
            (when-not (= :disk rkind) (disk/claim-dir! (disk/disk-dir opts))))
        ;; Resolved once (a `realpath`): `close!` releases it, and on an image-index KB the write entry
        ;; point hands it to the cadence, so other backends' write path pays no resolution.
        kb-dir (cond
                 (or (= :disk rkind) (= :disk-log ikind) (= :snapshot ikind))
                 (disk/canonical-dir (disk/disk-dir opts))

                 (and (= :overlay rkind) (= :disk ovr))
                 (disk/canonical-dir (disk/disk-dir ov-opts)))
        ;; The registry key a derived (RAM) index over durable records is held under, so `close!` can
        ;; release it (`release-index-space!`).  Nil for a durable index and for all-in-RAM records.
        index-space (when (and (not (:durable? (index-axes ikind)))
                               (contains? #{:disk :sqlite :pg} rkind))
                      (derived-index-space rkind opts))
        reasoner-at    (reasoner-locus opts rkind ovr ov-opts kb-dir)
        reasoner-names (open-reasoners! opts reasoner-at
                                        (when overlay? (base-reasoner-locus opts)))
        kb (kb-types/map->KB
            (merge
             {:records rstore
              :index   istore
              ;; The directory `close!` releases, when the records are durable.  A fork's is its own writable
              ;; half's, since that directory holds the exclusive lock; the base's is mounted read-only and shared.
              ;; A durable index puts a directory here too, even over server records (`:pg-disk-log` takes its
              ;; exclusive lock on open).
              :dir     kb-dir
              ;; ...and the same directory again for a KB whose index is the mapped image; the cadence check is a
              ;; nil check on this field.
              :snapshot-dir (when snapshot? kb-dir)
              ;; the RAM derived-index registry key `close!` forgets (nil unless the
              ;; index is derived and the records durable) — `release-index-space!`
              :index-space index-space
              ;; the engine-allocated RAM space of this KB's own stores, which `close!`
              ;; drops: a fork's own half for an `:overlay` KB, else the KB's `:space`
              :engine-space (let [own (if overlay? (:space ov-opts) space)]
                              (when (mem/engine-space? own) own))
              :provers  (atom provers/default-provers)
              ;; the shipped reasoners this KB names, and where its store records them;
              ;; `open-kb` and `fork` register their provers once recovery has run
              :reasoners {:names (atom reasoner-names)
                          :at    reasoner-at}
              :solver   (atom solve/local-solver)
              :feed      (feed/create-feed)
              ;; a plain value, not an atom: the conventions the public entry point holds content to are settled
              ;; when the KB is opened
              :naming    naming
              ;; empty rather than `{:no-belief false :no-index false}`: an absent key means nobody has asked
              ;; yet.  The belief half is settled by whoever first needs it and the index half by this open
              ;; (`write-hazards`).
              :unrecovered (atom {})
              ;; the derived state, as one value: a background rebuild's install
              ;; replaces it whole (`vaelii.impl.types.reasoning`)
              :reasoning (volatile! (empty-reasoning tms))}))]
    ;; Install the observer only after the mutually-referential KB exists, and before recovery can ask
    ;; a scoped cache question.
    (attach-visibility! kb (reasoning/of kb))
    (when snapshot? (register-index-snapshot! (disk/disk-dir opts) istore rstore))
    ;; Whose records is this index of?  For `:pg` the index directory and the database are joined by
    ;; nothing but this opts map, so the directory records the database identity on first use and a later
    ;; open over a different one is refused.  The coverage check below cannot stand in: it compares
    ;; counts, which two unrelated stores can match.
    (when (and (#{:disk-log :snapshot} ikind) (not= :disk rkind))
      (let [root  (str (disk/disk-dir opts) "/index")
            ident (pg-identity (:pg opts))
            seen  (dfiles/records-identity root)]
        (cond
          (nil? seen) (dfiles/write-records-identity! root ident)
          (not= seen ident)
          (throw (ex-info (str "the durable index at " root " was built against "
                               (pr-str seen) " and this KB's records are " (pr-str ident)
                               ".  An index is derived from records, so one store's index"
                               " cannot answer another's reads.  Give this KB its own :dir,"
                               " or delete that index directory to rebuild it from these"
                               " records.")
                          {:type :stale-index-records :dir root
                           :recorded seen :records ident})))))
    ;; The durable index's key-layout sentinel is checked before anything reads the index: another
    ;; `kv/index-layout-version` replays cleanly and then misses every read.  A stale version clears the
    ;; index and rebuilds it from the records, `recover?` notwithstanding; the version is written only
    ;; after the rebuild (`dfiles/index-layout-decision`).
    (when (and (= :disk-log ikind)
               ;; The index kind, not `index-durable?`: on the `:overlay` axis that flag says the merged contents
               ;; hold something, and a fork inherits no `:dir`, so the check would clear the fork's merged index
               ;; and write a sentinel into a directory this open never read.  A base mounted under `:base` is held
               ;; to the sentinel by `check-base-index-layout!`.
               (.isDirectory (java.io.File. (str (disk/disk-dir opts) "/index"))))
      (let [root     (str (disk/disk-dir opts) "/index")
            decision (dfiles/index-layout-decision
                      root kv/index-layout-version
                      (pos? (long (reads/stored-count-at istore []))))]
        (case decision
          ;; a fresh directory needs the layout version and no rebuild; this KB owns it, so
          ;; this is where the write `index-layout-decision` refuses to make happens
          :unwritten (dfiles/write-index-layout! root kv/index-layout-version)
          :stale (do
                   (dfiles/mark-index-rebuilding! root)
                   (p/clear-index! istore)
                   (let [t0 (System/nanoTime)
                         {:keys [sentexes rules]} (reindex-fn kb)
                         ms (/ (- (System/nanoTime) t0) 1e6)]
                     (dfiles/write-index-layout! root kv/index-layout-version)
                     (trove/log! {:level :warn :id ::index-layout-rebuilt
                                  :msg (format "the durable index at %s was written under another key layout — rebuilt from %d records (%d rules) in %.0f ms"
                                               (disk/disk-dir opts) (long sentexes) (long rules) ms)})))
          nil)
        ;; The layout check answers whether the keys are right, not whether the index describes all the
        ;; records.  A short index arrives by a torn `kv.log` tail, a directory grown under a derived-index
        ;; mode (`:disk-dense` writes nothing under `<dir>/index`), or a crash between the record write and
        ;; the index batch, and answers short forever: re-asserting a fact the index cannot find mints a
        ;; second handle for it.  Coverage is exact (the root count equals the live record count, rules,
        ;; negations and exceptWhen metas included), so it is compared and repaired like a stale layout, by
        ;; rebuilding from the records.  It runs only under `recover?`: `:recover? false` asks to do no work,
        ;; and the crossing from a derived-index mode is a migration driven by an explicit `reindex`.
        (when (and recover? (not= :stale decision))
          ;; Three instruments, since the three ways a short index arrives leave different survivors.  The
          ;; batch-seal counter is the last op of every index batch, so a torn append-mode tail loses it first;
          ;; zero means the index predates the counter or arrived by `index-load` replay, and the root count
          ;; remains.  The damaged flag is the clean marker's length disagreeing with the file, which catches a
          ;; lost tail of a compacted log whose seal and counts may still agree.  Both counts are compared: a lost last record beside a kept prefix of its index batch leaves the seal and the record count agreeing and the root count one ahead.
          (let [indexed  (long (reads/stored-count-at istore []))
                sealed   (long (reads/stored-count-at istore kv/sealed-prefix))
                damaged  (:damaged (:backend istore))
                ;; the record count, not the enumeration: on a store whose enumeration is a query it is one row
                ;; against the whole table (`p/Tallying`).
                stored   (cap/count-sentexes (:records kb))]
            (when (or damaged
                      (not= indexed stored)
                      (and (pos? sealed) (not= sealed stored)))
              (dfiles/mark-index-rebuilding! root)
              (p/clear-index! istore)
              (let [t0 (System/nanoTime)
                    {:keys [sentexes rules]} (reindex-fn kb)
                    ms (/ (- (System/nanoTime) t0) 1e6)]
                (dfiles/write-index-layout! root kv/index-layout-version)
                (trove/log! {:level :warn :id ::index-coverage-rebuilt
                             :msg (format "the durable index at %s described %d of %d records%s — rebuilt from %d records (%d rules) in %.0f ms"
                                          (disk/disk-dir opts)
                                          (if (pos? sealed) sealed indexed) stored
                                          (case damaged
                                            :short-log " (and its log is shorter than its clean marker recorded)"
                                            :damaged-frame " (and a frame inside its log does not decode)"
                                            "")
                                          (long sentexes) (long rules) ms)})))))))
    ;; A durable fork's own index half is held to the same checks as a plain `:disk-log` index (layout
    ;; sentinel; coverage under `recover?`).  Both the instruments and the repair go through the merged
    ;; mount, never the own half alone: the own half is the fork's delta over the base (copy-on-write
    ;; counters, tombstones, removal records), so its counters disagree with the fork's own record count
    ;; on every fork that has written, and clearing it and reindexing the own records would drop every
    ;; removal.  The rebuild is the one `reindex` makes on any fork (`kv-clear!` on the mount sets
    ;; `::cleared`, then the merged records reindex into the own half).  See docs/overlay.md.
    (when (and own-istore (= :disk-log ovi)
               (.isDirectory (java.io.File. (str (disk/disk-dir ov-opts) "/index"))))
      (let [root     (str (disk/disk-dir ov-opts) "/index")
            decision (dfiles/index-layout-decision
                      root kv/index-layout-version
                      (pos? (long (reads/stored-count-at own-istore []))))]
        (case decision
          :unwritten (dfiles/write-index-layout! root kv/index-layout-version)
          :stale (do (dfiles/mark-index-rebuilding! root)
                     (let [{:keys [sentexes rules]} (reindex-fn kb)]
                       (dfiles/write-index-layout! root kv/index-layout-version)
                       (trove/log! {:level :warn :id ::fork-index-layout-rebuilt
                                    :msg (format "the fork's own index at %s was written under another key layout — rebuilt the merged index from %d records (%d rules)"
                                                 root (long sentexes) (long rules))})))
          nil)
        (when (and recover? (not= :stale decision))
          (let [stored   (cap/count-sentexes (:records kb))
                sealed   (long (reads/stored-count-at istore kv/sealed-prefix))
                indexed  (long (reads/stored-count-at istore []))
                damaged  (:damaged (:backend own-istore))]
            (when (or damaged
                      (not= indexed stored)
                      (and (pos? sealed) (not= sealed stored)))
              (dfiles/mark-index-rebuilding! root)
              (let [{:keys [sentexes rules]} (reindex-fn kb)]
                (dfiles/write-index-layout! root kv/index-layout-version)
                (trove/log! {:level :warn :id ::fork-index-coverage-rebuilt
                             :msg (format "the fork's merged index described %d of %d records through its own half at %s%s — rebuilt from %d records (%d rules)"
                                          (if (pos? sealed) sealed indexed) stored root
                                          (case damaged
                                            :short-log " (whose log is shorter than its clean marker recorded)"
                                            :damaged-frame " (a frame inside whose log does not decode)"
                                            "")
                                          (long sentexes) (long rules))})))))))
    (cond
      ;; A **derived** index opens empty over records that are not, so the repair is
      ;; one step longer than `recover`: rebuild the index from the records first, then
      ;; recover the TMS and taxonomy from both.  That ordering *is* `core/reindex`.
      (some? (cap/some-sentex-id (:records kb)))
      (do
        (when recover?
          (if (#{:auto :background :trust} recover?)
            (if index-durable?
              (binding [*background-belief?* (= :background recover?)
                        *trust-source?*      (= :trust recover?)]
                (recover-fn kb))
              ;; A derived index is rebuilt from the records here, unless a mapped snapshot survives and its
              ;; records fingerprint still matches (`vaelii.impl.disk.index-snapshot`), in which case its bytes are
              ;; read back.  A failed snapshot falls back to the rebuild.
              (let [snap (when snapshot?
                           (map-index-snapshot! (disk/disk-dir opts) istore rstore))]
                (if (= :mapped (:index snap))
                  (binding [*background-belief?* (= :background recover?)
                            *trust-source?*      (= :trust recover?)]
                    (recover-fn kb))
                  ;; O(records), paid on every open — the standing cost of not persisting
                  ;; the index, and the number that decides whether persisting a snapshot
                  ;; of one is worth it, so it is reported rather than absorbed silently
                  (let [t0 (System/nanoTime)
                        {:keys [sentexes rules]} (binding [*trust-source?* (= :trust recover?)]
                                                   (reindex-fn kb))
                        ms (/ (- (System/nanoTime) t0) 1e6)]
                    ;; `:warn` when the backend was named for its image: a `:disk-snapshot` KB rebuilding has paid the
                    ;; cost the operator selected that name to avoid; a `:disk-columnar` rebuild is a measurement.
                    (trove/log! {:level (if snapshot? :warn :info) :id ::reindexed-on-open
                                 :msg (format "rebuilt the derived index from %d records (%d rules) in %.0f ms%s"
                                              (long sentexes) (long rules) ms
                                              (cond
                                                ;; `snap` is read only when `snapshot?`
                                                snap
                                                (str " — the :snapshot index found no usable image ("
                                                     (name (:reason snap)) "), so this open paid the"
                                                     " rebuild the backend is named to skip")
                                                :else ""))})))))
            (trove/log! {:level :warn :id ::unrecovered-store
                         :msg (str "the record store (space " space ") already holds sentexes "
                                   "but this KB's TMS and taxonomy are empty"
                                   (when-not index-durable?
                                     ", and its index is derived state that opens empty")
                                   " — queries will silently answer nothing.  Call "
                                   (if index-durable? "(recover kb)" "(reindex kb)")
                                   ", or construct with {:recover? :auto}; {:recover? false} "
                                   "silences this.")})))
        ;; The write side is settled here and only here, from what the dispatch above left and not from
        ;; which arm it took: a mapped snapshot populates the derived index without a `reindex`, and
        ;; `:recover? :warn` recovers nothing.
        (note-hazards! kb {:no-belief (not (jtms/any-node? (reasoning/tms kb)))
                           :no-index  (zero? (long (reads/stored-count-at (:index kb) [])))})
        ;; ...and saying so, which `{:recover? false}` was silent about: the state is not read-only, since
        ;; writes into it are refused by name.  At `:info`, so `false` stays as quiet as promised at `:warn`.
        ;; `:stale-belief` is left out; its rebuild logs its own start and finish (`vaelii.impl.recovery`).
        (when-let [hz (seq (dissoc (write-hazards kb) :stale-belief))]
          (let [index? (contains? (into {} hz) :no-index)]
            (trove/log! {:level :info :id ::unrecovered-store-writes
                         :msg (str "this KB is open over a store whose "
                                   (if index? "belief and index were" "belief was")
                                   " never built, so writes into it are refused"
                                   " (:type :unrecovered-kb).  Call "
                                   (if index? "(reindex kb)" "(recover kb)")
                                   " to make it writable, or bind"
                                   " vaelii.core/*write-unrecovered?* to accept them"
                                   " unchecked and un-deduplicated.")
                         :data {:hazards (vec (sort (keys (into {} hz))))}}))))

      ;; The mirror case: a derived index holding entries for records that are gone (a directory closed,
      ;; deleted and reopened) resolves handles to no record.  It is derived, so it is dropped whatever
      ;; `recover?` says (docs/storage.md).
      (and (not index-durable?) (pos? (reads/stored-count-at (:index kb) [])))
      (do (p/clear-index! (:index kb))
          (trove/log! {:level :warn :id ::stale-derived-index
                       :msg (str "dropped a derived index left over from an earlier life of "
                                 "this record store — the records it describes are gone")})))
    kb))

(def equality-predicates
  "The relations that assert a merge, acted on in `vaelii.impl.special` and read by
  stratification (`vaelii.impl.checks`).  `different` reads the closure and is never
  stored."
  '#{rewriteOf sameAs equals})

;; ---- type queries -------------------------------------------------------

(defn- exists-in?
  "Does the ground `sentence` hold in a context visible from `context` (its genlCx
  up-closure; a variable context means any context)?"
  [kb sentence context]
  (boolean (seq (res/matches-visible kb sentence context))))

(defn find-sentexes
  "Every stored sentex that contains `term` anywhere (any position, any nesting).  An atom
  is one inverted-index read.  A compound is narrowed by the postings of its atoms and each
  candidate is verified against its own sentence.  A compound holding a variable is a pattern
  and answers nothing here; `sentexes-matching` takes a pattern."
  [kb term]
  (let [t (sx/canon term)]
    (if (and (sequential? t) (not (sx/indexable-term? t)))
      ()
      (cond->> (if (sequential? t)
                 (p/sentexes-with-terms (:index kb) (sx/probe-atoms t))
                 (reads/as-stored-with-term (:index kb) t))
        true            (map #(p/get-sentex (:records kb) %))
        true            (filter some?)
        (sequential? t) (filter #(sx/mentions? % t))))))

(defn find-sentexes-all
  "Every stored sentex that contains all of `terms`.  One intersection over every term's
  probe keys, then the same verify `find-sentexes` does, once per compound among them."
  [kb terms]
  (let [ts    (mapv sx/canon terms)
        cmpds (filterv sequential? ts)
        ks    (into [] (comp (mapcat #(if (sequential? %) (sx/probe-atoms %) [%])) (distinct)) ts)]
    (if (some #(not (sx/indexable-term? %)) cmpds)
      ()
      (cond->> (p/sentexes-with-terms (:index kb) ks)
        true        (map #(p/get-sentex (:records kb) %))
        true        (filter some?)
        (seq cmpds) (filter (fn [sx] (every? #(sx/mentions? sx %) cmpds)))))))

(defn types-of
  "The types asserted of term `x` — functors of unary sentexes (T x), found via the
  argument root.  Scoped to memberships visible from `context` (default: any context),
  under `res/type-memberships`' filters.

  `x` is any term, not only an individual: a predicate carries the meta-ontology's
  types (`binary_predicate`, `instance_relation_predicate`, …) the same way `Muffet`
  carries `dog`."
  ([kb x] (types-of kb x '?ctx))
  ([kb x context]
   (distinct (map #(nm/functor (:sentence %)) (res/type-memberships kb x context)))))

(defn memberships
  "What a term is, as the checks ask it: `{:types [t …] …}`, the types asserted of `x` and
  visible from `context`, with what `isa-among?` needs.  `isa? x t` reads up from the types
  the term holds (`genl?` walks without building the closure), the cheap direction, since
  `specs(t)` is every type for `t` = `thing`.  Memoized per `memberships` read, which
  `membership-reader` memoizes per term."
  [kb x context]
  {:types (vec (types-of kb x context)) :tax (reasoning/taxonomy kb) :context context
   :isa (volatile! {})})

(defn isa-among?
  "Is `t` a supertype of one of the types a `memberships` read `ms` holds — by `genl?` from
  its context, reflexively?  Memoized in `ms`."
  [{:keys [types tax context isa]} t]
  (let [m @isa]
    (if (contains? m t)
      (get m t)
      (let [a (boolean (some #(tax/genl? tax % t context) types))]
        (vswap! isa assoc t a)
        a))))

(defn- membership-arity
  "The arity the first exact-arity class a `memberships` read `ms` is under says, or nil."
  [ms]
  (first (for [[t n] tax/exact-arity-classes :when (isa-among? ms t)] n)))

(defn relation-arity
  "The exact length that binds `pred`, its own or one it inherits through `genl`, or nil:
  `arity/relation-length`'s `:exact`, read the same at every context (docs/taxonomy.md,
  \"Arity\").  The integrity pass reads it."
  [kb pred]
  (:exact (arity/relation-length kb pred)))

(defn relation?
  "Is `term` a relation of two or more places by its stored content, visible from
  `context` (nil: every believed declaration): a declared arity of two or more, or a
  `variable_arity` membership, or, where neither answers, a length of two or more it
  inherits through `genl` (`arity/relation-length`, read the same at every context).  A
  `genl` edge between two relations makes each a node of the `genl` hierarchy; such a
  node is not a type, and a node with an arity of one or none is.  No spelling is read.
  The believed reading of an arity (docs/taxonomy.md, \"Arity\")."
  [kb term context]
  (let [n (tax/declared-arity (reasoning/taxonomy kb) term context)]
    (if (and (integer? n) (pos? n))
      (>= n 2)
      (let [ms (memberships kb term (or context '?ctx))]
        (boolean (or (some-> (membership-arity ms) (>= 2))
                     (isa-among? ms 'variable_arity)
                     (let [{l :exact via :via} (arity/relation-length kb term)]
                       (and l (>= l 2) (not= via term)))))))))

(defn isa?
  "Is individual `x` (transitively) of type `t`?  Considers only type memberships visible
  from `context` (default: any).  Reads `x`'s own memberships and climbs from each (see
  `memberships`).  A non-symbol `x` falls back to the matcher.  Lazy in the memberships;
  `memberships` is the batch form."
  ([kb x t] (isa? kb x t '?ctx))
  ([kb x t context]
   (if (and (symbol? x) (not (sx/variable? x)))
     (let [tax (reasoning/taxonomy kb)]
       (boolean (some #(tax/genl? tax % t context) (types-of kb x context))))
     (exists-in? kb (list t x) context))))

(defn reach-strength
  "The defeat class of the **strongest** route `sub →* super` in `rel-key` (`:genl` for the
  type/predicate hierarchy, `:genlCx` for contexts) that `context` sees — `:monotonic` /
  `:default`, or nil when unreachable.  `nil` context is the unscoped read.

  The diagnostic half of the widest-bottleneck rule: it reports the strength a subsuming
  firing's conclusion now rests on, so a KB with a defeasible taxonomy edge and an alternate
  route can ask how strongly one term subsumes another.  Reads the live JTMS defeat-class of
  each edge supporter (docs/taxonomy.md, \"Strength of a subsumption path\")."
  ([kb rel-key sub super] (reach-strength kb rel-key sub super nil))
  ([kb rel-key sub super context]
   (tax/reach-strength (reasoning/taxonomy kb) rel-key sub super context
                       #(jtms/defeat-class (reasoning/tms kb) %))))

(defn membership-reader
  "A `term -> memberships` reader, memoized for the life of one caller.  The definitional
  checks ask about each of a few terms several times, and each ask is a posting read, a record
  fetch and a belief test per entry that cannot change under one `assert`."
  [kb context]
  (let [cache (volatile! {})]
    (fn [term]
      (if-some [m (get @cache term)]
        m
        (let [m (memberships kb term context)]
          (vswap! cache assoc term m)
          m)))))

(defn disjoint?
  "Are types `a` and `b` provably disjoint (via disjoint declarations, closed
  under genl) — anywhere, or (with `context`) using only the declarations and
  genl edges visible from it?

  The 3-arity is the KB-wide reading `vaelii.core/disjoint?` documents."
  ([kb a b] (tax/disjoint? (reasoning/taxonomy kb) a b))
  ([kb a b context] (tax/disjoint? (reasoning/taxonomy kb) a b context)))

;; ---- storage helpers ----------------------------------------------------

(defn handle-cache-key
  "What a cached handle lookup is valid under: which KB it was asked of, and the set of
  predicates declared `symmetric`, the one thing `resolution/kb-sentex` reads off the KB.
  The record store rides in the key because `with-handle-cache` reuses an outer run's map,
  so a nested run on a second KB would read the first's handles.  The set is read unscoped."
  [kb]
  [(:records kb) (tax/props (reasoning/taxonomy kb) :symmetric)])

;; A forward-chain run binds the handle cache over its whole fixpoint (`chain/chain-all`).  For a
;; functor the store held no sentex under when the run began, a cache miss is proof of absence and
;; skips the trie walk.  The verdict is recorded per functor at its first probe, dropped when the
;; cache generation steps, armed only for a bulk frontier (`chain-authority-min-frontier`), and keyed
;; on the store's root key `(sx/body built)`, not the sentence head.  Bound only by `chain`; nil
;; elsewhere.  See docs/inference.md, "A cache miss as proof of absence".
(def ^:dynamic *chain-authoritative-functors* nil)

(def chain-authority-min-frontier
  "The smallest seed frontier a `chain` run arms the authority memo above for.  Coarse,
  not tuned: it separates an incremental `assert` (a seed of one, plus a few migration
  seeds) from a bulk fixpoint (a `forward-chain`'s whole datum set, a load, a broad edge's
  subsumption seeds), and the memo's benefit is flat across the wide band between them —
  above the floor one probe per functor is repaid by the walks it skips, below it there
  are too few conclusions to repay a probe at all.  Placed here beside the memo var it
  arms, so the mechanism and the policy that arms it read together."
  64)

(def ^:private memo-generation-key
  "Where the authority memo records the handle-cache generation its verdicts were
  decided under — a keyword, so it cannot collide with a functor symbol."
  ::generation)

(defn- functor-cache-authoritative?
  "Is the run's handle cache authoritative for the sentex `built`: did the store hold zero
  sentexes under its root functor when the run first asked?  The functor is the store's root
  key (`(first (sx/body built))`, `kv/root-keys`).  Memoized in `*chain-authoritative-functors*`
  per handle-cache generation under `cache-key`.  A nil var, or a `built` with no extent
  posting (a rule), answers falsey.  See docs/inference.md, A cache miss as proof of absence."
  [kb cache-key built]
  (when-let [^java.util.Map memo *chain-authoritative-functors*]
    (when-let [gen (observe/cache-generation cache-key)]
      (when-not (= gen (.get memo memo-generation-key))
        (.clear memo)
        (.put memo memo-generation-key gen))
      (let [b (sx/body built)]
        (when (and (sequential? b) (seq b) (symbol? (first b)))
          (let [functor (first b)
                cached  (.get memo functor)]
            (if (some? cached)
              cached
              (let [auth (zero? (long (p/count-with-functor (:index kb) functor)))]
                (.put memo functor auth)
                auth))))))))

(defn- stored-at
  "Which of the sentexes at `built`'s own trie leaf stores exactly it, or nil.  Reads
  `p/leaf-at` and not `p/lookup`, since a variable is a wildcard to `lookup` and would read
  every record of the shape.  A ground sentence keys the trie exactly, so the first candidate
  is the answer with no record read.  A sentence with variables alpha-renames, so the stored
  sentence decides, one record read per sentex at the leaf.  A rule's key is its canonical
  form, so the trie answers it exactly."
  [kb built handles]
  (if (or (some? (:antecedent built)) (sx/ground? built))
    (first handles)
    (let [sentence (:sentence built)]
      (some (fn [h]
              (when (= sentence (:sentence (p/get-sentex (:records kb) h))) h))
            handles))))

(defn find-sentex-handle
  "The handle of an existing sentex for `sentence` in `context`, or nil.  A sentence with
  variables is found by its stored sentence (`stored-at`), since the key alpha-renames.  Every
  probe is `p/leaf-at`, the exact leaf.  One probe answers a symmetric literal: the sort is
  order-blind, and the `(symmetric P)` mark migrates earlier rows
  (`integrate/commute-existing`), so the store holds the spelling this probe builds."
  [kb sentence context]
  ;; a spelling one reader reads (`res/*spelled-by*`) is looked up past the cache, which
  ;; holds the store's own spelling of a sentence
  (let [cache-key (when-not res/*spelled-by* (handle-cache-key kb))]
    (or (when cache-key (observe/cached-handle cache-key sentence context))
        (let [built  (res/kb-sentex kb sentence context)]
          ;; The run cache said "no", and for a chain-authoritative functor that is final.  Guarded on the
          ;; queried spelling being the canonical one: if canonicalization moved it, the cache was consulted
          ;; under a different key than the store holds.
          (if (and cache-key (= sentence (sx/sentence-of built))
                   (functor-cache-authoritative? kb cache-key built))
            nil
            (let [direct (stored-at kb built (reads/as-stored-leaf (:index kb) (sx/path built)))]
              (when direct
                ;; The cache says this sentence is stored at this handle until the sentex is removed.  Filled only
                ;; when the spelling survives canonicalization: the removal choke point clears the canonical key
                ;; (`integrate/sentex-removed!`), so an entry under a rewritten spelling would outlive its sentex.
                (if (and cache-key (= sentence (sx/sentence-of built)))
                  (observe/cache-handle! cache-key sentence context direct)
                  direct))))))))

;; ---- the body under a negation --------------------------------------------

(defn body-under-not
  "A fact's body with a single leading `not` stripped — the form both polarities key
  on (`(not (flies Opus))` and `(flies Opus)` share the body `(flies Opus)`).  Double
  negation is eliminated at store time, so one strip suffices; a non-fact sentence (a
  rule, a metadata declaration) is returned unchanged and simply never opposes."
  [sentence]
  (if (and (sequential? sentence) (= 'not (first sentence)) (= 2 (count sentence)))
    (second sentence)
    sentence))

;; ---- the excepts and defeats ---------------------------------------------
;; `reads/as-stored-naming` reads which `(except (sentexHandle H))` or `(defeat (sentexHandle H))`
;; names which handle, in which context; `jtms/in?` on its own handle is the reader's filter.

(defn except-target
  "The handle a visibility `(except (sentexHandle H))` sentence hides, or nil for any
  other sentence — including `(not (except …))`, whose functor is `not`.

  A **meta-exception** — `(except (sentexHandle E))` where E is itself an `(except …)` —
  cascades: hiding an except suppresses its effect, restoring visibility of the target
  the inner except was hiding.  The cascade is evaluated at read time by
  `exc/excepted-handles`, which checks whether each except-handle is itself
  hidden before counting it as active."
  [sentence]
  (when (and (sequential? sentence)
             (= sx/except-functor (first sentence))
             (= 2 (count sentence)))
    (sx/handle-id (second sentence))))

(defn defeat-target
  "The handle a `(defeat (sentexHandle H))` sentence removes from belief, or nil for any
  other sentence.  The shape test of `except-target`, on the `defeat` functor."
  [sentence]
  (when (and (sequential? sentence)
             (= sx/defeat-functor (first sentence))
             (= 2 (count sentence)))
    (sx/handle-id (second sentence))))

(defn placed-targets
  "The handles the placed sentence `s` moves with no relabel: a `defeat`'s target, and,
  while an except is stored, the members of a `(contradicts …)`, one of which a reader
  whose excepts lower its class reads as defeated (`exc/conflicts-naming`)."
  [kb s]
  (if-let [t (defeat-target s)]
    [t]
    (when (and (seq? s) (= 'contradicts (first s)) (reads/stores-any? (:index kb) sx/except-functor))
      (keep sx/handle-id (rest s)))))

(defn- defeat-walk
  "Walk forward from `seeds` over the justifications resting on each handle met, and from
  each placed sentex met (a handle with a `nogood` or `guard` justification) to the
  handles it moves (`placed-targets`): a defeat resting on a moved handle can move in
  force, which moves its target with no relabel, and a cycle of defeats is walked once
  (docs/nmtms.md, \"A defeat-dependency cycle\").  Answers the first handle `hit?` holds
  of, or with `hit?` nil the set walked.  Stores nothing."
  [kb seeds hit?]
  (let [recs    (:records kb)
        tms     (reasoning/tms kb)
        placed? (fn [d] (some #(contains? #{exc/nogood-informant exc/guard-informant}
                                          (:informant (jtms/justification tms %)))
                              (jtms/supports tms d)))]
    (loop [seen #{}, stack (vec seeds)]
      (if-let [d (peek stack)]
        (let [stack (pop stack)]
          (cond (contains? seen d)  (recur seen stack)
                (and hit? (hit? d)) d
                :else
                (recur (conj seen d)
                       (cond-> (into stack (comp (keep #(jtms/justification tms %)) (map :consequence))
                                     (jtms/dependents tms d))
                         (placed? d)
                         (into (some->> (p/get-sentex recs d) :sentence (placed-targets kb)))))))
        (when-not hit? seen)))))

(defn defeat-reach
  "The handles the placed sentexes `stored` move (`placed-targets`) and those of `removed`
  (`[target …]` pairs), and every handle walked forward from them (`defeat-walk`): the
  handles whose belief those moves can change with no relabel."
  [kb stored removed]
  (let [recs  (:records kb)
        seeds (-> (into #{} (mapcat #(some->> (p/get-sentex recs %) :sentence (placed-targets kb))) stored)
                  (into (map first) removed))]
    (defeat-walk kb seeds nil)))

(defn moved-reach
  "The handles `seeds` and every handle walked forward from them (`defeat-walk`): the
  handles whose belief a write naming `seeds` can change with no relabel."
  [kb seeds]
  (defeat-walk kb seeds nil))

;; ---- creating, respelling and keying sentexes ----------------------------

(def ^:dynamic *defer-index-refresh?*
  "True while `vaelii.impl.recovery` runs a recover from the records on the calling thread.
  `refresh-index-image!` then writes nothing, so a settle does not wait on an image write
  that its own later writes make stale.  `recover` calls `refresh-index-image!` once after the recover."
  false)

(defn refresh-index-image!
  "Offer `kb`'s index image the mid-life refresh (`disk/maybe-refresh-index-snapshot!`),
  from the writer's thread.  A no-op for a KB with no image (`:snapshot-dir` nil) and while
  `*defer-index-refresh?*` is true.  The root count is a profiled index read, so it is read
  only for a KB that has an image."
  [kb]
  (when-let [d (:snapshot-dir kb)]
    (when-not *defer-index-refresh?*
      (disk/maybe-refresh-index-snapshot! d (reads/stored-count-at (:index kb) [])))))

;; ---- the table of the inert rules the argument-type mints are justified under

(defn mint-rule-table
  "`{kind handle}`: the handles `kb` stores the rules of `kv/mint-rules` at, read off the
  index's `[:mint-rules]` family (`reads/as-stored-mint-rules`) and held in the
  `:mint-rules` atom until `forget-mint-rules!` moves its generation.  The fill installs
  with a compare-and-set against the generation it read, so a rule stored or removed
  during the fill makes it read the family again."
  [kb]
  (let [a (reasoning/mint-rules kb)]
    (loop []
      (let [held @a]
        (or (:table held)
            (let [t (into {} (reads/as-stored-mint-rules (:index kb)))]
              (if (compare-and-set! a held (assoc held :table t)) t (recur))))))))

(defn records-mint-kind
  "`mint-kind` read off the record store `records` alone, for a reader with no table to
  ask (`reindex`): one record fetch per rule handle `informant`."
  [records informant]
  (if (integer? informant)
    (kv/mint-rule-kind (p/get-sentex records informant))
    (when (contains? kv/mint-rules informant) informant)))

(defn mint-kind
  "The declaring kind a justification with `informant` mints under, or nil: the kind whose
  rule handle `informant` is in `mint-rule-table`, or the kind `informant` names when it is
  a key of `kv/mint-rules` itself."
  [kb informant]
  (if (integer? informant)
    (some (fn [[k h]] (when (= h informant) k)) (mint-rule-table kb))
    (when (contains? kv/mint-rules informant) informant)))

(defn mint-informant?
  "Is `informant` one an argument declaration's mint is justified under (`mint-kind`)?"
  [kb informant]
  (some? (mint-kind kb informant)))

(defn forget-mint-rules!
  "Drop `kb`'s `mint-rule-table` and move its generation, so the next read fills it off
  the index: at the store or removal of a rule of `kv/mint-rules`, and at a write of the
  stores that bypasses `create-sentex` (`reindex`, an import's record phase).  With
  `empty?`, the table holds no rule instead, which a wipe of the stores leaves true
  (`core/clear!`)."
  ([kb] (forget-mint-rules! kb false))
  ([kb empty?]
   (some-> (reasoning/mint-rules kb)
           (swap! (fn [m] (cond-> {:gen (inc (long (:gen m 0)))} empty? (assoc :table {})))))))

(defn note-mint-rule-moved!
  "`forget-mint-rules!` when sentex `s`, stored or leaving, is a rule of `kv/mint-rules`,
  after the index write that posts or retires it.  Every sentex that is not an inert rule
  costs two field reads."
  [kb s]
  (when (kv/mint-rule-kind s) (forget-mint-rules! kb)))

(defn stores-lazy-rule?
  "Does `kb`'s store hold a rule whose `:engines` take `:lazy`?  The rule extent's `[:lazy]`
  count over every context, as `chain/lazy-table` reads it, read once and held in the
  `:lazy-rules` atom until `forget-lazy-rules!` moves its generation; a fill installs only
  over the generation it read."
  [kb]
  (let [a (reasoning/lazy-rules kb)]
    (loop []
      (let [held @a]
        (if (contains? held :any?)
          (:any? held)
          (let [any? (pos? (reads/stored-rule-count-global (:index kb) :lazy))]
            (if (compare-and-set! a held (assoc held :any? any?)) any? (recur))))))))

(defn forget-lazy-rules!
  "Drop `stores-lazy-rule?`'s answer and move its generation: at the store or removal of a
  rule taking `:lazy`, at an engines join adding it, and at a write of the stores that
  bypasses `create-sentex` (`reindex`, an import's record phase).  With `empty?`, the answer
  is false instead, which a wipe of the stores leaves true (`core/clear!`)."
  ([kb] (forget-lazy-rules! kb false))
  ([kb empty?]
   (some-> (reasoning/lazy-rules kb)
           (swap! (fn [m] (cond-> {:gen (inc (long (:gen m 0)))} empty? (assoc :any? false)))))))

(defn note-lazy-rule-moved!
  "`forget-lazy-rules!` when sentex `s`, stored or leaving, is a rule taking `:lazy`."
  [kb s]
  (when (contains? (:engines s) :lazy) (forget-lazy-rules! kb)))

(defn create-sentex
  "Store `sentence` in `context` as a new sentex, index it, and return `[handle sentex]`.
  `strength` (optional) is the strength the record is born with, so a caller asserting a
  premise avoids a second record frame from `mark-premise`.  An index write that throws takes
  the record with it: the postings that landed are taken out and the record is deleted
  before the throw travels, since the next open's coverage check would otherwise index it and
  believe it as a premise whose forward rules never ran.  A failed unindex or delete is added as suppressed; the next
  open's coverage check repairs the pair."
  ([kb sentence context] (create-sentex kb sentence context nil))
  ([kb sentence context strength]
   (let [s (cond-> (res/kb-sentex kb sentence context)
             strength (assoc :strength strength))
         h (p/put-sentex (:records kb) s)
         s (assoc s :id h)]
     (try
       (p/index-sentex (:index kb) s h)
       (catch Throwable t
         ;; the index write may have landed some of its postings before it threw, and a
         ;; posting left naming `h` is found by the dedup probe and by `handle-of` after
         ;; the record is gone
         (try (p/unindex-sentex! (:index kb) s h)
              (catch Throwable t2 (.addSuppressed t t2)))
         (try (p/delete-sentex! (:records kb) h)
              (catch Throwable t2 (.addSuppressed t t2)))
         (throw t)))
     ;; the index image's cadence, on the one thread allowed to write this index
     ;; (`disk/maybe-refresh-index-snapshot!`).  `:snapshot-dir` is non-nil only on a KB that has an
     ;; image, so every other backend pays one field read.
     (refresh-index-image! kb)
     ;; the add-side boundary for an incremental matcher's alpha memories — a no-op
     ;; unless one is engaged (docs/inference.md, "Incremental rule matching")
     (observe/notify-add kb s h)
     ;; and the coarse clock a *derived, resident* structure records itself under: this
     ;; is one of the two points the stored content moves at, the other being
     ;; `integrate/sentex-removed!`
     (observe/note-change)
     (exc/note-stored! kb s true)
     ;; a run with the handle cache engaged learns the handle here, keyed on the canonical sentence;
     ;; another spelling misses and fills its own key off the index
     (observe/cache-handle! (handle-cache-key kb) (sx/sentence-of s) (:context s) h)
     ;; the candidates of the nogood families the settle places
     (decide/note-candidate! kb s true)
     (note-mint-rule-moved! kb s)
     (note-lazy-rule-moved! kb s)
     [h s])))

(defn canonical-sentence
  "`sentence` as this KB would **store** it in `context` — the entry point's own canonicalizer,
  asked without storing or looking anything up.  Equal to `sentence` for the sentence a
  caller just wrote through the entry point, and different for one the store already holds under
  a spelling the taxonomy has since stopped canonicalizing to: a `(symmetric P)` mark
  arriving after `(P b a)` was stored is the case, and telling the two apart is what
  `integrate/commute-existing` sweeps on."
  [kb sentence context]
  (sx/sentence-of (res/kb-sentex kb sentence context)))

(defn respell-sentex!
  "Store the sentex at `sx`'s handle under `sentence` instead: the same handle, TMS node,
  premise mark and justifications, one different stored spelling.  Returns the restored record.
  Everything keyed on the sentence (trie path, alpha memories, handle cache, `except` set) is
  dropped under the old spelling and rebuilt under the new; the caller owes the cache-effect
  walk (`special/disintegrate-sentex!`, then `special/integrate-sentex`).  For a
  re-canonicalization only (`integrate/commute-existing`, `chain/reconcile-reified!`), never a
  change of what the sentex says.  The sentence goes back through `res/kb-sentex`; a rule keeps
  its `:engines`, `:defeasible` and `:effect`."
  [kb sx sentence]
  (let [h   (:id sx)
        idx (:index kb)
        s'  (assoc (merge (res/kb-sentex kb sentence (:context sx))
                          (when (some? (:antecedent sx))
                            (select-keys sx [:engines :defeasible :effect])))
                   :id h :strength (:strength sx))]
    ;; the old spelling out — `integrate/sentex-removed!`'s store-side half, minus the
    ;; record delete and the re-check the caller's integrate half posts for the new one
    (p/unindex-sentex! idx sx h)
    (observe/notify-remove kb sx)
    (observe/forget-handle! (sx/sentence-of sx) (:context sx))
    (decide/note-candidate! kb sx false)
    ;; ...and the new spelling in — `create-sentex`'s half, with the handle it already has
    (p/put-sentex (:records kb) s')
    (p/index-sentex idx s' h)
    (refresh-index-image! kb)
    (observe/notify-add kb s' h)
    (observe/note-change)
    (exc/note-stored! kb sx false)
    (exc/note-stored! kb s' true)
    (observe/cache-handle! (handle-cache-key kb) (sx/sentence-of s') (:context s') h)
    (decide/note-candidate! kb s' true)
    (negation/note-respelled! kb s')
    s'))

(defn find-or-create-sentex
  "The existing sentex for `sentence` in `context`, or a new one — `[handle sentex new?]`.
  `strength` is passed through to `create-sentex` and so applies only to a *new* record;
  an existing one keeps what it has until `mark-premise` says otherwise."
  ([kb sentence context] (find-or-create-sentex kb sentence context nil))
  ([kb sentence context strength]
   (let [h (find-sentex-handle kb sentence context)
         s (when h (p/get-sentex (:records kb) h))]
     (cond
       s [h s false]
       h (do (trove/log! {:level :warn :id ::record-less-posting-dropped
                          :data {:handle h :context context}
                          :msg (str "index posting " h " names no record; the sentence is stored anew (run reindex to verify the index)")})
             (try (p/unindex-sentex! (:index kb) (assoc (res/kb-sentex kb sentence context) :id h) h)
                  (catch Throwable _ nil))
             (let [[h s] (create-sentex kb sentence context strength)] [h s true]))
       :else (let [[h s] (create-sentex kb sentence context strength)] [h s true])))))

(defn antecedent-order
  "`handles` as a justification's stored antecedent vector, ordered by what each antecedent
  says (its sentence, then its context), never by the handle.  A handle is assertion order, so
  an arrival-ordered vector would leak arrival into `core/why`, `why-not`, `preview` and the
  sort key of `core/supporting-justifications`.  The informant is not in the vector; belief
  reads the antecedents as a set.  Short-circuited below two.  Call it where something is
  stored (the justification writers and the refusal ledger), never where something is only
  decided: move a call later, never earlier."
  [kb handles]
  ;; The key is structural (the antecedent's sentence, then its context), compared by
  ;; `nm/compare-form` in place: no String per handle, and no ambient `*print-length*` can collapse the
  ;; key back onto arrival order.  Built once per antecedent; a run of one is left as it came.
  (let [recs (:records kb)]
    (nm/sort-by-content-key (fn [h] (let [s (p/get-sentex recs h)] [(sx/sentence-of s) (:context s)]))
                            handles)))

(defn justification-content-key
  "The key every listing of justifications sorts on: the informant's content (a rule's
  sentence and context, or the symbol), its antecedents' sentences, the firing's bindings, and
  the concluded sentence and context.  Returns the key fn.  Shared by
  `core/supporting-justifications`, `core/dependent-justifications` and a clash report's
  `:justifications`, which must not drift.  The informant enters as content and never as its
  handle.  The consequence is in the key for `dependent-justifications`.  Compare with
  `nm/compare-form`, never `compare`."
  [kb]
  (let [recs (:records kb)
        ;; with the context, because `antecedent-order` sorts on it: a coarser key leaves one firing placed
        ;; into two contexts tied, and the tie falls back to `jtms/supports`' id order (arrival order).
        ;; `core/preview` reads `(first (supporting-justifications …))`.
        sent (fn [x] (when-let [s (some->> x (p/get-sentex recs))]
                       [(sx/sentence-of s) (:context s)]))]
    (fn [j]
      (let [inf (:informant j)
            isx (when (integer? inf) (p/get-sentex recs inf))
            c   (some->> (:consequence j) (p/get-sentex recs))]
        ;; A structural key, compared by `nm/compare-form` and never printed, for the reasons in
        ;; `antecedent-order`.  A key that must print goes through `nm/print-key`.
        [(if (integer? inf) (sx/sentence-of isx) inf) (:context isx)
         (mapv sent (:antecedents j))
         ;; sorted, because a small binding map is a `PersistentArrayMap` and iterates in insertion order,
         ;; which is the trigger order; one rule reached through two antecedents would otherwise give unequal
         ;; keys.  A vector of pairs, which `nm/compare-form` walks.
         (when-let [b (:bindings j)] (mapv (fn [[k v]] [k v]) (into (sorted-map) b)))
         (sx/sentence-of c) (:context c)]))))

;; ---- the equality closure: reading and rewriting -------------------------
;; The closure is `vaelii.impl.taxonomy`'s and the migration and supersession machinery is
;; `vaelii.impl.special`'s.  This half reads which terms an equality sentence merges and restates a
;; sentence or goal under the class representatives, because `sentexes-matching` needs it.

(defn equality-sentence?
  [sentence] (contains? equality-predicates (nm/functor sentence)))

(defn preferred-term
  "The term this equality sentence puts on top, or nil.  `rewriteOf` deprecates its
  second argument in favour of its first; `sameAs` and `equals` deprecate neither."
  [[f a _]] (when (= f 'rewriteOf) a))

(defn rewrite-term*
  "`term` (a sentence or a term) in its equality **normal form** (`res/normal-form`),
  given a built supporter predicate `visible?`, nil for the unscoped read.  A caller
  normalizing many sentences under one reader builds `visible?` once, since deciding
  visibility costs a record fetch per equality supporter (`special/supersession-map`)."
  ([kb term visible?] (res/normal-form kb term visible?)))

(defn rewrite-term
  "`rewrite-term*` for a caller holding a context: only the merges and schematic
  equations `context` sees apply.  The two-arity is the unscoped read."
  ([kb term] (rewrite-term* kb term nil))
  ([kb term context] (rewrite-term* kb term (res/visible-supporter-fn kb context))))

(defn displaced-terms*
  "The `{old-term representative}` rewrites `sentence` undergoes under the built
  predicate `visible?` (`res/displaced-terms-in`), empty when nothing in it merged."
  [kb sentence visible?]
  (res/displaced-terms-in kb visible? sentence))

(defn displaced-terms
  "The `{old-term representative}` rewrites a sentence undergoes as `context` elects them,
  empty when nothing in it merged: what a supersession records, so `why-not` names the
  displacing representative."
  ([kb sentence] (displaced-terms* kb sentence nil))
  ([kb sentence context] (displaced-terms* kb sentence (res/visible-supporter-fn kb context))))

(defn rewrite-goal
  "A query goal in the normal form `context` sees (`res/goal-normal-form`), so a caller
  asking under a retired spelling still finds the restated facts.  `different` and a
  positive equation are asked as spelled (`res/goal-held-as-spelled?`), and a
  `modal_predicate`'s proposition is held opaque inside `res/representative-term`.
  `handle-of` and the `lookup` levels do not rewrite: they answer about storage."
  ([kb goal] (rewrite-goal kb goal nil))
  ([kb goal context] (res/goal-normal-form kb goal context)))

(defn rewritable-sentex?
  "May this stored sentex be migrated by an equality merge?  A rule when the merge
  displaces a symbol it mentions (`displaced-terms`): a predicate, a type or an
  individual constant (docs/equality.md, \"Merging predicates and types\").  A non-rule
  unless it is an equality relation or the negation of one: migration never restates an
  equation (docs/equality.md, \"Answering an equation\")."
  [kb sentex]
  (if (rules/rule? sentex)
    (boolean (seq (displaced-terms kb (sx/sentence-of sentex))))
    (let [s (:sentence sentex)]
      (and (not (equality-sentence? s))
           (not (equality-sentence? (sx/positive-body s)))))))

;; ---- matching ------------------------------------------------------------

(defn- permuting-literal?
  "Does `sentence` reach `res/raw-match`'s arrangement fan — a symmetric literal, or one
  whose predicate declares a commuting group?  `stored-once-per-handle` builds its dedup
  set only when this answers true, and `raw-match` asks itself the same question, so the
  reader pays for the dedup set exactly where a fan can put one handle in the result
  twice.

  Read unscoped, as `res/raw-match` reads it: the fan reaches every stored spelling,
  and `res/without-unbelieved-spellings` hides the one a reader's belief rules out."
  [kb sentence]
  (let [tax (reasoning/taxonomy kb)
        f   (when (sequential? sentence) (first sentence))]
    (or (sx/symmetric-literal? sentence #(tax/has-prop? tax :symmetric %))
        (boolean (and (symbol? f) (seq (tax/commuting-groups tax f)))))))

(defn- stored-once-per-handle
  "The stored sentex of each match, one per handle, keeping the first.  A symmetric literal
  with two variable arguments matches one stored fact twice and differently (`res/raw-match`),
  and the sentexes reader reports it once.  Lazy, so a consumer taking fifty of a hundred
  thousand pays for fifty.  Only a symmetric or commuting literal pays for the `seen` set;
  `negation-arbitration` reads this twice per opposed body."
  [symmetric? ms]
  (if-not symmetric?
    (map (fn [m] (nth m 2)) ms)
    (letfn [(step [xs seen]
              (lazy-seq
               (when-let [s (seq xs)]
                 (let [m (first s), h (nth m 0)]
                   (if (contains? seen h)
                     (step (rest s) seen)
                     (cons (nth m 2) (step (rest s) (conj seen h))))))))]
      (step ms #{}))))

(defn sentexes-matching-as-stored
  "Believed sentexes matching `sentence` as spelled, in `context`: `sentexes-matching`
  without the equality goal rewrite.  For a caller iterating the engine's own storage:
  `settle`'s walk over bodies stored in both polarities needs a superseded body to answer
  nothing, where the rewrite would hand back the representative's sentexes.  Otherwise
  `sentexes-matching`'s: literal, both symmetric orders, belief-sensitive, clear of the
  `exceptWhen` metas."
  ([kb sentence] (sentexes-matching-as-stored kb sentence '?ctx))
  ([kb sentence context]
   ;; This is the level-2 (`:local`) matcher: one literal context, no subtype fan-out, both symmetric
   ;; orders, belief-filtered, clear of the exceptWhen metas.  Routing through `res/raw-match` shares
   ;; `match-one`'s argument-root retrieval, so `(parentOf ?x Tom)` reads the node `[parentOf 2 Tom]`.
   ;; `without-excepted` then drops what a visible `except` hides (docs/contexts.md).  The fetched record
   ;; rides along as the third element.
   (->> (res/raw-match kb sentence context)
        (res/without-hidden-matches kb context sentence)
        (stored-once-per-handle (permuting-literal? kb sentence)))))

(defn sentexes-matching
  "*Believed* sentexes matching `sentence` in `context` — the implementation behind
  `vaelii.core/sentexes-matching`, which owns the user-facing docstring.  Literal (no subtype
  expansion), belief-sensitive (a stored-but-disbelieved sentex is excluded)."
  ([kb sentence] (sentexes-matching kb sentence '?ctx))
  ([kb sentence context]
   ;; a goal naming a term an equality merge has retired is rewritten to the class
   ;; representative first — the retired spelling stays a usable *question* even
   ;; though it is no longer a usable *answer* (docs/equality.md)
   (sentexes-matching-as-stored kb (rewrite-goal kb sentence context) context)))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :S7 :label "Last edge program" :kind :index :keyed-by :global :reads [:records :S5]
  :holds-content? false
  :retired-by {:image-install :R}
  :computed :write :imaged? :state :at [[:program]]
  :note "the last Program handed to the solver, with its classification (`vaelii.impl.asp.label`); registered here because that namespace loads on its first `do/label`"})

(caches/register-derived
 {:id :T12 :label "Supporter reach memo" :kind :cache :keyed-by :value
  :reads [:index :justifications]
  :holds-content? false
  :retired-by {:stored :G :removed :G :respelled :G :relabelled :K :held :K :settle-exit :K
               :recover :R :image-install :R}
  :computed :read :imaged? false :at [[:taxonomy :supporter-reach]]
  :value (fn [kb] (some-> (caches/value-at kb [:taxonomy :supporter-reach]) deref))
  :covered-by {:perf [:record-pass-beside-defeated-chains :record-pass-beside-a-reached-supporter]}
  :note "per relation and entry functors, the handles a forward walk from the stored `except`s' and placed `defeat`s' targets read and met no supporter of, with those targets and a mark of the touched sets: a read walks on from the handles touched since and, once `except/frame-write-count` moves, from the targets new since, and `note-reach-touched!` feeds it the touched sets a settle exit empties; or, for a walk that met a supporter, a path to it from a target, which a read checks against the network (`held-forward-reach`)"})

(caches/register-derived
 {:id :R12 :label "Call-scoped memos" :kind :pass :keyed-by :value :reads [:index :T1]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false
  :note "volatiles and memoized fns one call holds: `memberships`, `membership-reader` here; `checks/declaration-reader`, `stratification-readers` (held for a write or a settle in `rules/*stratification-memo*`, and the stored rules' negated antecedent keys in `rules/*negated-keys-memo*`, both emptied by a rule-index write); `except/reader-state`, held for a pass in `except/*reader-states*` while the change clock stands and its frame while `frames-hold?`; `plan/memoizing`, `plan-pairs`; `special/visibility-seeds`, `supersession-map`, `lift-statements`; `inherit/rejoin-rules`; `asp.label/local-analysis`, `component-classifier`"})
