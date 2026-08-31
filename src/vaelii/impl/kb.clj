;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.kb
  "The KB record, its constructor, and the ground floor of retrieval:
  find/create sentexes, the belief-filtered `sentexes-matching`, and the equality-closure
  goal rewriting that keeps a retired spelling usable as a question.

  Bottom of the engine stack (kb <- checks <- special <- integrate <- chain <-
  settle <- vaelii.core): everything here reads the storage protocols, the taxonomy, the
  JTMS and the matchers — never assertion, chaining, or settling.  `sentexes-matching`
  lives here rather than in core because the layers above it (`integrate-sentex`,
  `negation-nogoods`) need *querying*, not asserting — moving it down is what
  unties the old `declare assert query settle` knot."
  (:refer-clojure :exclude [isa?])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.config :as config]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.disk.index-snapshot :as snapshot]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.taxonomy :as tax]))

;; `solver`, `conflicts`, and `program` are atoms: the solver is swappable (the ASP
;; backend in vaelii.impl.asp.edge); `conflicts` holds the last settle's
;; unsatisfiable contradictions — the "solve result" surfaced by `core/conflicts`;
;; `program` holds the last edge Program handed to the solver.
;;
;; `program` is kept because belief is *self-erasing evidence*: once settle defeats
;; one side of a tie, that side stops matching, so the very nogood that produced the
;; contested set is no longer derivable from the KB.  Recomputing it after the fact
;; yields nothing.  Anything wanting to ask what the tie *was* — which beliefs were
;; forced and which were an arbitrary pick (`asp.edge/classify`) — has to read the
;; program the decision was actually made from.
;;
;; `violations` holds the definitional constraints a *derived* conclusion would have
;; broken during the last chaining run — see `place-conclusion` and `violations`.
;;
;; `contradictions` holds the coexisting P/¬P pairs the last settle left standing.
;; Those are *represented dilemmas*, not conflicts: neither rule named the other's
;; case, so there is nothing to arbitrate and both sides stay believed at :default
;; (docs/exceptions.md, "What surfaces where").  `conflicts` is now only the
;; irreducible clashes among known-true content.
;;
;; `recheck` is the exception re-check queue: `{rule-handle -> triggers}` for the rules
;; whose `exceptWhen` query may have flipped since the last settle, posted by the
;; triggers (a fact arriving or leaving on one of the exception's predicates, or any
;; genl/genlCx edge change) and drained by `settle`.  `triggers` is the set of
;; sentences that moved — which firings of that rule to re-evaluate — or `:all` when
;; there is no such sentence and all of them must be.  Nothing here caches whether an
;; exception *holds* — the queue says what to re-evaluate, and the re-evaluation says
;; what is true.
;;
;; `settle-stats` is instrumentation for the exception fixpoint: `:iterations` counts
;; the passes in which the blocked set actually moved (0 = nothing blocked, 1 = one
;; pass sufficed), `:passes` the total loop passes including the confirming one, and
;; `:histogram` the distribution of `:iterations` since the last reset.
;;
;; `qcn` is where a qualitative constraint network **lives between reads**: an atom of
;; `{[calculus-name context] -> {:read … :clock n}}`, stamped with `observe/change-clock`
;; and re-derived the moment that has moved (`vaelii.impl.qcn-kb`).  Per KB rather than
;; global, because two KBs in one JVM share the clock but not their content.
;;
;; `matches` is the literal cache (`vaelii.impl.literal-cache`): an atom of
;; `{[canonical-literal context hierarchical? arg-root?] -> {:value … :clock n}}` holding
;; what `matches-visible` answered, α-renamed so two spellings of one question share an
;; entry and stamped with `observe/change-clock` so any mutation retires it.  Per KB for
;; the same reason `qcn` is: two KBs in one JVM share the clock but not their content, so
;; a global cache would serve one KB's extent as another's.  A **declared field** rather
;; than a bare key on the map, because `matches-visible` reads it on every retrieval and
;; an extension-map key costs a hash lookup where a field costs none.
;; `reports` memoizes the `contradicts` reports `conflicts` and `contradictions` hand
;; back — `{#{h1 h2} -> report}` for the pairs the last settle reported, and nothing else,
;; so it is bounded by what is standing rather than by what ever stood.  Why an entry the
;; settle's region does not hold can be carried forward, and what removing it costs:
;; docs/nmtms.md, "The reports are rebuilt only where the region moved".
;;
;; `negations` is the memo beside `:opposed`, and the two answer different halves of one
;; question: `:opposed` says *which bodies could contradict*, kept O(1) per mutation at the
;; store and removal choke points; `:negations` says *what each of those bodies currently
;; contradicts about*, as `{body #{nogood}}`.  `:dirty` is the bodies a store or a removal
;; touched since the last settle drained it (`note-opposed!` posts them, the same choke
;; points that maintain `:opposed`); `:vocab` is the genlCx generation the
;; joint-visibility test reads through, so a context edge retires the whole memo.  Which
;; three things move a pairing, and the measured cost of dropping either narrowing:
;; docs/nmtms.md, "Soft, prioritized contradictions".
;;
;; `feed` is the change feed's listeners and the region a settle files for them
;; (`vaelii.impl.feed`).  A field rather than a bare key for the same reason as
;; `:naming`: every settle reads it to decide whether to accumulate anything, and a KB
;; nobody is listening to should pay a field read and not a hash lookup.
;; `rule-antecedents` and `rule-contexts` are the rule rosters `special` bumps on every
;; rule index/unindex and reads per settle for the visibility seeds — fields for the
;; same reason as `:matches` and `:feed`.  Neither is stored, and recovery replays
;; belief and the taxonomy rather than rule indexing, so `rebuild-rule-roster!` is what
;; refills them on a recovered, reopened or forked KB.
;;
;; `excepted` is the visibility roster beside `:opposed`, and kept the same way: `{context
;; -> {except-handle -> hidden-handle}}` for the stored `(except (sentexHandle H))` facts,
;; maintained O(1) at the store and removal choke points and rebuilt by `recover`.  It
;; holds **storage**, not belief — an except's own handle is what a reader checks `in?`
;; against — for the reason `:opposed` holds storage: belief moves without a sentex
;; arriving or leaving, so a roster that tried to track it would be maintained at a choke
;; point that does not exist.  A field rather than a bare key because `res/excepted-handles`
;; reads it per placement and per candidate justification (docs/exceptions.md, "Visibility
;; removal").
;; `dir` is the record store's directory when the records are durable, else nil. It is
;; here so `core/close!` can release the exclusive FileLock the disk backend takes:
;; without it a long-running process could not hand a directory to another process, or
;; reopen it elsewhere, until the JVM exited.
;; `snapshot-dir` is that same directory again, and non-nil only on a KB whose index is
;; the mapped image — the write door's whole gate on the image cadence
;; (`create-sentex`).  A separate field rather than a test on `dir`, because `dir` is set
;; for every durable-records KB and the cadence is for one of them: reading `dir` there
;; put the refresh call, its root-count argument and a `realpath` on the write path of
;; `:disk-memory`, `:disk-dense`, `:disk-columnar` and `:disk-log` alike, none of which
;; has an image.  Resolved once at `open-kb`, so nothing on the write path canonicalizes
;; a path this one already did.
;; `unrecovered` is the write side of "this KB's derived state was never built over a
;; store that already held records" — `{:no-belief bool :no-index bool :announced? bool}`,
;; each key absent until something asks.  Reads over that state answer nothing and can be
;; re-asked; a write lands content the store keeps, so the write doors ask
;; `write-hazards` below.  An atom because `recover` and `reindex` clear what they build.
(defrecord KB [records index tms taxonomy provers solver conflicts program violations
               contradictions recheck refused settle-stats chain-stats opposed excepted
               negations clashes supersessions reports qcn qcn-joined matches closures
               naming constraints rule-antecedents rule-contexts feed dir snapshot-dir
               unrecovered])

;; ---- storage selection: two independent axes ------------------------------
;;
;; A KB's two stores answer to different pressures and are chosen separately.  The
;; **records** are the ground truth — what must survive — so the question there is
;; durability.  The **index** is *derived*: `reindex` rebuilds every entry of it from
;; the records, through the protocols, so it need never
;; be persisted at all and the question there is representation (how dense, how fast).
;; Welding the two into one `:backend` keyword makes every density experiment
;; memory-only and every durable KB pay for a durable index it can always recompute.
;;
;; So the axes are independent — `:records` (`:memory` / `:disk`) and `:index`
;; (`:memory` / `:dense` / `:columnar` / `:disk-log`) — and `:backend` is sugar naming a
;; pair.  **Every legal pair has a name**, spelled `<records>-<index>`, so the two opts
;; are for overriding a half rather than for reaching a corner the table left out.

(def ^:private backend-modes
  "The `:backend` sugar: each name expands to a `{:records :index}` pair, and reads
  `<records>-<index>` — `:disk-memory` is durable records with the derived index in RAM
  (rebuilt on open), `:disk-columnar` the same with the columnar index instead.
  `:memory` is the one pair that is the same store on both axes, named for the store
  rather than doubled.

  `:disk-log` is durable records under the **log index**: a RAM key→value map with a
  write-ahead log beneath it, so it opens already populated and needs no reindex while its
  residency stays a RAM index's (`vaelii.impl.disk.kv`).  The name says which of those two
  things the disk buys.

  `:disk-snapshot` is the columnar index **read back from a mapped image** rather than
  rebuilt: `:index :snapshot` is `:columnar` plus the promise that an open maps
  `<dir>/index/` when the image there still describes the records.  It is a named
  representation and not a guarantee of validity — the stamp is checked on every open and
  any doubt reindexes — so what the name buys is that the intent is in the opts map, and
  an open that had to rebuild says so at `:warn` instead of passing for a fast one.

  Eight `:memory`/`:disk` pairs, plus the two adapter record axes — `:sqlite` (an
  embedded-SQLite file) and `:pg` (a Postgres server), each resolved lazily so the engine
  stays JDBC-free.  `:sqlite` and `:pg-memory` take the derived RAM index, rebuilt on
  open; `:pg-disk-log` takes the log index, which lives on the machine running the writer
  rather than in the database (docs/storage.md).  **RAM records with the log index is
  refused, and the image pairs with `:disk` records alone**, so no name spells either
  (`backend-axes` says why)."
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
   ;; a fork: both halves decorate whatever the frozen base resolved to, so `:overlay` is
   ;; a *decorator* selection rather than a store — see the `:base` / `:overlay` opts
   :overlay         {:records :overlay :index :overlay}})

(def ^:private durable-under-log-index
  "The **durable** record axes — the ones a persisted index half may sit over at all.
  `:disk` shares its directory and lifecycle; `:pg` is on a server, so a local index file
  is the only one its records can have, and the files then belong to the host that ran the
  writer rather than travelling with the KB (docs/storage.md).

  Both durable index axes want durability for the same reason, and only the reason's
  ending differs.  A `:disk-log` index over records that vanish at JVM exit would be read
  as truth on the next open.  An image over them is stamped with a fingerprint of those
  records, so it is *caught* — `:records-differ` — and the cost is a wasted rebuild rather
  than a wrong answer.  The second is refused anyway: a KB whose every open discards its
  image has asked for a representation it can never get.

  Durability is necessary and not sufficient for the image, which narrows to `:disk`
  alone one gate further down (`image-record-axis`)."
  #{:disk :pg})

(def ^:private durable-index-axes
  "The index axes that need durable records under them, and for each: the durable record
  axes it actually pairs with, and the sentence saying why it needs one — both spliced
  into `backend-axes`' refusal so it reads as one argument rather than as a shared message
  with a name substituted.

  `:snapshot` names `:disk` where `:disk-log` names both, and the narrowing is a *second*
  requirement rather than a stricter reading of this one: `:pg` records are durable and
  are refused the image a gate further down, with the argument that is actually theirs
  (`image-record-axis`)."
  {:disk-log {:with ":disk or :pg"
              :why  "persisting the derived half over a store that empties at JVM exit leaves index files describing records that are gone, and the next open answers every query out of them believing nothing is wrong"}
   :snapshot {:with ":disk"
              :why  "an image is stamped with a fingerprint of the records it was built from, so over a store that empties at JVM exit every open discards it and reindexes — the representation the name asks for is one this pairing can never hold"}})

(def ^:private image-record-axis
  "The one record axis the mapped image pairs with.

  Where `:disk-log` asks only for durability, the image asks for a **particular store**:
  it is stamped with `record-store/slot-fingerprint`, which is the disk record store's own
  sequential read of its slot file and lives on that namespace rather than on the
  `RecordStore` protocol.  No other record axis can answer it — an adapter is a separate
  repository and the protocol offers no method to implement — so an image over one could
  be neither stamped on the way out nor validated on the way in, and validity is this
  representation's whole design (`vaelii.impl.disk.index-snapshot`).  `:pg` records take
  the log index instead, which is derived from the records through the protocols and so
  needs nothing of the store but its reads."
  :disk)

(def ^:private reserved-backend-names
  "Names `open-kb` refuses outright, and the pairing to take instead.  Each is a name a
  caller reaches for and this engine does not read: `:disk` and `:pg-disk` read as *both
  halves out of core*, which no pairing here is.  The log index holds its whole key→value
  map in RAM and the log under it buys **durability, not residency**
  (`vaelii.impl.disk.kv`) — which is what `:disk-log` and `:pg-disk-log` say.

  **Refused rather than aliased.**  An index axis names a directory layout, so a name
  that answers to two of them opens a store in a layout its caller did not ask for: a
  wrong-shaped directory and a heap profile nobody chose, discovered by the machine
  running out of it.  `check-opts!` already treats an option `open-kb` cannot read as a
  refusal rather than a default, and a *name* it cannot read is that same argument one
  level up — one edit per call site, against a KB that is never opened in a layout its
  caller did not name."
  {:disk    :disk-log
   :pg-disk :pg-disk-log})

(defn backend-axes
  "The `{:records :index}` selection for `opts`: the `:backend` sugar expanded, with an
  explicit `:records` / `:index` opt overriding its half.  Public because it is the one
  answer to \"which two stores does this opts map name?\" — a harness asking that (the
  test suite's index-shape gate) must read the same table `open-kb` does, or a new sugar
  name silently leaves it saying the wrong thing.

  **The `:disk-log` index needs durable records**, on either spelling.  The index is
  a function of the records, so persisting the derived half while the ground truth
  evaporates at JVM exit leaves index files describing records that no longer exist — and
  the next open answers every query out of them, believing nothing is wrong.  Two record
  axes carry it: `:disk`, which shares the index's directory and lifecycle, and `:pg`,
  whose records are on a server and for which a *local* durable index is the only durable
  index there is.

  **The `:snapshot` index needs the `:disk` record store**, which is more than durability:
  an image carries a fingerprint of the records it describes, and only that store can
  compute one (`image-record-axis`).  So `:pg` records take `:pg-disk-log`, and the
  refusal says so.

  **`:disk` names no pairing here and no index axis.**  Both spellings are refused, and
  each refusal names the pairing to take instead rather than resolving to something near
  it (`reserved-backend-names`)."
  [{:keys [backend records index] :or {backend :memory}}]
  (when-let [want (reserved-backend-names backend)]
    (throw (ex-info (str "unknown KB backend " (pr-str backend) " — the durable-index pairing is "
                         "spelled " (pr-str want) ", durable records under a write-ahead-logged "
                         "index whose key->value map is in RAM.  The log buys durability and not "
                         "residency; the name says which.")
                    {:type :unknown-backend :backend backend :instead want})))
  (when (= :disk index)
    (throw (ex-info (str "unknown index backend :disk — the write-ahead-logged index is "
                         ":disk-log.  It holds the whole key->value map in RAM and logs its "
                         "mutations, so the log buys durability and not residency; the name "
                         "says which.")
                    {:type :unknown-backend :index index :instead :disk-log})))
  (let [pair (or (backend-modes backend)
                 (throw (ex-info (str "unknown KB backend " (pr-str backend) " — want one of "
                                      (pr-str (vec (sort (keys backend-modes))))
                                      ", or the :records / :index opts")
                                 {:type :unknown-backend :backend backend})))
        axes {:records (or records (:records pair))
              :index   (or index   (:index pair))}]
    (when-let [{:keys [with why]} (and (not (durable-under-log-index (:records axes)))
                                       (durable-index-axes (:index axes)))]
      (throw (ex-info (str "the " (:index axes) " index needs durable records — " with " — and these are "
                           (pr-str (:records axes)) ".  An index is derived from the records, so "
                           why ".  `:sqlite` records already live in a directory, and a durable index "
                           "beside them is this pairing without its shared lifecycle: take :disk-log or "
                           ":disk-snapshot for that.  Otherwise take a derived index (`:memory`, `:dense`, "
                           "`:columnar`), rebuilt on open.")
                      (assoc axes :type :unknown-backend))))
    ;; Durable, and still not the store the image needs.  The gate above has already taken
    ;; every non-durable record axis, so what reaches here is `:pg` — durable, on a server,
    ;; and with no fingerprint to stamp an image with.
    (when (and (= :snapshot (:index axes)) (not= image-record-axis (:records axes)))
      (throw (ex-info (str "the :snapshot index pairs with :disk records and these are "
                           (pr-str (:records axes)) ".  An image is stamped with a fingerprint "
                           "only the disk record store computes — a sequential read of its slot "
                           "file, which belongs to that store rather than to the RecordStore "
                           "protocol — so an image over these records could be neither stamped "
                           "when it was written nor checked when it was read, and an image nothing "
                           "can check is one every open has to discard.  Take :pg-disk-log, whose "
                           "durable index is derived through the protocols and so asks nothing of "
                           "the record store but its reads.")
                      (assoc axes :type :unknown-backend :instead :pg-disk-log))))
    axes))

(defn- sqlite-record-store-ctor
  "The `com.vaelii/sqlite` adapter's record-store constructor, resolved **lazily** — the
  same trick `create-tms` uses for the dense TMS — so the SSPL engine never loads the
  SQLite driver unless a KB selects `:sqlite`.  Throws a clear missing-adapter error when
  the Apache-2.0 sibling is not on the classpath, rather than a bare
  `FileNotFoundException` from the resolve."
  []
  (or (try (requiring-resolve 'vaelii.sqlite.record-store/sqlite-record-store)
           (catch java.io.FileNotFoundException _ nil))
      (throw (ex-info (str "backend :sqlite needs the vaelii-sqlite adapter (com.vaelii/sqlite) "
                           "on the classpath — an Apache-2.0 sibling the engine does not depend "
                           "on, so add it to your project to select the :sqlite backend.")
                      {:type :unknown-backend :records :sqlite}))))

(defn- pg-record-store-ctor
  "The `com.vaelii/postgres` adapter's record-store constructor, resolved **lazily** —
  the same trick `create-tms` uses for the dense TMS — so the SSPL engine never loads a
  JDBC driver unless a KB selects `:pg-memory` or `:pg-disk-log`.  Throws a clear
  missing-adapter error when the Apache-2.0 sibling is not on the classpath, rather than
  a bare `FileNotFoundException` from the resolve."
  []
  (or (try (requiring-resolve 'vaelii.postgres.record-store/pg-record-store)
           (catch java.io.FileNotFoundException _ nil))
      (throw (ex-info (str "the :pg record backend needs the vaelii-postgres adapter "
                           "(com.vaelii/postgres) on the classpath — an Apache-2.0 sibling the "
                           "engine does not depend on, so add it to your project to select "
                           ":pg-memory or :pg-disk-log.")
                      {:type :unknown-backend :records :pg}))))

(defn- pg-spec
  "The `:pg` opt as a db-spec map.  A string is a JDBC URL, which is the spelling an
  environment variable arrives in; a map is a next.jdbc db-spec, plus the adapter's own
  keys (`:schema` and the cache sizes), and is passed through untouched."
  [pg]
  (if (string? pg) {:jdbcUrl pg} pg))

(defn- record-store-for
  "The `RecordStore` for the record axis.  `:memory` keys the in-RAM store by `:space`,
  so a KB rebuilt over the same number sees the same records
  (`vaelii.impl.memory`); `:disk` opens the durable log/idx record store in a directory
  (`:dir`, else derived from the space number), shared per directory — and opens
  *only* the records, so a derived-index mode writes no index files
  (`vaelii.impl.disk.backend`).  `:sqlite` opens the embedded-SQLite record store over a
  single file in that same directory, and `:pg` opens the Postgres store over the
  database the `:pg` opt names — both through lazily-resolved sibling adapters."
  [kind {:keys [space] :or {space 0} :as opts}]
  (case kind
    :memory (mem/memory-record-store {:space space})
    :disk   (disk/records-for (disk/disk-dir opts))
    ;; a single file under the KB's directory; ensure the directory exists (SQLite
    ;; creates the file, not its parent), the way the disk backend makes its own dir.
    :sqlite (let [dir (disk/disk-dir opts)]
              (.mkdirs (java.io.File. ^String dir))
              ((sqlite-record-store-ctor) {:dbtype "sqlite" :dbname (str dir "/records.sqlite")}))
    ;; the database is named by the caller and nothing here derives one: a KB that
    ;; silently took a default server is a KB whose records are somewhere nobody said
    :pg     ((pg-record-store-ctor) (pg-spec (:pg opts)))
    ;; `:overlay` is resolved by `open-kb`, which alone knows the base — reaching here
    ;; means a base or an overlay half was itself declared `:overlay`, and a stack of
    ;; forks is deliberately not built (docs/overlay.md)
    (throw (ex-info (str "unknown record backend " (pr-str kind) " — want :memory, :disk, :sqlite or :pg"
                         (when (= :overlay kind)
                           " (an :overlay half cannot itself be an overlay)"))
                    {:type :unknown-backend :records kind}))))

(def ^:private jdbc-pg-url
  ;; jdbc:postgresql://host[:port]/dbname[?params] — enough to canonicalize the two
  ;; spellings of one database against each other.
  #"(?i)jdbc:postgres(?:ql)?://([^:/?]+)(?::(\d+))?/([^?]+)(?:\?.*)?")

(defn- pg-identity
  "What two `:pg` opts have to agree on to be **the same record store**: the server, the
  database and the schema the tables live in.

  **Canonical, not literal.**  A JDBC URL and the `:dbtype`/`:host`/`:dbname` spelling of
  one database are the same store and must key alike — `pg-spec`'s own docstring calls the
  URL \"the spelling an environment variable arrives in\" — and so are a stated `:port 5432`
  and an omitted one.  Keying on the literal opts map splits one database into two index
  spaces, and two KBs then mint two handles for one sentence, which no `reindex` can merge
  afterwards.

  A `:space` number does not name a database at all, which is why this exists."
  [pg]
  (let [m       (if (string? pg) {:jdbcUrl pg} pg)
        [_ h p d] (some->> (:jdbcUrl m) (re-matches jdbc-pg-url))
        host    (str/lower-case (str (or h (:host m) "localhost")))
        port    (or (some-> (or p (:port m)) str str/trim parse-long) 5432)
        dbname  (str (or d (:dbname m)))
        schema  (some-> (:schema m) name)]
    [host port dbname schema]))

(defn- derived-index-space
  "What a **derived** (in-RAM) index's shared state is keyed by.  A derived index is a
  function of the records, so it must be shared exactly when the records are — and this
  is the whole of what enforces that: the `:space` number when the records are in RAM,
  the record *directory* when they are in one (`:disk`, and `:sqlite`'s file), the
  database when they are on a server (`:pg`).  Each axis has its own registry
  (`vaelii.impl.memory`, `.dense-kv`, `.columnar`), so one key keys both stores
  without either reaching the other's, and a KB cannot be given a private index over
  records it shares — one store's records answered out of another's index, with
  nothing to signal it."
  [record-kind {:keys [space] :or {space 0} :as opts}]
  (case record-kind
    ;; The **tag** discriminates the axis, not just the directory: `:sqlite` records and
    ;; `:disk` records in one directory are two different stores, and keying both on the
    ;; path alone hands them one shared index over records neither of them holds.
    :disk   [:disk (disk/canonical-dir (disk/disk-dir opts))]
    :sqlite [:sqlite (disk/canonical-dir (disk/disk-dir opts))]
    :pg     [:pg (pg-identity (:pg opts))]
    space))

(defn- index-store-for
  "`[index-store durable?]` for the index axis.  Four of the five are **derived-only**
  — the flat `:memory` map, the `:dense` int-postings backend (Phase 1,
  `vaelii.impl.dense-kv`), the `:columnar` native trie (Phase 2, `vaelii.impl.columnar`)
  and `:snapshot`, which is that same trie — and open empty, so a KB pairing one with
  durable records must `reindex` before it can answer (`open-kb`).  `:disk-log` is the
  write-ahead-logged index, which opens already populated.

  **`:snapshot` is derived, and that is the whole of the difference between it and
  `:disk-log`.**  It builds the columnar store and answers `false` here, so `open-kb`
  takes the rebuild path — and the mapped image is an *attempt* on the way into that
  path, taken when the stamp holds and skipped when it does not.  Answering `true` would
  say the store opens populated, which is true only of an image nobody has checked yet.

  The flag is returned rather than sniffed from the store type at the call site: what
  makes an index durable is which one was *selected*, and a type test would have to be
  updated by whoever adds the next backend, silently and after the fact."
  [kind record-kind opts]
  (if (= :disk-log kind)
    [(disk/index-for (disk/disk-dir opts)) true]
    (let [space (derived-index-space record-kind opts)]
      (case kind
        :memory   [(mem/memory-index-store        {:space space}) false]
        :dense    [(dense/dense-index-store       {:space space}) false]
        (:columnar :snapshot) [(columnar/columnar-index-store {:space space}) false]
        (throw (ex-info (str "unknown index backend " (pr-str kind)
                             " — want :memory, :dense, :columnar, :snapshot, or :disk-log"
                             (when (= :overlay kind)
                               " (an :overlay half cannot itself be an overlay)"))
                        {:type :unknown-backend :index kind}))))))

;; ---- forks: an overlay over a frozen base ---------------------------------
;; `:overlay` is not a store but a *decorator* over whatever each axis resolves to, so it
;; is the one selection `open-kb` has to resolve itself: it needs the base's stores, which
;; the axis functions above are not given.  A base arrives either already open
;; (`:base-stores`, what `core/fork` passes from a live KB) or as the opts naming it
;; (`:base`, which opens the base's stores here — a directory this process is not
;; already holding a KB over, since a durable directory takes the exclusive
;; single-writer lock).

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

(defn- gate-base-index-layout!
  "Hold a durable base index to the same key-layout sentinel `open-kb` holds its own to.

  `open-kb`'s gate reads the *fork's* directory, so a base opened by `:base` opts slips
  past it and the fork mounts an index whose keys moved — a populated-looking count over
  queries that answer nothing.  The repair the gate performs elsewhere (clear, rebuild
  from the records, restamp) is a **write to the base**, which a read-only mount may not
  make, so this refuses instead and names the one place the rebuild can happen."
  [index-kind base index-store]
  (when (= :disk-log index-kind)
    (let [root (str (disk/disk-dir base) "/index")]
      (when (and (.isDirectory (java.io.File. ^String root))
                 (= :stale (dfiles/index-layout-decision
                            root kv/index-layout-version
                            (pos? (long (p/count-at index-store []))))))
        (throw (ex-info (str "the durable index at " root " was written under another key "
                             "layout — every read whose key shape moved would miss.  A fork "
                             "mounts its base read-only and cannot rebuild it: open that "
                             "directory as a KB first, which clears and rebuilds the index, "
                             "then mount the fork over it.")
                        {:type :stale-index-layout :dir root})))))
  index-store)

(defn- resolve-base
  "The `{:records :index}` pair a fork mounts over, frozen by the mount itself."
  [{:keys [base base-stores]}]
  (cond
    ;; only this arm needs the fork check: an `:overlay` half in the `:base` opts below
    ;; never reaches a store, since `record-store-for` refuses the name outright
    base-stores (check-not-forked! base-stores)
    base        (let [{rk :records ik :index} (backend-axes base)]
                  {:records (record-store-for rk base)
                   :index   (gate-base-index-layout!
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
  to it.  `:reference` stays the simpler baseline a caller can pin.

  Resolved lazily, exactly as the solver backends are, so `:reference` never loads
  RoaringBitmap or fastutil."
  [kind]
  (case kind
    :reference (jtms/create-tms)
    :dense     ((requiring-resolve 'vaelii.impl.dense-jtms/create-dense-tms))
    (throw (ex-info (str "unknown TMS " (pr-str kind) " — want :reference or :dense")
                    {:type :unknown-backend :tms kind}))))

(def opt-keys
  "Every key `open-kb` reads.  Public because it is the answer to \"is this a real
  option?\", and a caller that can ask does not have to find out from a wrong answer."
  #{:backend :records :index :space :dir :pg :tms :recover?
    :naming :constraints :base :base-stores :overlay})

(defn- check-opts!
  "Refuse a key `open-kb` does not read.  **An option that is not read is not an option**:
  a misspelt `:space` leaves the KB on the default space in silence, so two KBs a
  caller built to keep apart share one store — each one's flush empties the other, and
  every read after it answers out of the wrong records with nothing to signal it.  A KB
  that took the default is indistinguishable downstream from one that asked for it, so
  the only place that can still tell is here, where what was written is still legible.

  `where` names the map, since a fork's `:base` and `:overlay` carry opts of their own.

  Through the shared door (`opts/check!`), which also refuses a non-map `opts` — the one
  thing this door did not: `(open-kb :nope)` reached `keys` and came back as a bare
  `IllegalArgumentException` about creating an ISeq, where every other public entry point
  answers `:unknown-option`.  It is the most-used option map in the API and was the one
  with no guard on the shape of it."
  [opts where]
  (opts/check! opts opt-keys where
               (str "An option nothing reads takes the default in silence,"
                    " which for a store number means sharing a store.")))

;; How many in-RAM KBs this process has opened on the **default** space without naming
;; it — read by `note-default-ram-space!` below.  `defonce` so a REPL reload does not
;; forget, which is the session the count exists for.
(defonce ^:private default-ram-space-opens (atom 0))

(defn- note-default-ram-space!
  "Say so the second time a KB opens on the default in-RAM space without naming it.

  The space number names the store, and it defaults to 0 — so `(open-kb {})` twice
  in one process is **one store behind two KB values**, which is not what the second
  call looks like it asked for.  It is the REPL's most ordinary gesture: build a KB,
  experiment, then `(def kb2 (open-kb {}))` to start clean.  What that gets is the
  first KB's records recovered into the second (an `::reindexed-on-open` line at
  `:info`, addressed to a different question), and from then on two belief graphs over
  one store: `kb` writes and `kb2` does not see it, because belief is per-KB and only
  the writer's is relabelled.  Neither answer is an error, so nothing else says a word.

  **A warning and never a refusal.** Sharing a space is a feature — it is how
  `recover` sees the same records, how the suite's fixtures rebuild over one store, and
  how a second KB mounts a base.  What is unlikely to be deliberate is *defaulting*
  onto it twice, so naming the number — `{:space 2}`, or `0` written out — says the
  sharing is meant and silences this.  Only in-RAM records are affected: a `:disk` KB
  is keyed by directory and takes a file lock."
  [opts rkind]
  (when (and (= :memory rkind)
             (not (contains? opts :space))
             (= 2 (swap! default-ram-space-opens inc)))
    (trove/log! {:level :warn :id ::default-ram-space-reused
                 :msg (str "a second in-RAM KB opened on the default space (:space 0) "
                           "— the number names the store, so this KB and the earlier "
                           "one are two belief graphs over one set of records, and a "
                           "write through either is invisible to the other until it is "
                           "recovered.  Give this KB its own space ({:space 2}), or "
                           "name 0 to say the sharing is meant and silence this.")
                 :data {:space 0}})))

(defn- check-mount-opts!
  "Refuse a mount or durability key nothing in this axis selection reads.

  All five keys are in `opt-keys` — each is a real option — so `check-opts!` passes
  them, but each is read only under the selection it belongs to, and an opts map that
  names one without the other is two halves of a request whose silent resolution is a
  different KB.  `:base` / `:base-stores` / `:overlay` are read when an axis is
  `:overlay`: on any other selection `{:backend :memory :base-stores …}` opens a plain
  KB with nothing mounted, and every read that was meant to see the base answers as
  though it were empty.  `:dir` is read when a half is `:disk`, or the records are
  `:sqlite` (whose file lives in that directory): on RAM stores it names a directory
  nothing writes, so the caller who asked for durability loses the store at JVM exit —
  behind an open that looked exactly like the durable one.  (A fork's
  top-level `:dir` is the same nothing: its own writable half's directory lives in the
  `:overlay` sub-map, checked here on its own axes.)  `:pg` names the database the
  records live in, and is the one key here that is **required** rather than merely
  read: nothing derives a default server, so `:pg` records without it have nowhere to
  be — and `:pg` on any other records axis is a database nothing connects to, behind a
  KB that opened in RAM.  `where` names the opts map, as in `check-opts!`."
  [opts {rkind :records ikind :index} where]
  (when-not (or (= :overlay rkind) (= :overlay ikind))
    (when-let [given (seq (filterv #(contains? opts %) [:base :base-stores :overlay]))]
      (throw (ex-info (str where " was given " (str/join ", " (map pr-str given))
                           " but neither axis is :overlay, so nothing would be mounted"
                           " — the KB opens plain and every read of the base answers"
                           " empty.  A fork is spelled {:backend :overlay :base …} (or"
                           " :records / :index :overlay); drop the key if no fork was"
                           " meant.")
                      {:type :unknown-option :unknown (vec given)
                       :records rkind :index ikind}))))
  (when-not (or (= :disk rkind) (= :disk-log ikind) (= :sqlite rkind))
    (when (contains? opts :dir)
      (throw (ex-info (str where " was given :dir " (pr-str (:dir opts))
                           " but no half is :disk or :sqlite, so nothing writes there — the"
                           " store lives in RAM and is gone at JVM exit, the opposite of what"
                           " naming a directory asks for.  Want durability?"
                           " {:backend :disk-log} (or :disk-memory / :disk-dense /"
                           " :disk-columnar / :sqlite / :pg-memory).")
                      {:type :unknown-option :unknown [:dir]
                       :records rkind :index ikind}))))
  (if (= :pg rkind)
    (let [pg (:pg opts)]
      (when-not (or (and (map? pg) (seq pg)) (and (string? pg) (seq pg)))
        ;; A present nil, an empty map and a bare DataSource all reach here.  The first two
        ;; name no database — and `:or` does not fire on a present nil, so silence would be
        ;; the default server this option exists to refuse.  A DataSource names one that
        ;; cannot be *identified*: the derived index and the durable one are both keyed by
        ;; which database the records are in, and an opaque object answers that with
        ;; nothing.  Hand the adapter its own pool directly if that is what is wanted.
        (throw (ex-info (str where " needs :pg to name a database: a next.jdbc db-spec"
                             " ({:dbtype \"postgresql\" :host … :dbname …}, optionally"
                             " :schema) or a JDBC URL string, got " (pr-str pg)
                             ".  Nothing here derives a server, and an index is keyed by"
                             " which database its records are in — so a KB that took one by"
                             " default would hold its records somewhere nobody said, and one"
                             " whose database cannot be named cannot be keyed apart from"
                             " another's.")
                        {:type :unknown-option :missing [:pg]
                         :records rkind :index ikind})))
      ;; The durable index is files on THIS host describing records on a server, and
      ;; nothing in a directory says which server.  A derived default would put two KBs
      ;; over two databases in one directory — `disk-dir` falls back to
      ;; `<tmpdir>/vaelii-disk/space-<n>`, so two `{:backend :pg-disk-log}` opts that name
      ;; no directory are the same one — and the coverage check that would otherwise catch
      ;; it compares *counts*, which two unrelated databases can easily match.
      (when (and (= :disk-log ikind) (not (contains? opts :dir)))
        (throw (ex-info (str where " selected :pg-disk-log but named no :dir.  The durable index"
                             " lives on this host and describes records on a server, so the"
                             " directory belongs to a database rather than falling out of a"
                             " space number — and a derived default is one two KBs over two"
                             " databases would share, each answering out of the other's"
                             " index.  Name the directory, or take :pg-memory, whose index"
                             " is in RAM and rebuilt on open.")
                        {:type :unknown-option :missing [:dir]
                         :records rkind :index ikind}))))
    (when (contains? opts :pg)
      (throw (ex-info (str where " was given :pg but its records are " (pr-str rkind)
                           ", so nothing connects to that database — the KB opens on the"
                           " store its records axis names and every write lands there"
                           " instead.  Want Postgres records? {:backend :pg-memory :pg …}"
                           " (or :pg-disk-log, which adds a local durable index).")
                      {:type :unknown-option :unknown [:pg]
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
                    {:type :unknown-option :naming policy
                     :options (vec (sort (keys nm/policies)))}))))

(def constraint-policies
  "The constraint policies a KB's front door may hold, as `open-kb`'s `:constraints`.

    :refuse     `assert` refuses a disjoint / functional clash, and a declaration
                arriving after the content it convicts reports rather than decides
    :arbitrate  refuse only against `:monotonic` content; against a `:default` claim
                admit the sentence and let `settle` arbitrate the pair — and let a
                declaration reach back over what is already stored, so a violating set
                lands on the same belief in every arrival order

  This is **this KB's** policy, not the build's, for `:naming`'s reason: whether a writer
  is told no is an application question, and one process can hold a KB curating a
  hand-written ontology beside one ingesting a corpus whose schema arrives last.
  `checks/arbitrating?` is what reads it, and an unstated policy reads the process
  default there rather than one of these.

  **The policy is not persisted, and a `recover` decides more than `:refuse` does.**  It
  belongs to the KB handle, not to the store, so reopening the same records under the
  other policy is legitimate and changes what belief settles to.  Sharper than that: a
  rebuild's region is *every* stored sentex, so `settle/clash-nogoods` finds a standing
  clash from the region alone — no declaration sweep needed — and decides it under either
  policy.  A `:refuse` KB therefore believes both sides of a clash it was built
  incrementally into, and one side of the same clash after a restart.  That is the
  `:refuse` half being the loose one: `clash-nogoods` is deliberately not gated on
  `*rebuilding?*` because a nogood is *state* that belief depends on, and a rebuild that
  skipped it would revive the loser of a decided clash.  A KB that wants the two to agree
  wants `:arbitrate`."
  #{:refuse :arbitrate})

(defn- check-constraints!
  "Refuse a `:constraints` policy `constraint-policies` does not name, returning it.
  Beside `check-naming!` because it is the same kind of setting — this KB's front-door
  policy, not the build's — and the same failure when it is misspelt: a KB that silently
  took `:refuse` when it was told `:arbitrate` refuses content the caller expected to
  land and arbitrate."
  [policy]
  (if (contains? constraint-policies policy)
    policy
    (throw (ex-info (str "unknown :constraints policy " (pr-str policy) " — open-kb reads "
                         (str/join ", " (map pr-str (sort constraint-policies))))
                    {:type :unknown-option :constraints policy
                     :options (vec (sort constraint-policies))}))))

(def recover-modes
  "What `:recover?` may say, and the setting each one means.

    :auto / true   rebuild the TMS and taxonomy at construction — and, over a derived
                   index, rebuild the index first.  The default
    :warn          leave them empty and log that the store holds records nothing can
                   answer out of
    false          leave them empty, in silence

  `true` is an **alias**, not a fifth behaviour: a `?`-suffixed option reads as a
  boolean, and a caller who writes one is asking for the recovery rather than for the
  warning."
  {:auto :auto, true :auto, :warn :warn, false false})

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
                         " — open-kb reads :auto (or true), :warn, and false"
                         ;; `:or` does not fire on a key that is present holding nil, so
                         ;; a caller threading an optional through lands here rather than
                         ;; on the default, and the bare roster reads as if it should not
                         (when (nil? recover?)
                           (str ".  An explicit nil is not the default: omit the key"
                                " for :auto, or pass false to open in silence")))
                    {:type :unknown-option :recover? recover?
                     :options [:auto true :warn false]}))))

;; ---- the write side of an unbuilt derived state --------------------------
;;
;; "Unrecovered" names one condition on the read side and two on the write side, and the
;; two are repaired by different calls.  **No belief** is an empty TMS over a full record
;; store: every definitional check reads `jtms/in?` and so passes vacuously, and no later
;; moment re-runs them (`recover`'s closing settle binds `settle/*rebuilding?*`).  **No
;; index** is the derived index opening empty over those same records: `assert` dedups
;; through `p/lookup`, so every assert mints a fresh handle for a sentence already stored
;; and `reindex` cannot merge the two, because they are two records.  A KB can hold either
;; without the other — `recover` over a derived-index store builds belief and leaves the
;; index empty — so they are reported separately and each names its own repair.
;;
;; Both are **declared** rather than probed for, and that is the load-bearing decision
;; here.  A probe would have to read "the store holds records and this KB's TMS holds no
;; node" — and that is a true reading of a perfectly healthy KB, because `assert-inert`
;; stores a record and mints no node.  A KB of nothing but inert sentexes is
;; record-for-record and node-for-node identical to one whose belief was never built, so
;; the probe does not merely risk a false positive: on that KB it refuses every write, and
;; the inert store is a shape the engine offers a door for.  Nor would it survive being
;; right — one assert into a KB with no belief gives the TMS its first node and erases the
;; evidence for the refusal it should still be making.
;;
;; So each hazard is a fact about how the KB came to hold what it holds — it opened over a
;; populated store, or a loader filled it and skipped the recover — recorded where that is
;; known: `open-kb` below, and the loader through `note-hazards!`.  What that costs is
;; stated rather than hidden: a KB opened over an **empty** store which another KB then
;; fills has no declaration to make and no way to infer one, so the same two-KB pairing is
;; guarded or unguarded depending on which end opened first.  Belief is per-KB and the
;; second KB's is behind by construction (`open-kb`'s docstring, and
;; `note-default-ram-space!`); a write through the KB that is behind is as unchecked as any
;; other write over an unbuilt network, and only the ordering that lets `open-kb` see the
;; records catches it.

(defn note-hazards!
  "Record which of `{:no-belief :no-index}` hold for this KB — `{:no-belief false}` from
  `core/recover`, `{:no-index false}` from `core/reindex`, and whatever it finds from
  `open-kb`.  A key this does not mention is left as it was.  Returns `kb`.

  Also, and necessarily, the seam an **importer** declares itself through: a load that
  lands records and skips the recover (`:belief? false`, `:belief? :stored`) leaves
  exactly this state in a KB that opened over an empty store, and nothing downstream can
  work that out by reading — a records-only foreign load's store is byte-for-byte the
  store a KB of `assert-inert` sentexes has.  Such a load says `{:no-belief true}` here."
  [kb hazards] (swap! (:unrecovered kb) into hazards) kb)

(defn write-hazards
  "What about this KB makes a write into it wrong, as a map of the hazards that hold —
  `{:no-belief true}`, `{:no-index true}`, both, or `{}` when neither does.  The write
  doors read it (`core/check-writable!`); the read doors do not, since a read over an
  unbuilt derived state answers nothing and can simply be re-asked.

  Reports what was **declared** — by `open-kb` over a store that was already populated,
  by a loader through `note-hazards!` — and retires what `recover` / `reindex` have
  since built.  It infers nothing, for the reason above the seam: the state a probe
  could see is indistinguishable from a supported arrangement, and this one is a fact
  about the KB's history rather than about the current shape of two data structures.

  **A standing hazard is confirmed against the store still holding something**, and reads
  as absent while it does not.  Every hazard here is a claim about stored records, so an
  empty store has nothing for one to be true of: there is no unbuilt belief over no
  records, and the first assert into an empty store builds the network as it goes.

  **The read does not retire the declaration**, which is the difference between reading
  the hazard and clearing it.  An importer declares `{:no-belief true}` *before* its first
  write, so that it holds for the whole load including one that throws part-way
  (`io.import`), and at that moment the store is still empty — a read that cleared the
  latch there would release the declaration for good and hand the finished load a KB whose
  records are unbuilt and whose hazard is gone.  So the emptiness decides the answer and
  nothing else, and retiring it is `discharge-over-empty-store!`'s, on the one event that
  distinguishes the two cases.  Only ever asked when something is claimed: the healthy
  answer reads the atom and no store."
  [kb]
  (let [held (into {} (filter (comp true? val)) (dissoc @(:unrecovered kb) :announced?))]
    (cond
      (empty? held)                                   {}
      (some? (cap/some-sentex-id (:records kb)))      held
      :else                                           {})))

(defn discharge-over-empty-store!
  "Retire a standing hazard when a **write door is about to write into an empty store**,
  and answer whether one was retired.

  This is the event that tells the importer's declaration apart from a stale one, which a
  read of the atom cannot.  Both look identical — a hazard declared, no records yet — and
  they differ in what happens next: the importer writes its records *around* the write
  doors, at the dump's own handles, so it never arrives here and its declaration stands
  for the whole load.  Anything else that emptied the store and is now asserting is
  building this KB's network as it goes, and the hazard it would otherwise inherit is a
  claim about records that are gone.

  Discharging it here rather than at each wipe is what keeps the rule in one place.  A
  store can be emptied by `p/clear-records!`, which any holder of the store can call —
  `core/clear!` is one route, the suite's fixtures another, the perf harness a third — and
  a rule every caller has to know is one three of them have already got wrong.

  Costs a map read on a KB with no hazard standing, which is every healthy one after its
  first write; the store read behind it is reached only while a hazard stands."
  [kb]
  (let [held (into {} (filter (comp true? val)) (dissoc @(:unrecovered kb) :announced?))]
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
  the axis names the representation, `backend-axes` has already held it to `:disk` records
  — the one store that can compute the fingerprint an image is stamped with — and no other
  pairing has an image to write, since `:disk-log` persists its index outright.

  The platform read still runs, and it throws rather than answering false
  (`index-snapshot/enabled?`): an operator who named a backend this platform cannot serve
  has asked for something it will not get, which is the same class of refusal
  `backend-axes` makes one line up."
  [_rkind ikind]
  (and (= :snapshot ikind) (snapshot/enabled?)))

(defn- register-index-snapshot!
  "Arrange for `dir`'s index image to be written when the directory closes.  Registered
  for every KB in snapshot mode, not only one that read an image: a KB that *rebuilt* its
  index is precisely the one worth snapshotting afterwards, and a freshly loaded one has
  no image to have read."
  [dir istore rstore]
  ;; the cadence clock starts here, saying there is no image yet: `map-index-snapshot!`
  ;; corrects it when one maps, and a directory that has never held one is left drifting
  ;; from zero, which is what makes its *first* image happen mid-life rather than at a
  ;; close it may never reach.
  (snapshot/note-no-image! dir)
  (disk/register-index-snapshot!
   dir (fn [] (snapshot/save! dir istore #(drs/slot-fingerprint rstore)))))

(defn- map-index-snapshot!
  "Try to map `dir`'s index image into `istore` instead of rebuilding it — the decision
  map (`{:index :mapped}` or `{:index :rebuild :reason r}`)."
  [dir istore rstore]
  (snapshot/load! dir istore #(drs/slot-fingerprint rstore)))

(defn open-kb
  "Construct a KB — the implementation behind `vaelii.core/open-kb`, which owns the
  user-facing docstring.  `:backend` (`:memory` default) names a record/index store
  pair, or `:records` / `:index` select the two axes independently; `:tms`
  (`:dense` default, or `:reference`) selects the truth-maintenance representation.

  `recover-fn` and `reindex-fn` are injected by the caller: both rebuild through the
  whole engine stack (taxonomy, TMS, settle), which sits *above* this namespace, so they
  arrive as arguments rather than as a require that would close the layering cycle this
  namespace exists to break.  `reindex-fn` is `core/reindex` — rebuild the index from
  the records, *then* recover — which is what a derived index over a durable record
  store needs: `recover` alone reads the index it is recovering from
  (`special/rebuild-taxonomy` reads the functor root), so over an empty one it would
  rebuild an empty taxonomy and report nothing wrong."
  ;; `:recover? :auto` is the default because the alternative is a wrong answer rather
  ;; than an error: under `:warn` a reopened store hands back a fully functional KB whose
  ;; `isa?` answers false and whose queries answer `[]`, with nothing on the returned
  ;; value for a caller to detect and a single `:warn` log as the only signal — and the
  ;; `:test` profile floors logging at `:error`, so that signal is invisible exactly
  ;; where it matters most.  The mirror case below (a derived index describing records
  ;; that are gone) repairs first and logs after, and this branch agrees with it.
  ;; `:warn` and `false` are there for a caller that wants one of them, spelled out.
  [{:keys [space recover? tms naming constraints]
    :or   {space 0 recover? :auto tms :dense naming :strict}
    :as   opts}
   recover-fn reindex-fn]
  ;; The build's switches, before the KB's own options: a JVM property is read on a
  ;; worker thread or at a `def`, so this is the earliest door where a wrong value can
  ;; still be reported as the typo it is rather than as a fsync tick that logs a class
  ;; name (`config/check!`).
  (config/check!)
  (check-opts! opts "open-kb")
  (check-naming! naming)
  ;; **No default here, and nil is not one.**  An unstated policy means the caller said
  ;; nothing, which `checks/arbitrating?` answers from the process default — so a
  ;; `binding` and `VAELII_ARBITRATE_CONSTRAINTS=1` still move a KB that did not ask.
  ;; Defaulting to `:refuse` here would make every KB state a policy and silently take
  ;; the var out of the picture.
  (when (some? constraints) (check-constraints! constraints))
  (doseq [half [:base :overlay]]
    (when-let [sub (get opts half)]
      (check-opts! sub (str half))
      (check-mount-opts! sub (backend-axes sub) (str half))))
  ;; A fork's own writable half needs bookkeeping beside its records (`mount/meta-kv`),
  ;; which exists for `:memory` and `:disk` and not for a server.  Refused **here**, at the
  ;; door, rather than where `meta-kv` says no: by then `open-kb` has already built the
  ;; overlay's record store — a live connection pool, registered for durability — and its
  ;; index half, which takes the directory's exclusive lock.  No KB value is returned from
  ;; a throw at that point, so neither is closeable and the directory is unopenable for the
  ;; life of the JVM.
  (when-let [ov (:overlay opts)]
    (when (= :pg (:records (backend-axes ov)))
      (throw (ex-info (str "a fork's own records cannot be :pg — an overlay keeps tombstones "
                           "and released premise marks beside its records, and that "
                           "bookkeeping is written for :memory and :disk.  Fork onto one of "
                           "those; a :pg KB can still be the frozen base.")
                      {:type :unknown-backend :records :pg :half :overlay}))))
  (let [recover?                      (check-recover! recover?)
        {rkind :records ikind :index} (backend-axes opts)
        _                             (check-mount-opts! opts {:records rkind :index ikind}
                                                         "open-kb")
        _                             (note-default-ram-space! opts rkind)
        overlay?                      (or (= :overlay rkind) (= :overlay ikind))
        base                          (when overlay? (resolve-base opts))
        ov-opts                       (:overlay opts {})
        {ovr :records ovi :index}     (when overlay? (backend-axes ov-opts))
        ;; The fork's own half and its base resolving to one store — one `:disk`
        ;; directory `store-for` shares per canonical path, or one memory space the
        ;; registry shares per number — is base immutability off with no error:
        ;; `FrozenRecords` guards only the calls routed through it, and the fork's
        ;; writes go to the same state direct.  Refused on the *descriptors* when the
        ;; base arrives as opts (before anything opens), and on store identity as the
        ;; backstop when it arrives as `:base-stores`.
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
        own-rstore (when (= :overlay rkind) (record-store-for ovr ov-opts))
        own-istore (when (= :overlay ikind) (first (index-store-for ovi ovr ov-opts)))
        _ (when (or (and own-rstore (identical? own-rstore (:records base)))
                    (and own-istore (identical? own-istore (:index base))))
            (throw (ex-info (str "the fork's own half and its base resolve to one store —"
                                 " the "
                                 (if (and own-rstore (identical? own-rstore (:records base)))
                                   "records"
                                   "index")
                                 " half of the fork is the store its base mounts, and a"
                                 " fork cannot write its own base.  Open that half on its"
                                 " own :dir or :space under :overlay, or pass"
                                 " :base-stores from a different KB")
                            {:type :base-is-overlay})))
        rstore  (if (= :overlay rkind)
                  (mount/mount-records own-rstore
                                       (:records base)
                                       (mount/meta-kv ovr ov-opts))
                  (record-store-for rkind opts))
        [istore index-durable?]
        (if (= :overlay ikind)
          ;; A fork's merged index opens populated exactly when its base's did, so what
          ;; the recovery branch below needs to know is simply whether the merged view
          ;; holds anything — which the trie's own root count answers in O(1), and
          ;; answers correctly whether the base index was durable or derived-and-built.
          (let [merged (mount/mount-index own-istore (:index base))]
            [merged (pos? (long (p/count-at merged [])))])
          (index-store-for ikind rkind opts))
        snapshot? (snapshot-mode? rkind ikind)
        ;; Resolved once, and read twice: the directory `close!` releases, and — on a KB
        ;; whose index is the image — the one the write door hands the cadence.  The
        ;; resolution is a `realpath`, so doing it here rather than per call is the whole
        ;; of what keeps the cadence gate off the other backends' write path.
        kb-dir (cond
                 (or (= :disk rkind) (= :disk-log ikind))
                 (disk/canonical-dir (disk/disk-dir opts))

                 (and (= :overlay rkind) (= :disk ovr))
                 (disk/canonical-dir (disk/disk-dir ov-opts)))
        ;; by name rather than positionally: seventeen `(atom {})`s in a row is a
        ;; miscount waiting to happen, and a miscount here hands one subsystem another's
        ;; state with nothing to notice it — every field is an atom, so the shapes do not
        ;; even disagree until something reads one.
        kb (map->KB {:records rstore
                     :index   istore
                     ;; The directory `close!` releases, when the records are durable.
                     ;; A fork's is its **own** writable half's: that directory takes the
                     ;; same exclusive lock and holds the same file handles, so without
                     ;; this a durable fork could never be handed to another process
                     ;; short of exiting the JVM.  The base's directory is not this KB's
                     ;; to release — it is mounted read-only and shared by every fork
                     ;; over it, which is exactly why nothing here names it.
                     ;; The durable **index** puts a directory here too, even when the
                     ;; records are elsewhere: `:pg-disk-log` writes its index under
                     ;; `:dir` and takes that directory's exclusive lock on open, and
                     ;; without this `close!` would leave the lock held for the JVM's life
                     ;; over a KB whose records are on a server.
                     :dir     kb-dir
                     ;; ...and the same directory again, for the KB whose index is the
                     ;; mapped image and only that one.  The write door's gate on the
                     ;; cadence is a nil check on this field, so every other durable
                     ;; backend pays a field read per assert and nothing else.
                     :snapshot-dir (when snapshot? kb-dir)
                     :tms     (create-tms tms)
                     :taxonomy (tax/create-taxonomy)
                     :provers  (atom provers/default-provers)
                     :solver   (atom solve/local-solver)
                     ;; The settle's two readings and the memo it rebuilds them from,
                     ;; in **one** atom because they are one publication: `record-clashes!`
                     ;; derives all three from a single pass and installs them together,
                     ;; and `core/conflicts` / `core/contradictions` are read doors a
                     ;; thread beside the writer may call at any moment.  Three atoms
                     ;; would let such a reader land between two of the resets and take
                     ;; one settle's conflicts beside another's contradictions — a reading
                     ;; of no state the KB was ever in (`settle/record-clashes!`).  Not
                     ;; `:clashes` below, which is the definitional-pair memo rather than
                     ;; a reading of one.
                     :clash-readings (atom {:reports {} :conflicts [] :contradictions []})
                     :program   (atom nil)
                     :violations (atom [])
                     :recheck   (atom {})
                     ;; `{rule-handle -> #{refusal} | :overflow}` — the firings
                     ;; `chain/place-conseq` declined to place because a re-checkable
                     ;; block condition already held.  A blocked justification is how
                     ;; the engine remembers a suppressed firing, and a *refused* one
                     ;; never becomes a justification at all, so it needs the same
                     ;; memory one level earlier (docs/exceptions.md, "A refused firing
                     ;; is remembered as bindings").  Derived state, in memory beside
                     ;; `jtms/blocked` rather than in it: these are not justifications
                     ;; and must never be labelled.
                     :refused   (atom {})
                     :settle-stats (atom {:iterations 0 :passes 0 :histogram {}})
                     :chain-stats  (atom {:runs 0 :last nil})
                     :opposed   (atom #{})
                     ;; `{[P R] -> how many sentexes declare it}` — the argument-preservation
                     ;; declarations, as storage.  `settle/preserving-nogoods` reads it as
                     ;; its gate and as its vocabulary, and the point of the roster is that
                     ;; both reads cost **nothing off the index**: a KB that declares no
                     ;; preservation — which is nearly every KB — is told so by one
                     ;; `empty?`, where `inherit/declarations-exist?` is two cardinality
                     ;; reads and would land on the assert path once per settle.  Kept at
                     ;; the same two choke points as `:opposed`, from the sentence's shape
                     ;; alone, and rebuilt by `recover` for the same reason.
                     ;; Reference-counted rather than a set: one declaration stated in two
                     ;; contexts is two sentexes, and the first retraction must not retire
                     ;; what the second still says.
                     :preserving (atom {})
                     ;; The candidates `settle/preserving-nogoods` reported a clash for
                     ;; last settle, so a standing report survives an unrelated assert:
                     ;; `conflicts` and `contradictions` are recomputed from scratch every
                     ;; settle and the region is only what that settle moved.  `:clashes`
                     ;; beside it does the same job for the definitional pairs; this holds
                     ;; one handle rather than a pair, since the other side of an
                     ;; inherited clash is not a sentex.
                     :preserved-clashes (atom #{})
                     ;; `{context -> {except-handle -> hidden-handle}}` — which stored
                     ;; `(except (sentexHandle H))` facts sit in which context, so a
                     ;; reader takes the visible ones off the map rather than fetching
                     ;; every except record in the KB.  Kept at the same two choke
                     ;; points as `:opposed`, and rebuilt by `recover` for the same
                     ;; reason: it is derived from storage and no store holds it
                     :excepted  (atom {})
                     ;; How many stored excepts target another except's handle.  When
                     ;; zero, `except-in-force?` is trivially true for every except
                     ;; and `excepted-handles` can skip the cascade entirely.  Maintained
                     ;; at the same choke points as `:excepted` and rebuilt by `recover`.
                     :meta-except-count (atom 0)
                     ;; `{antecedent-key -> how many rules take it}` — the roster
                     ;; `special/visibility-seeds` enumerates instead of walking a context
                     ;; cone.  A key is a predicate, or `[:not pred]` for a negated
                     ;; antecedent (`rules/antecedent-key`).  Kept O(1) at the rule
                     ;; index/unindex choke points, exactly as `:opposed` is kept at the
                     ;; store's, and rebuilt by `rebuild-rule-roster!` — recovery replays
                     ;; belief and the taxonomy, never rule indexing, so nothing else puts
                     ;; it back.  Reference-counted rather than a set: two rules on one
                     ;; antecedent must not have the first retraction retire the predicate
                     ;; the second still reads.
                     :rule-antecedents (atom {})
                     ;; `{context -> how many rules are stated there}` — the other half
                     ;; of the same question: an edge only needs seeding when one side
                     ;; holds a rule that could newly reach the other side's facts, and
                     ;; wiring an empty context under a full one holds none.  Kept and
                     ;; rebuilt with the roster above, in the same two places.
                     :rule-contexts (atom {})
                     :negations (atom {})
                     :clashes   (atom {})
                     ;; `#{#{x y} …}` — the sibling-disjointness exception pairs a retract
                     ;; just removed, posted at the disintegrate choke point.  Retracting
                     ;; an exception that was present ab initio re-arms a clash the pair
                     ;; never entered the clash set as, so the settle's re-arm sweep reads
                     ;; this to drive `two-sided-reach` over each departed pair, then
                     ;; `settle-finish` clears it.  Belief-quiet asserts never post to it.
                     :sib-exc-dirty (atom #{})
                     ;; the equality state `special/refresh-supersessions` last
                     ;; reconciled the superseded set against (`special/supersession-stamp`).
                     ;; nil means "not reconciled yet", which reads as *reconcile
                     ;; everything* — the same shape `:closures` uses, and the same
                     ;; direction: a stamp that cannot be compared costs a full pass and
                     ;; never a wrong answer
                     :supersessions (atom nil)
                     :qcn       (atom {})
                     ;; the join baselines beside the network cache, never inside it:
                     ;; the resident cache clears wholesale at its bound, and a baseline
                     ;; is bookkeeping whose loss degrades every later delta join to a
                     ;; full one — bounded by (calculi × reader contexts), not by reads
                     :qcn-joined (atom {})
                     :matches   (atom {})
                     ;; one shape, not a map of stamped entries: every entry in it is
                     ;; retired by the same clock move, so the stamp belongs to the map
                     ;; (`provers/closure-answers`)
                     :closures  (atom {})
                     :feed      (feed/create-feed)
                     ;; a plain value, not an atom: which conventions the front door
                     ;; holds content to is settled when the KB is opened, and a store
                     ;; whose policy moved under it would hold two vocabularies with
                     ;; nothing recording which sentence arrived under which
                     :naming    naming
                     ;; likewise, and nil on purpose — the caller said nothing, so
                     ;; `checks/arbitrating?` reads the process default
                     :constraints constraints
                     ;; empty rather than `{:no-belief false :no-index false}`: a key
                     ;; absent means *nobody has asked yet*, which is not the same
                     ;; answer as "no".  The store is not populated until the branch
                     ;; below runs (or an import fills it after this open returns), so
                     ;; the belief half is settled by whoever first needs it and the
                     ;; index half by this open — see `write-hazards`
                     :unrecovered (atom {})})]
    ;; Taxonomy owns derived structures; the KB owns whether one recorded supporter
    ;; is believed and visible from a reader after context-scoped exceptions.  Install
    ;; the seam only after the mutually-referential KB exists, and before recovery can
    ;; ask any scoped cache question.
    (tax/install-supporter-visibility!
     (:taxonomy kb)
     #(seq @(:excepted kb))
     (partial res/supporter-believed? kb))
    (when snapshot? (register-index-snapshot! (disk/disk-dir opts) istore rstore))
    ;; **Whose records is this index of?**  For `:disk` records the question cannot arise —
    ;; the index and the records are one directory.  For `:pg` they are a directory and a
    ;; database, joined by nothing but this opts map, so the directory is stamped with the
    ;; database identity on first use and a later open over a *different* one is refused
    ;; rather than answered.  The coverage check below cannot stand in for it: that compares
    ;; record *counts*, and two unrelated stores of the same size agree — after which
    ;; handles resolve to the wrong sentences and a re-assert mints a second handle for a
    ;; sentence already stored, which is the duplicate-canonical-form hazard the trie exists
    ;; to prevent.
    (when (and (= :disk-log ikind) (not= :disk rkind))
      (let [root  (str (disk/disk-dir opts) "/index")
            ident (pg-identity (:pg opts))
            seen  (dfiles/records-identity root)]
        (cond
          (nil? seen) (dfiles/stamp-records-identity! root ident)
          (not= seen ident)
          (throw (ex-info (str "the durable index at " root " was built against "
                               (pr-str seen) " and this KB's records are " (pr-str ident)
                               ".  An index is derived from records, so one store's index"
                               " cannot answer another's reads.  Give this KB its own :dir,"
                               " or delete that index directory to rebuild it from these"
                               " records.")
                          {:type :stale-index-records :dir root
                           :stamped seen :records ident})))))
    ;; The durable index is gated on its key-layout sentinel before anything reads
    ;; it: a log written under another `kv/index-layout-version` replays cleanly and
    ;; then misses every read whose key shape moved — populated-looking counts over
    ;; queries that answer nothing.  A stale stamp clears the index and rebuilds it
    ;; from the records, `recover?` notwithstanding: an index this open just cleared
    ;; is one this open must repopulate.  The stamp lands only after the rebuild
    ;; (`dfiles/index-layout-decision` for the crash story).
    (when (and (= :disk-log ikind)
               ;; The index kind, not `index-durable?`: on the `:overlay` axis that
               ;; flag says the *merged view holds something*, and a fork inherits no
               ;; `:dir`, so `disk/disk-dir` synthesizes the same default directory a
               ;; bare `{:backend :disk-log}` uses.  Gating on it clears the fork's merged
               ;; index and stamps a directory this open never read.  A base mounted
               ;; under `:base` is held to the sentinel by `gate-base-index-layout!`,
               ;; which is the one place a fork's inherited half is checked.
               (.isDirectory (java.io.File. (str (disk/disk-dir opts) "/index"))))
      (let [root     (str (disk/disk-dir opts) "/index")
            decision (dfiles/index-layout-decision
                      root kv/index-layout-version
                      (pos? (long (p/count-at istore []))))]
        (case decision
          ;; a fresh directory needs the stamp and no rebuild; this KB owns it, so
          ;; this is where the write `index-layout-decision` refuses to make happens
          :unstamped (dfiles/stamp-index-layout! root kv/index-layout-version)
          :stale (do
                   (dfiles/mark-index-rebuilding! root)
                   (p/clear-index! istore)
                   (let [t0 (System/nanoTime)
                         {:keys [sentexes rules]} (reindex-fn kb)
                         ms (/ (- (System/nanoTime) t0) 1e6)]
                     (dfiles/stamp-index-layout! root kv/index-layout-version)
                     (trove/log! {:level :warn :id ::index-layout-rebuilt
                                  :msg (format "the durable index at %s was written under another key layout — rebuilt from %d records (%d rules) in %.0f ms"
                                               (disk/disk-dir opts) (long sentexes) (long rules) ms)})))
          nil)
        ;; The layout gate above answers "are these the right *keys*"; it says nothing
        ;; about whether the index describes all the records, and a short one opens clean
        ;; and answers short forever.  Three ways in, none of them exotic: a torn `kv.log`
        ;; tail (the record log and the index log are separate files with separate
        ;; fsyncs, and truncating a torn tail is what recovery is *designed* to do), a
        ;; directory grown under a derived-index mode — `:disk-dense` writes nothing under
        ;; `<dir>/index`, so reopening it as `:disk-log` finds an empty durable index over
        ;; full records — and a crash between the record write and the index batch.
        ;;
        ;; The failure is silent and compounding: reads answer out of a populated-looking
        ;; store, and re-asserting a fact the index cannot find mints a **second handle**
        ;; for a sentence already stored, which is the duplicate-canonical-form hazard the
        ;; whole trie exists to prevent.  Coverage is exact — the root count equals the
        ;; live record count on a healthy store, rules, negations and exceptWhen metas
        ;; included — so it is compared rather than sampled, and repaired like a stale
        ;; layout: rebuild from the records, which are the truth an index is derived from.
        ;; Gated on `recover?`, where the layout gate is not: a layout mismatch means the
        ;; keys cannot be read at all, while `:recover? false` is a caller saying "open
        ;; this and read what is stored, do no work" — and the one-directional crossing
        ;; from a derived-index mode is a migration they drive with an explicit `reindex`.
        ;; `:auto`, the default, is where a short index is a fault rather than a choice.
        (when (and recover? (not= :stale decision))
          ;; Three instruments, because the three ways a short index arrives leave
          ;; different survivors.  The **batch-seal counter** is the last op of every
          ;; index batch, so a torn append-mode tail — which keeps a batch's prefix,
          ;; the root count `count-at []` reads included — loses it first; zero means
          ;; the index predates the counter or arrived by `index-load` replay, and the
          ;; root count is the check that remains.  The **damaged flag** is the clean
          ;; marker's length disagreeing with the file: a compacted log is one flat
          ;; `[:put]` per key in hash order, so a lost tail is arbitrary keys — the
          ;; seal may survive and the counts may still agree, and only the length says
          ;; the file is not the one that was closed.
          (let [indexed  (long (p/count-at istore []))
                sealed   (long (p/count-at istore kv/sealed-prefix))
                damaged? (boolean (:damaged (:backend istore)))
                ;; the record count, not the roster: on a store whose enumeration is a
                ;; query this is the difference between one row and the whole table, and
                ;; the coverage gate asks it on every open (`p/Tallying`).
                stored   (cap/count-sentexes (:records kb))]
            (when (or damaged?
                      (if (pos? sealed) (not= sealed stored) (not= indexed stored)))
              (dfiles/mark-index-rebuilding! root)
              (p/clear-index! istore)
              (let [t0 (System/nanoTime)
                    {:keys [sentexes rules]} (reindex-fn kb)
                    ms (/ (- (System/nanoTime) t0) 1e6)]
                (dfiles/stamp-index-layout! root kv/index-layout-version)
                (trove/log! {:level :warn :id ::index-coverage-rebuilt
                             :msg (format "the durable index at %s described %d of %d records%s — rebuilt from %d records (%d rules) in %.0f ms"
                                          (disk/disk-dir opts)
                                          (if (pos? sealed) sealed indexed) stored
                                          (if damaged? " (and its log is shorter than its clean marker recorded)" "")
                                          (long sentexes) (long rules) ms)})))))))
    ;; A durable fork's **own** index half is held to the same gates as a plain
    ;; `:disk-log` index — the layout sentinel, and the coverage instruments under
    ;; `recover?`.  The merged mount above answers reads, but what lives in
    ;; `<fork-dir>/index` is only what the fork itself wrote: a layout bump would
    ;; silently misread it (the base gets a clean `:stale-index-layout` refusal from
    ;; `gate-base-index-layout!`; this half is the fork's own to stamp and rebuild),
    ;; and a torn tail would silently shorten it.
    ;;
    ;; **Both the instruments and the repair go through the merged mount, never the
    ;; own half alone.**  The own half is not an index of the fork's own records: it is
    ;; the fork's *delta* over the base in the overlay's merge model
    ;; (`vaelii.impl.overlay.kv`) — copy-on-write counters holding base+net, tombstones
    ;; and removal records for what the fork took out of inherited postings — so its
    ;; counters read against the fork's own record count disagree on every healthy
    ;; fork that has written anything, and clearing it and reindexing the own records
    ;; into it would drop every removal (an inherited fact the fork retracted would
    ;; reappear) and leave own-only absolute counters shadowing the base's.  Read
    ;; through the mount, the seal and the root count are the merged index's and
    ;; compare against the merged records, exactly as on a plain `:disk-log` KB; and the
    ;; rebuild is the one `reindex` makes on any fork — `kv-clear!` on the mount sets
    ;; `::cleared` (the base reads absent from then on) and the merged records reindex
    ;; into the own half as absolute entries, which the merged view serves unchanged.
    (when (and own-istore (= :disk-log ovi)
               (.isDirectory (java.io.File. (str (disk/disk-dir ov-opts) "/index"))))
      (let [root     (str (disk/disk-dir ov-opts) "/index")
            decision (dfiles/index-layout-decision
                      root kv/index-layout-version
                      (pos? (long (p/count-at own-istore []))))]
        (case decision
          :unstamped (dfiles/stamp-index-layout! root kv/index-layout-version)
          :stale (do (dfiles/mark-index-rebuilding! root)
                     (let [{:keys [sentexes rules]} (reindex-fn kb)]
                       (dfiles/stamp-index-layout! root kv/index-layout-version)
                       (trove/log! {:level :warn :id ::fork-index-layout-rebuilt
                                    :msg (format "the fork's own index at %s was written under another key layout — rebuilt the merged index from %d records (%d rules)"
                                                 root (long sentexes) (long rules))})))
          nil)
        (when (and recover? (not= :stale decision))
          (let [stored   (cap/count-sentexes (:records kb))
                sealed   (long (p/count-at istore kv/sealed-prefix))
                indexed  (long (p/count-at istore []))
                damaged? (boolean (:damaged (:backend own-istore)))]
            (when (or damaged?
                      (if (pos? sealed) (not= sealed stored) (not= indexed stored)))
              (dfiles/mark-index-rebuilding! root)
              (let [{:keys [sentexes rules]} (reindex-fn kb)]
                (dfiles/stamp-index-layout! root kv/index-layout-version)
                (trove/log! {:level :warn :id ::fork-index-coverage-rebuilt
                             :msg (format "the fork's merged index described %d of %d records through its own half at %s%s — rebuilt from %d records (%d rules)"
                                          (if (pos? sealed) sealed indexed) stored root
                                          (if damaged? " (whose log is shorter than its clean marker recorded)" "")
                                          (long sentexes) (long rules))})))))))
    (cond
      ;; A **derived** index opens empty over records that are not, so the repair is
      ;; one step longer than `recover`: rebuild the index from the records first, then
      ;; recover the TMS and taxonomy from both.  That ordering *is* `core/reindex`.
      (some? (cap/some-sentex-id (:records kb)))
      (do
        (when recover?
          (if (= :auto recover?)
            (if index-durable?
              (recover-fn kb)
              ;; A derived index is rebuilt from the records here — unless a **mapped
              ;; snapshot** of it survives and still describes them, in which case the
              ;; rebuild is replaced by reading its bytes back
              ;; (`vaelii.impl.disk.index-snapshot`).  The stamp decides; a snapshot that
              ;; fails any part of it falls back to exactly the rebuild below, which is
              ;; always legal because the index is derived state.
              (let [snap (when snapshot?
                           (map-index-snapshot! (disk/disk-dir opts) istore rstore))]
                (if (= :mapped (:index snap))
                  (recover-fn kb)
                  ;; O(records), paid on every open — the standing cost of not persisting
                  ;; the index, and the number that decides whether persisting a snapshot
                  ;; of one is worth it, so it is reported rather than absorbed silently
                  (let [t0 (System/nanoTime)
                        {:keys [sentexes rules]} (reindex-fn kb)
                        ms (/ (- (System/nanoTime) t0) 1e6)]
                    ;; **`:warn` when the backend was named for its image.**  A
                    ;; `:disk-columnar` KB rebuilding is doing what its name says, and the
                    ;; line is a measurement.  A `:disk-snapshot` KB rebuilding has just
                    ;; paid the cost the operator selected that name to avoid, and the
                    ;; reason is the one thing they can act on — so it is a warning that
                    ;; names the mismatch class, not an info line they will read after the
                    ;; hour is gone.
                    (trove/log! {:level (if snapshot? :warn :info) :id ::reindexed-on-open
                                 :msg (format "rebuilt the derived index from %d records (%d rules) in %.0f ms%s"
                                              (long sentexes) (long rules) ms
                                              (cond
                                                (and snapshot? snap)
                                                (str " — the :snapshot index found no usable image ("
                                                     (name (:reason snap)) "), so this open paid the"
                                                     " rebuild the backend is named to skip")
                                                snap (str " — no usable index snapshot ("
                                                          (name (:reason snap)) ")")
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
        ;; The **write** side, settled here and only here: this is the one place that
        ;; knows the store was already populated when this KB opened, and it reads what
        ;; the dispatch above actually left rather than which arm it took — a mapped
        ;; index snapshot populates the derived index without a `reindex`, and a
        ;; `:recover? :warn` recovers nothing at all.
        (note-hazards! kb {:no-belief (not (jtms/any-node? (:tms kb)))
                           :no-index  (zero? (long (p/count-at (:index kb) [])))})
        ;; ...and saying so, which `{:recover? false}` was silent about entirely.  The
        ;; warning above describes what a *read* gets, and `false` asks not to hear it —
        ;; a caller managing recovery itself already knows.  What that caller could not
        ;; know is that the same state is not a read-only one: writes into it are refused
        ;; by name, which is a different fact with a different repair, and this is the
        ;; only moment before the refusal at which it can be said.  At `:info`, so
        ;; `{:recover? false}` stays as quiet as it promised at `:warn` and above.
        (when-let [hz (seq (write-hazards kb))]
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

      ;; The mirror case, and the more dangerous one: a derived index holding entries
      ;; for records that are *gone*.  Such an index is shared for the life of the JVM
      ;; under the identity of the records it is derived from, so a store emptied out
      ;; from under it (a directory closed, deleted and reopened) leaves it describing
      ;; nothing — resolving handles to no record and answering `find-or-create` with a
      ;; dead one.  It is derived state and the records are the ground truth, so it is
      ;; simply dropped — **whatever `recover?` says**.  `{:recover? false}` asks for
      ;; silence about an unrecovered store, not for an index that answers out of
      ;; records nobody holds, and the drop is what docs/storage.md promises happens on
      ;; the next open.
      (and (not index-durable?) (pos? (p/count-at (:index kb) [])))
      (do (p/clear-index! (:index kb))
          (trove/log! {:level :warn :id ::stale-derived-index
                       :msg (str "dropped a derived index left over from an earlier life of "
                                 "this record store — the records it describes are gone")})))
    kb))

(def equality-predicates
  "The relations that assert a merge — `vaelii.impl.special` is where they are
  acted on, but stratification (`vaelii.impl.checks`) needs the set too.  `different`
  is not among them: it *reads* the closure and is never stored (see
  `vaelii.impl.wff`)."
  '#{rewriteOf sameAs equals})

;; ---- type queries -------------------------------------------------------

(defn- exists-in?
  "Does the ground `sentence` hold in a context visible from `context` (its genlCx
  up-closure; a variable context means any context)?"
  [kb sentence context]
  (boolean (seq (res/matches-visible kb sentence context))))

(defn find-sentexes
  "Every stored sentex that contains `term` anywhere (any position, any nesting).

  An atom is one inverted-index read.  A **compound** is narrowed by the postings of the
  atoms it contains — every sentex holding the compound holds all of them — and each
  candidate is then verified against its own sentence, since that intersection is a
  superset.  So a compound is findable whether or not it earns a key of its own
  (`sentex/*min-indexed-depth*`, `sentex/max-indexed-compound`), and the verify reads the
  record this was going to return anyway.

  A compound holding a **variable** is a pattern rather than a term, and this answers
  nothing for one — `sentexes-matching` is what takes a pattern."
  [kb term]
  (let [t (sx/canon term)]
    (if (and (sequential? t) (not (sx/indexable-term? t)))
      ()
      (cond->> (if (sequential? t)
                 (p/sentexes-with-terms (:index kb) (sx/probe-atoms t))
                 (p/sentexes-with-term (:index kb) t))
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
  argument root.  Scoped to memberships visible from `context` (default: any context).

  `x` is any term, not only an individual: a predicate carries the meta-ontology's
  types (`binaryPredicate`, `instanceRelationPredicate`, …) the same way `Muffet`
  carries `dog`.

  The same three filters `matches-visible` applies, since this *is* the retrieval
  `isa?` and the disjointness check are built on and the two must not disagree about
  what the KB holds: believed, asserted in a context `context` sees, and not hidden
  from it by an `except`.  A negative membership is excluded by the argument test
  rather than by a truth filter — a `(not (T x))` sentex has `not` for its functor and
  `(T x)` for its lone argument, so it is not a unary sentence *about* `x` at all."
  ([kb x] (types-of kb x '?ctx))
  ([kb x context]
   (let [recs     (:records kb)
         tms      (:tms kb)
         visible? (if (sx/variable? context)
                    (constantly true)
                    (let [up (tax/context-up (:taxonomy kb) context)] #(contains? up %)))
         hidden?  (or (res/hidden-fn kb context) (constantly false))]
     ;; the argument root goes straight to the sentexes holding x in argument
     ;; position 1, instead of every sentex mentioning x anywhere (any position, any
     ;; nesting) — this runs on every unary assert, via disjoint-problem.
     ;;
     ;; The filters are one `keep` rather than a stack of threaded stages: every
     ;; definitional check bottoms out here, the postings are short, and a chain of
     ;; six `filter`/`map` stages allocates six conses per entry to do a few field
     ;; reads.  Lazy, so a caller looking for one type does not pay for a long posting
     ;; — which is also why this is not a transducer: at these lengths `sequence` spends
     ;; more on building the pipeline than the pipeline saves.
     (->> (p/sentexes-with-arg (:index kb) 1 x)
          (keep (fn [h]
                  (when-not (hidden? h)
                    (when-let [s (p/get-sentex recs h)]
                      (when (and (jtms/in? tms (:id s))      ; believed memberships only
                                 (visible? (:context s)))
                        (let [sen (:sentence s)]
                          (when (and (= 1 (nm/arity sen)) (= x (first (nm/args sen))))
                            (nm/functor sen))))))))
          distinct))))

(defn memberships
  "What a term is, as the checks need to ask it: `{:types [t …] :closures [#{…} …]}` —
  the types asserted of `x` and visible from `context`, each paired with its own genl
  up-closure.

  The closures are what make repeated questions free.  `isa? x t` is \"does some type
  `x` holds reach `t`\", and reachability is the *same* edge set read either way — `t' ∈
  specs(t)` iff `t ∈ genls(t')` — so the two directions differ only in what they cost
  here.  `specs(t)` is unbounded in the wrong direction: with `t` = `thing`, the floor
  every `arg` check tests first, it is every type in the KB.  The up-closure of a
  type a term actually holds is one chain, cached, and once read every constraint on
  that term is one set membership."
  [kb x context]
  (let [tax (:taxonomy kb)
        ts  (vec (types-of kb x context))]
    {:types ts :closures (mapv #(tax/genls tax % context) ts)}))

(defn isa-among?
  "Is `t` in one of the genl up-closures a `memberships` read returned?  The subtype
  test, once the retrieval it rests on has been paid for."
  [closures t]
  (boolean (some #(contains? % t) closures)))

(defn isa?
  "Is individual `x` (transitively) of type `t`?  Considers only type memberships
  visible from `context` (default: any context).

  Read `x`'s own memberships and climb from each, rather than matching `(t x)` and
  letting the matcher fan `t` out over its genl spec closure — see `memberships` for
  why that direction is the cheap one.

  A non-symbol `x` has no argument-root posting to read, so it falls back to the
  matcher, which reaches the same facts through the functor extents.

  Lazy in the memberships, so a term with a long posting stops at the first type that
  reaches `t` — `memberships` is the batch form, for a caller that will ask again."
  ([kb x t] (isa? kb x t '?ctx))
  ([kb x t context]
   (if (and (symbol? x) (not (sx/variable? x)))
     (let [tax (:taxonomy kb)]
       (boolean (some #(contains? (tax/genls tax % context) t) (types-of kb x context))))
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
   (tax/reach-strength (:taxonomy kb) rel-key sub super context
                       #(jtms/defeat-class (:tms kb) %))))

(defn membership-reader
  "A `term -> `memberships`` reader, memoized for the life of one caller.

  The definitional checks ask about a handful of terms — the sentence's arguments, and
  its predicate — but ask about each several times over: the arity arm reads the
  predicate's memberships for three spellings of the declaration and again for
  `variableArity`, `arg` reads an argument's twice per constraint on its position,
  and for a unary sentence the disjointness arm wants the very memberships `arg`
  just read.  Each is a posting read plus a record fetch and a belief test per entry,
  and none of it can change underneath one `assert`."
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
  genl edges visible from it?"
  ([kb a b] (tax/disjoint? (:taxonomy kb) a b))
  ([kb a b context] (tax/disjoint? (:taxonomy kb) a b context)))

;; ---- storage helpers ----------------------------------------------------

(defn canon-stamp
  "What a cached handle lookup is valid under: **which KB** it was asked of, and the
  set of predicates declared `symmetric` — the one thing `resolution/kb-sentex` reads
  off the KB, so a lookup memoized under one reading of that set is never served
  under another.  The record store rides in the stamp because `with-handle-cache`
  deliberately reuses an outer run's map: a nested run on a *second* KB (a chaining
  callback asserting elsewhere) shares the cache, and two KBs declaring nothing
  symmetric would otherwise stamp the one shared empty set — KB-B reading KB-A's
  handles."
  [kb]
  [(:records kb) (tax/props (:taxonomy kb) :symmetric)])

;; A forward-chain run binds the handle cache over its whole fixpoint
;; (`chain/chain-all`), so every sentex the run *creates* is cached.  For a functor
;; the store held **no** sentex under when the run began, that makes the cache
;; authoritative: nothing outside the run could have stored one, and everything the
;; run stored is cached, so a cache *miss* is proof of absence — and the trie walk
;; `find-sentex-handle` would otherwise do to reconfirm it (a ~5-level megamorphic
;; walk per novel conclusion, the join pyramid's dominant cost) is pure overhead.
;;
;; This memo records that verdict per functor, decided at the functor's first probe —
;; which is before its first conclusion is placed, so the store still reads zero for a
;; genuinely chain-only functor.  A functor that already held facts reads non-zero and
;; is never trusted (the trie answers it, exactly as before).  Bound only by
;; `chain` (`chain-all`'s fixpoint), and only alongside the handle cache it reasons
;; about; nil for every other caller, so a lone `find-sentex-handle` behaves precisely
;; as it did.
;;
;; **The verdict is only as old as the cache's current filling.**  The handle cache
;; empties itself whenever its stamp moves (`observe/cache-generation`) — a run whose
;; rule concludes `(symmetric P)` moves it mid-fixpoint — and after that the sentexes
;; the run stored before the move are in the store but no longer in the cache, so a
;; miss proves nothing.  The memo therefore records the cache generation it was decided
;; under and drops every verdict when the generation has stepped: the next probe per
;; functor re-reads the store, which now counts what the run stored, and a functor the
;; run already concluded under reads non-zero and goes back to the trie.
;;
;; **Armed only for a bulk frontier** (`chain-authority-min-frontier`).  The probe is a
;; `count-with-functor` read, repaid only when the run concludes *many* facts of the
;; functor so the one read skips many walks.  A large forward-chain earns it — a
;; `forward-chain` seeds every believed sentex, a bulk load or a broad `genl` edge seeds
;; a wide frontier — but an incremental `assert` seeds one fact, concludes a handful, and
;; would pay a probe per assert it could never amortize (worse, a probe that reads
;; non-zero off an *accumulating* conclusion functor and walks anyway).  So `chain` binds
;; the memo only when the seed frontier clears the floor; below it the var stays nil and
;; the assert path costs exactly what it did before the optimization.  A run seeded small
;; that nonetheless fans out wide forgoes the skip — the frontier is a lower bound on the
;; run, not a prediction of it — but that is the cheap-store case where a walk is cheap,
;; and the profiled win (`w4.join`, `find-sentex-handle` 9.95% -> 2.47%) is a single
;; large-seed `forward-chain` the floor passes.
;;
;; **The functor is the store's own root key, not the sentence head**, which is the
;; whole point of asking `count-with-functor` at all: a negative fact roots under its
;; positive body's predicate (`kv/root-keys`, polarity lives in the record), so
;; `(not (believed X))` counts under `believed` and *never* under `not`.  Keying the
;; memo on the sentence head would ask `count-with-functor` about `not` — a functor
;; nothing ever roots under — read zero every time, and declare the cache authoritative
;; for a body the store may well hold, skipping the trie into a duplicate sentex.  So
;; the key is `(sx/body built)`'s functor, computed exactly as `root-keys` does; a rule
;; has no body and no functor-root posting, so the memo declines it and the trie answers.
(def ^:dynamic *chain-authoritative-functors* nil)

(def chain-authority-min-frontier
  "The smallest seed frontier a `chain` run arms the authority memo above for.  Coarse,
  not tuned: it separates an incremental `assert` (a seed of one, plus a few migration
  seeds) from a bulk fixpoint (a `forward-chain`'s whole datum set, a load, a broad edge's
  subsumption seeds), and the memo's benefit is flat across the wide band between them —
  above the floor one probe per functor is repaid by the walks it skips, below it there
  are too few conclusions to repay a probe at all.  Placed here beside the var it gates so
  the mechanism and the policy that arms it read together."
  64)

(def ^:private memo-generation-key
  "Where the authority memo records the handle-cache generation its verdicts were
  decided under — a keyword, so it cannot collide with a functor symbol."
  ::generation)

(defn- functor-cache-authoritative?
  "Is the run's handle cache authoritative for the sentex `built` — did the store hold
  zero sentexes under the functor it roots at when this run first asked, with the cache
  holding everything stored since?  The functor is the store's root key (`(first
  (sx/body built))`, `kv/root-keys`), so a negative asks about its body's predicate
  rather than `not`.  Memoized in `*chain-authoritative-functors*` (a mutable map bound
  by `chain-all`) per handle-cache generation under `stamp`: a generation that stepped
  since the verdicts were recorded means the cache was emptied, so the verdicts are
  dropped and each functor is re-probed against a store that now counts what the run
  stored.  A nil var (no run, or no cache) answers falsey, leaving the caller on the
  trie — as does a `built` with no functor-root posting (a rule, or a non-symbol-headed
  body)."
  [kb stamp built]
  (when-let [^java.util.Map memo *chain-authoritative-functors*]
    (when-let [gen (observe/cache-generation stamp)]
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
  "Which of the sentexes at `built`'s own trie leaf stores exactly it, or nil.

  The leaf is the whole candidate set and never more.  A sentex's key is its sentence
  α-renamed with the context appended (`sentex/key-tokens`), so anything sharing this
  sentence and context shares this leaf, and anything at another leaf is by construction
  another sentence — which is why this reads `p/leaf-at` rather than matching `p/lookup`.
  A variable in the path is a *wildcard* to `lookup`: it fans over every stored sentex of
  the same shape, and this would then read the record of each, at one positional read and
  one nippy thaw apiece on a paged store.  `handle-of` and `why-not` are public, so the
  pattern is the caller's to choose.

  A ground sentence keys the trie exactly, so its leaf holds its own handle alone and the
  first candidate is the answer with no record read.  A sentence with variables α-renames,
  so its leaf can still hold sentexes of the same *shape* naming other variables (two
  `exceptWhen` exceptions on one rule differing in which rule variable they name, a
  `defn*` condition with its variables transposed); for those the stored sentence decides,
  one record read per sentex at that leaf.  Only a non-ground Literal pays it: a rule's key
  is its canonical form whole — α-renamed literals, never a bare variable token — so the
  trie answers it exactly."
  [kb built handles]
  (if (or (some? (:antecedent built)) (sx/ground? built))
    (first handles)
    (let [sentence (:sentence built)]
      (some (fn [h]
              (when (= sentence (:sentence (p/get-sentex (:records kb) h))) h))
            handles))))

(defn find-sentex-handle
  "The handle of an existing sentex for `sentence` in `context`, or nil.  A **ground**
  symmetric literal also probes its mirror, so a fact stored before its `symmetric`
  declaration is still found (and re-asserting the mirror image resolves to it rather
  than storing a duplicate).  A sentence **with variables** is found by its stored
  sentence, not by its trie key alone: the key α-renames, so the sentexes at that key's
  own leaf share the sentence's shape and `stored-at` picks the one that *is* it.

  Every probe here is `p/leaf-at` — the **exact** leaf — never `p/lookup`: dedup asks
  where *this* sentence is stored, and a match would fan a caller-supplied variable over
  every stored sentex of that shape (`stored-at`)."
  [kb sentence context]
  (let [stamp (canon-stamp kb)]
    (or (observe/cached-handle stamp sentence context)
        (let [built  (res/kb-sentex kb sentence context)]
          ;; The run cache already answered "no", and for a chain-authoritative functor
          ;; that "no" is final — skip the trie.  Guarded on the queried spelling being
          ;; the canonical one: if canonicalization moved it (a symmetric literal sorted,
          ;; an α-rename, a fold), the cache was consulted under a different key than the
          ;; store holds, so its miss proves nothing and the trie must answer.  That one
          ;; equality subsumes every special-predicate storage rule at once.
          (if (and (= sentence (:sentence built))
                   (functor-cache-authoritative? kb stamp built))
            nil
            (let [probe  #(first (p/leaf-at (:index kb) (sx/path (res/kb-sentex kb % context))))
                  direct (stored-at kb built (p/leaf-at (:index kb) (sx/path built)))]
              (if direct
                ;; only this arm fills the cache, and the difference is what the answer
                ;; *says*.  Here it is "this sentence is stored at this handle" — true until
                ;; the sentex is removed, which is a choke point.  The mirror arm's answer is
                ;; "this sentence resolves to the handle of its mirror", which additionally
                ;; needs the mirror to keep resolving; the stamp covers that, but a firing
                ;; never asks it, so there is nothing to buy by widening the contract.
                ;; **Cached only when the spelling survives canonicalization**: the removal
                ;; choke point clears the canonical key (`integrate/sentex-removed!`), so an
                ;; entry keyed on a spelling canonicalization rewrites — a sorted symmetric
                ;; literal, a folded comparison — would outlive its sentex as a stale handle
                (if (= sentence (:sentence built))
                  (observe/cache-handle! stamp sentence context direct)
                  direct)
                ;; the global property, matching kb-sentex's key discipline: storage sorted
                ;; the arguments (or did not), and which it did cannot vary by who is looking
                (let [sym? #(tax/has-prop? (:taxonomy kb) :symmetric %)]
                  (when (and (sx/symmetric-literal? sentence sym?)
                             (every? sx/ground-term? (rest sentence)))
                    (probe (sx/mirror-literal sentence)))))))))))

;; ---- the P/¬P coincidence set --------------------------------------------
;; A negation nogood (`settle/negation-nogoods`) needs a body stored in *both*
;; polarities, and most negative facts have no positive twin.  Enumerating every
;; stored negation on every settle to find the few that clash is quadratic in the
;; negation count (a settle runs after every mutation).  `:opposed` instead holds
;; exactly the bodies stored both ways, maintained O(1) from two `count-at` probes at
;; the store primitive below and the removal choke point (`integrate/sentex-removed!`),
;; so settle iterates it directly rather than scanning the `:false` trie node.

(defn body-under-not
  "A fact's body with a single leading `not` stripped — the form both polarities key
  on (`(not (flies Opus))` and `(flies Opus)` share the body `(flies Opus)`).  Double
  negation is eliminated at store time, so one strip suffices; a non-fact sentence (a
  rule, a metadata declaration) is returned unchanged and simply never opposes.

  Public because `settle` reads it the other way round: given a handle whose belief just
  moved, this is which opposed body's pairing that handle could have changed, and so
  which memo entry the settle owes a re-derivation."
  [sentence]
  (if (and (sequential? sentence) (= 'not (first sentence)) (= 2 (count sentence)))
    (second sentence)
    sentence))

(defn- opposed?
  "Is `body` stored in **both** polarities — some positive fact under it and some
  `(not body)` under `[:false body]`?  Storage only (belief-blind), the same gate
  `negation-nogoods` applies before its belief-filtered pairing.  The `:false` probe
  runs first: it is 0 for the overwhelmingly common body with no negative twin, so the
  positive `key-stream` walk is never built."
  [idx body]
  (let [b (sx/canon body)]
    (and (pos? (p/count-at idx [:false b]))
         (pos? (p/count-at idx (vec (sx/key-stream b)))))))

(defn note-opposed!
  "Update the `:opposed` coincidence set for a sentence whose fact just arrived or
  left: add its body when both polarities are now stored, drop it otherwise.  Runs at
  the store primitive (`create-sentex`, every add) and the removal choke point
  (`integrate/sentex-removed!`, every remove), so no store path can bypass it; recover
  rebuilds the set with `rebuild-opposed!`.

  The same call posts the body to `:negations` as **dirty** and drops whatever the last
  settle derived for it.  A store or a removal is the one way a body's pairing can change
  with no belief moving to record it — a second `(not S)` arriving in another context adds
  a pair between two sentexes that were both already believed — so the settle's other
  input, the relabelled region, cannot see it.  Posting it here means the two inputs
  together cover every way the answer moves, and it costs one `dissoc` and one `conj` at a
  choke point that was already being paid for.

  **Both writes are skipped for a body that is opposed neither before this store nor
  after it**, which on a positive corpus is every fact of it.  Such a body's pairing has
  not moved: it had none and it has none.  Nothing can read the post either — the two
  readers of `:dirty` (`settle/moved-bodies` and `settle/note-supersession-flips!`)
  filter it by `:opposed` — and `:by-body` cannot hold an entry for it, since entries are
  only ever derived for bodies that were opposed at some settle and the arm below drops
  one the moment a body stops being opposed.  Without the guard a bulk load conj's every
  fact's body into a `:dirty` set that grows to the size of the corpus and is then
  dropped whole by the first settle, which is the one phase of a load whose per-fact cost
  **grows** with the corpus (docs/storage.md, \"What a bulk load costs\")."
  [kb sentence]
  (let [b   (sx/canon (body-under-not sentence))
        now (opposed? (:index kb) b)]
    (when (or now (contains? @(:opposed kb) b))
      (swap! (:opposed kb) (if now conj disj) b)
      (swap! (:negations kb) (fn [m] (-> m
                                         (update :by-body dissoc b)
                                         (update :dirty (fnil conj #{}) b)))))))

(defn rebuild-opposed!
  "Recompute `:opposed` from storage — the scan `recover` needs, since the set is
  derived state no store holds.  Enumerates the stored negated bodies (the `:false`
  node's children, deduped across contexts) and keeps those with a stored positive
  twin.

  The `:negations` memo over that set goes with it, for the reason every derived cache
  here is cleared rather than merged into on a rebuild: a merge can only ever *add*, so an
  entry for a body the rebuilt set no longer holds would outlive the sentexes it was
  derived from.  The `relabel` in the same `recover` touches every node, so the next
  settle repopulates it whole."
  [kb]
  (let [idx (:index kb)]
    (reset! (:negations kb) {})
    (reset! (:opposed kb)
            (into #{} (comp (filter #(opposed? idx %)) (map sx/canon))
                  (p/children idx [:false])))))

;; ---- the argument-preservation roster --------------------------------------
;; `settle/preserving-nogoods` has to decide, once per settle, whether this KB declares
;; any argument preservation at all — and the honest read of that (`inherit/declarations-
;; exist?`) is a set-cardinality read per declaration functor, on the path every assert
;; runs.  `assert_cost_test` prices exactly that kind of constant.  So the declarations
;; are kept here as storage instead: `:preserving`'s bargain is `:opposed`'s, except that
;; nothing is read off the index to maintain it either, because a declaration is
;; recognized from the sentence's own functor.

(defn- preservation-pair
  "The `[P R]` an argument-preservation declaration states, or nil for any other
  sentence — including `(not (transitiveInArg …))`, whose functor is `not`.  The one
  shape test the roster keys on, so an ordinary fact costs a map lookup on its functor
  and nothing else."
  [sentence]
  (when (and (sequential? sentence) (= 4 (count sentence))
             (contains? inherit/declarations (first sentence)))
    (let [[_ pred _ rel] sentence]
      (when (and (symbol? pred) (symbol? rel)) [pred rel]))))

(defn note-preserving!
  "Record (`true`) or drop (`false`) an argument-preservation declaration in the
  `:preserving` roster.  Called at the store primitive (`create-sentex`, every add) and
  the removal choke point (`integrate/sentex-removed!`, every remove), so no store path
  can bypass it; `recover` rebuilds the roster with `rebuild-preserving!`.

  A no-op for every sentence that is not a declaration, which on any corpus is all but a
  handful — and like `note-excepted!` beside it, and unlike `note-opposed!`, it reads
  **nothing off the index**, so a bulk load whose backing atom is stale mid-load
  (`memory/*bulk-txn*`) is not a case this has to be correct across.

  Counted, not a set: `(transitiveInArg largerThan 1 genl)` stated in two contexts is two
  sentexes saying one thing, and retracting the first must not retire what the second
  still says.  The count is *storage* — belief is the reader's filter here exactly as it
  is for `:opposed`, since a defeated declaration is one `positions` will decline to read
  and not one the roster should forget."
  [kb sentence add?]
  (when-let [pr (preservation-pair sentence)]
    (swap! (:preserving kb)
           (fn [m] (let [n (+ (get m pr 0) (if add? 1 -1))]
                     (if (pos? n) (assoc m pr n) (dissoc m pr)))))))

(defn rebuild-preserving!
  "Recompute `:preserving` from storage — the scan `recover` needs, since the roster is
  derived state no store holds.  One functor-root walk per declaration functor, both
  empty for nearly every KB.

  Counts what is **stored**, negations included as non-declarations: `preservation-pair`
  is the same shape test the choke points apply, so a rebuilt roster and an incrementally
  maintained one cannot disagree about what a declaration is."
  [kb]
  (let [idx (:index kb) recs (:records kb)]
    (reset! (:preserving kb)
            (reduce (fn [m h]
                      (if-let [pr (some-> (p/get-sentex recs h) :sentence preservation-pair)]
                        (update m pr (fnil inc 0))
                        m))
                    {}
                    (mapcat #(p/sentexes-with-functor idx %) (keys inherit/declarations))))))

;; ---- the visibility roster ------------------------------------------------
;; `res/excepted-handles` answers which handles a believed `(except (sentexHandle H))`
;; hides from a view context, and it is asked **per placement** and per candidate
;; justification during a chaining run.  Read off the index it is E record fetches, E
;; `jtms/in?` calls and a `tax/context-up` per call, for E excepts anywhere in the KB —
;; measured at 89% of a chaining run's wall clock at E=1,000 (`lein bench-hotreads`).
;;
;; What the roster removes is the *fetches*: which except sits in which context, and what
;; each hides, are facts about storage, so they are maintained here at the two choke
;; points and read as a map.  What stays a read is belief — `jtms/in?` on the except's own
;; handle — and the `context-up` walk, both of which move without a sentex arriving or
;; leaving.  This is `:opposed`'s bargain exactly (belief-blind storage, filtered by the
;; reader), and it is the second idiom rather than a stamped memo because the scope that
;; asks is the scope that writes: forward chaining moves the change clock per conclusion,
;; so a clock-stamped memo would be retired between one placement and the next
;; (`literal-cache/lookup`).

(defn except-target
  "The handle a visibility `(except (sentexHandle H))` sentence hides, or nil for any
  other sentence — including `(not (except …))`, whose functor is `not`.  The one shape
  test the roster keys on, so a sentence that is not an `except` costs a `=` on its
  functor at the store choke point and nothing else.

  A **meta-exception** — `(except (sentexHandle E))` where E is itself an `(except …)` —
  cascades: hiding an except suppresses its effect, restoring visibility of the target
  the inner except was hiding.  The cascade is evaluated at read time by
  `resolution/excepted-handles`, which checks whether each except-handle is itself
  hidden before counting it as active."
  [sentence]
  (when (and (sequential? sentence)
             (= sx/except-functor (first sentence))
             (= 2 (count sentence)))
    (sx/handle-id (second sentence))))

(defn- roster-add
  "`m` with the except stored at `eh` in `ctx`, hiding `target`, recorded."
  [m ctx target eh]
  (update-in m [ctx target] (fnil conj #{}) eh))

(defn- roster-drop
  "`m` with that entry gone, and any level it emptied gone with it — so an entry means
  *something is hidden here*, and the roster's own emptiness is the read's O(1) gate."
  [m ctx target eh]
  (let [ehs   (disj (get-in m [ctx target] #{}) eh)
        inner (if (empty? ehs)
                (dissoc (get m ctx) target)
                (assoc (get m ctx) target ehs))]
    (if (empty? inner) (dissoc m ctx) (assoc m ctx inner))))

(defn note-excepted!
  "Record (`true`) or drop (`false`) a visibility `except` in the `:excepted` roster,
  from the sentex itself: the context it holds in, the handle it hides, and its own
  handle.  Called
  at the store primitive (`create-sentex`, every add) and the removal choke point
  (`integrate/sentex-removed!`, every remove), so no store path can bypass it; `recover`
  rebuilds the roster with `rebuild-excepted!`.

  A no-op for every sentence that is not an `except`, which on any corpus is all but a
  handful — and unlike `note-opposed!` beside it this reads **nothing off the index**, so
  a bulk load whose backing atom is stale mid-load (`memory/*bulk-txn*`) is not a case
  this has to be correct across.

  **Target outside, except handles inside**, because that is the question the hot caller
  asks: `chain/antecedent-hidden?` wants to know whether *these two or three* handles are
  hidden, and this shape answers it with a lookup per handle instead of materializing
  every handle hidden anywhere in the cone.  A **set** of except handles under each
  target, since two excepts in one context may name one target and the first removal must
  not retire what the second still hides — the same non-interference `special/bump-roster!`
  keeps with a count, done with identities because an except has exactly one."
  [kb sentex add?]
  (when-let [target (except-target (:sentence sentex))]
    (let [ctx (:context sentex)
          eh  (:id sentex)]
      (swap! (:excepted kb) (if add? roster-add roster-drop) ctx target eh)
      ;; Maintain the meta-except counter so it always equals what `rebuild-excepted!`
      ;; computes: the number of stored excepts whose target resolves to a stored except.
      ;; Two roles change that when this except is stored or removed.
      ;;
      ;; (1) This except *as a referencer*.  If its own target resolves to a stored
      ;; except, this except is a meta-except: count it on add, discount it on a remove
      ;; whose target still resolves.  A remove whose target is already gone is a no-op
      ;; here — role (2) discounted it when that target left.
      (when-let [target-sentex (p/get-sentex (:records kb) target)]
        (when (except-target (:sentence target-sentex))
          (swap! (:meta-except-count kb) (if add? inc dec))))
      ;; (2) This except *as a target*.  Removing it strands every meta-except that named
      ;; it — each stops resolving to a stored except — so discount them here, while the
      ;; roster still holds them (they live in records this removal does not touch).  This
      ;; is the leak's fix: their own later removal reads *this* record for the target and
      ;; finds it gone, so the decrement can only happen now.  Add never needs it — a
      ;; target outlives the excepts that name it, so nothing waits on its arrival.
      ;;
      ;; Gated on the counter itself: a KB with no meta-except (all but a handful) can
      ;; strand nothing, so it skips the roster scan entirely and the common except
      ;; removal stays O(1) — only a KB that actually holds a meta-except pays the walk.
      (when (and (not add?) (pos? @(:meta-except-count kb)))
        (let [stranded (reduce-kv (fn [n _ctx targets] (+ n (count (get targets eh))))
                                  0 @(:excepted kb))]
          (when (pos? stranded)
            (swap! (:meta-except-count kb) - stranded)))))))

(defn rebuild-excepted!
  "Recompute `:excepted` from storage — the scan `recover` needs, since the roster is
  derived state no store holds, and the one a **fork** needs for the same reason: a fork's
  belief is rebuilt over the merged view rather than inherited, so its own roster starts
  empty over a base full of excepts (docs/overlay.md).

  Enumerates the stored `except` facts through the functor root, which spans both
  polarities — a `(not (except H))` roots there too and `except-target` drops it."
  [kb]
  (let [recs (:records kb)
        roster (reduce (fn [m h]
                         (if-let [s (p/get-sentex recs h)]
                           (if-let [target (except-target (:sentence s))]
                             (roster-add m (:context s) target h)
                             m)
                           m))
                       {}
                       (p/sentexes-with-functor (:index kb) sx/except-functor))
        ;; Count meta-exceptions: excepts whose target is itself an except
        meta-count (reduce (fn [n h]
                             (if-let [s (p/get-sentex recs h)]
                               (if-let [target (except-target (:sentence s))]
                                 (if-let [ts (p/get-sentex recs target)]
                                   (if (except-target (:sentence ts))
                                     (inc n) n)
                                   n)
                                 n)
                               n))
                           0
                           (p/sentexes-with-functor (:index kb) sx/except-functor))]
    ;; Two atoms, one logical value — and they may be written in two steps because this
    ;; runs only where nothing else can read them: `recover` and `fork` both build the KB
    ;; before handing it to anybody, and the maintenance path (`note-except!`) keeps the
    ;; count in step one write at a time.  A reader beside the writer reads them only
    ;; through the query path (`resolution/excepted?`), which is after both.
    (reset! (:excepted kb) roster)
    (reset! (:meta-except-count kb) meta-count)))

;; ---- the rule rosters ----------------------------------------------------

(def rule-key-pattern
  "The trie pattern every stored rule — and nothing else — matches.

  A rule keys as `[:rule <antecedents> <consequent> <assumption> <constraint> <context>]`
  and at **that** depth always: `:assumption` and `:constraint` are constant slots,
  present as nil on a rule that is neither a choice nor a contradiction rule, precisely so
  no rule keys shallower than another (`sentex/key-tokens`).  So one fixed-length pattern
  of variables under the `:rule` root enumerates the rule extent through the trie, at the
  cost of the rule subtree rather than of the fact extent — which is what makes rebuilding
  the rosters below O(rules)."
  '[:rule ?antecedents ?consequent ?assumption ?constraint ?context])

(defn rebuild-rule-roster!
  "Recompute `:rule-antecedents` and `:rule-contexts` from storage — the scan a
  **recover** needs, since both are derived state no store holds, and the one a **fork**
  needs for the same reason: a fork's derived state is rebuilt over the merged view
  rather than inherited, so its own rosters start empty over a base full of rules.

  Neither is put back by anything else.  Recovery replays justifications and the stored
  special-predicate sentexes; it does not replay rule *indexing*, which is where
  `special/note-rule!` bumps these — so without this a recovered KB answers
  `chain/rule-firing-report` with nothing, and `special/visibility-seeds` seeds nothing,
  leaving a `genlCx` edge asserted after a restart to re-join no rules.  That is exactly
  the arrival-order dependence the seeds exist to remove.

  The keys are the ones the live path writes (`rules/antecedent-predicates`): a positive
  antecedent's predicate, and `[:not pred]` for a negated one.  Reference counts, so the
  rebuilt roster is entry-for-entry equal to the one a KB that never restarted holds.

  The two atoms are reset one after the other rather than as one step, and that is
  enough: this runs inside `recover` and inside a fork, on the writer, before the KB
  reaches any reader — the same footing as `rebuild-excepted!` above."
  [kb]
  (let [recs (:records kb)
        [antes ctxs]
        (reduce (fn [acc h]
                  (if-let [sx (p/get-sentex recs h)]
                    (-> acc
                        (update 0 (fn [m]
                                    (reduce (fn [m k] (update m k (fnil inc 0)))
                                            m
                                            (rules/antecedent-predicates (:sentence sx)))))
                        (update 1 update (:context sx) (fnil inc 0)))
                    acc))
                [{} {}]
                (p/lookup (:index kb) rule-key-pattern))]
    (reset! (:rule-antecedents kb) antes)
    (reset! (:rule-contexts kb) ctxs)))

(defn create-sentex
  "Store `sentence` in `context` as a new sentex, index it, and return `[handle sentex]`.

  `strength` (optional) is the assumption strength the record is *born* with.  A premise
  is a sentex whose `:strength` is non-nil, so a caller that already knows it is asserting
  a premise says so here rather than storing the record and having `mark-premise` store it
  again — on the disk backend that second store is a second full frame, leaving the first
  dead the moment it is written, which is half the record log and what trips its compaction
  threshold mid-load."
  ([kb sentence context] (create-sentex kb sentence context nil))
  ([kb sentence context strength]
   (let [s (cond-> (res/kb-sentex kb sentence context)
             strength (assoc :strength strength))
         h (p/put-sentex (:records kb) s)
         s (assoc s :id h)]
     (p/index-sentex (:index kb) s h)
     ;; the index image's cadence, on the one thread allowed to write this index
     ;; (`disk/backend/maybe-refresh-index-snapshot!`).  `:snapshot-dir` is non-nil only
     ;; on a KB that *has* an image, so every other backend pays one field read: the root
     ;; count is a profiled index read and the refresh call resolves nothing, so both stay
     ;; behind the gate rather than being evaluated for a directory with no image in it.
     (when-let [d (:snapshot-dir kb)]
       (disk/maybe-refresh-index-snapshot! d (p/count-at (:index kb) [])))
     ;; the add-side seam for an incremental matcher's alpha memories — a no-op
     ;; unless one is engaged (docs/inference.md, "Incremental rule matching")
     (observe/notify-add kb s h)
     ;; and the coarse clock a *derived, resident* structure stamps itself with: this
     ;; is one of the two points the stored content moves at, the other being
     ;; `integrate/sentex-removed!`
     (observe/note-change)
     ;; a run with the handle cache engaged learns the handle here rather than paying a
     ;; trie walk to rediscover it — keyed on the *canonical* sentence, which is what the
     ;; store holds; a caller looking it up by some other spelling misses and fills its
     ;; own key off the index, since a miss costs exactly the trie walk and no more
     (observe/cache-handle! (canon-stamp kb) (:sentence s) (:context s) h)
     ;; maintain the P/¬P coincidence set for settle (this store may have completed an
     ;; opposing pair); the remove mirror is `integrate/sentex-removed!`
     (note-opposed! kb (:sentence s))
     ;; ...and the visibility roster, at the same point and with the same mirror
     (note-excepted! kb s true)
     ;; ...and the argument-preservation roster, third of the same kind: settle's gate on
     ;; whether preservation can clash with anything is an `empty?` on it
     (note-preserving! kb (:sentence s) true)
     [h s])))

(defn find-or-create-sentex
  "The existing sentex for `sentence` in `context`, or a new one — `[handle sentex new?]`.
  `strength` is passed through to `create-sentex` and so applies only to a *new* record;
  an existing one keeps what it has until `mark-premise` says otherwise."
  ([kb sentence context] (find-or-create-sentex kb sentence context nil))
  ([kb sentence context strength]
   (if-let [h (find-sentex-handle kb sentence context)]
     [h (p/get-sentex (:records kb) h) false]
     (let [[h s] (create-sentex kb sentence context strength)]
       [h s true]))))

(defn antecedent-order
  "`handles` as a justification's stored antecedent vector: ordered by what each
  antecedent **says** — its sentence, then its context — never by the handle.

  A handle is allocated in assertion order, so a vector in the order the derivation
  built it is a record of which side arrived first.  A firing is seeded by the antecedent
  that triggered it (`chain/complete-antecedents`), so `a(x,y) ⇐ b1, b2` arrives here as
  `[h_b2 h_b1 rule]` under one arrival order and `[h_b1 h_b2 rule]` under the other, and
  a merge derived from two facts arrives naming them in the order they were written.
  Stored that way, everything that reads it would inherit that: `core/why`'s `:because`,
  `why-not`'s `:missing`, `preview`'s `:antecedents`, the browser's justification line —
  and `core/supporting-justifications`' sort key is computed *from* it, so the key whose
  whole job is to make a list of justifications order-independent would itself be keyed
  on arrival.

  **The informant is ordered with the rest, not pinned to a position.**  It is named by
  the record's own `:informant` slot, so a position would restate it; half the engine's
  informants are symbols (`rewriteOf`, `functional`) that are no part of the vector at
  all, so a position rule could not hold uniformly where one order over every antecedent
  does.  Nothing reads a position: belief reads the antecedents as a **set**
  (`jtms/valid?`, `jtms/has-justification?`), and `why` lifts the rule out by identity.

  Keyed once per antecedent rather than once per comparison, and short-circuited below
  two: this runs on the derivation path, where a firing builds one vector per placement
  and the content key is not free.

  **Called where something is stored, never where something is only decided.**  A
  content key per antecedent is the price of the order, so it is paid once per
  record written rather than once per firing: the callers are the justification writers
  (`chain/place-fact-conclusion`, `chain/mint-rule`, `special/derive-equality`) and the
  refusal ledger.  Everything upstream of them reads the antecedents as a **set** or as a
  membership test — `jtms/has-justification?` keys on `[informant (set antecedents)]`,
  `chain/antecedent-hidden?` is a `some` — so ordering upstream buys nothing and prices
  the sort against firings rather than against records.  Keep it that way: move a call
  **later** if a caller turns out to decide before it stores, never earlier."
  [kb handles]
  ;; The key is **structural** — the antecedent's sentence, then its context — and
  ;; `nm/sort-by-content-key` compares it by `compare-form`, walking the two forms in place
  ;; rather than printing them: no String is built per handle, and no ambient
  ;; `*print-length*` can elide two long sentences to one prefix, collapse the key and
  ;; drop the tie back onto the arrival order this exists to remove.  The key is built
  ;; once per antecedent (not once per comparison), and a run of one is left as it came.
  (let [recs (:records kb)]
    (nm/sort-by-content-key (fn [h] (let [s (p/get-sentex recs h)] [(:sentence s) (:context s)]))
                            handles)))

(defn justification-content-key
  "The key every listing of justifications sorts on: what a justification **says** — the
  informant, its antecedents' sentences, the firing's bindings, and the sentence and
  context of what it concludes.  Returns the key fn, so a listing builds it once and the
  record store is looked up through one closure.

  Three readings share it and must not drift: `core/supporting-justifications`,
  `core/dependent-justifications`, and a clash report's `:justifications`
  (`settle/clash-report`).  All three start from a **set** of allocation-ordered ids
  (`jtms/supports`, `jtms/dependents`), so an unsorted listing would say which
  derivation happened to land first.

  **The informant enters as its content, never as its handle.**  A rule informant
  contributes the rule's sentence and context; a symbol informant (`rewriteOf`,
  `functional`, `decontextualizedPredicate`) contributes the symbol.  Its handle would
  be assertion order wearing a key's clothes — and it would decide the whole
  comparison, since two justifications for one conclusion usually differ in their rule
  before they differ in anything else.

  The antecedent sentences are a key about content because the stored vector is itself
  content-ordered (`antecedent-order`); computed off an arrival-ordered vector, the key
  whose job is to make the *list* order-independent would be reading arrival order out
  of each element instead.

  The **consequence** is in the key for `dependent-justifications`, whose members
  conclude different sentexes: one firing placed into two contexts differs in nothing
  else, nor does a lifted copy from the fact it was lifted from.  It is constant across
  the other two readings, which each list one conclusion's supports, so it moves
  nothing there.

  The keys are **structural** forms, ordered by `nm/compare-form` — a caller sorts with
  that comparator, never with the default `compare` (which would throw on a sentence).
  Two justifications with equal keys say the same thing; only their ids separate them,
  and an id is the arrival order this key exists to keep out."
  [kb]
  (let [recs (:records kb)
        ;; **with the context**, because `antecedent-order` sorts on it: a key coarser
        ;; than the ordering it is derived from leaves one firing placed into two
        ;; contexts tied, and a tie falls back to `jtms/supports`' id order, which is the
        ;; arrival order this key exists to keep out.  `core/preview` reads
        ;; `(first (supporting-justifications …))`, so the tie is not cosmetic there
        sent (fn [x] (when-let [s (some->> x (p/get-sentex recs))]
                       [(:sentence s) (:context s)]))]
    (fn [j]
      (let [inf (:informant j)
            isx (when (integer? inf) (p/get-sentex recs inf))
            c   (some->> (:consequence j) (p/get-sentex recs))]
        ;; A **structural** key, compared by `nm/compare-form` — never printed.  The
        ;; comparator closes both of a printed key's costs at once: no String is built
        ;; per justification, and no ambient `*print-length*` can elide a long sentence to
        ;; a prefix and drop the tie back onto the id set's own order
        ;; (`antecedent-order`'s reason).  A key that must print anyway goes through
        ;; `nm/print-key`, which is where that guard lives.
        [(if (integer? inf) (:sentence isx) inf) (:context isx)
         (mapv sent (:antecedents j))
         ;; sorted, because a small binding map is a `PersistentArrayMap` and iterates in
         ;; **insertion** order — which is the trigger order.  One rule reached through two
         ;; antecedents binds the same variables to the same terms, so unsorted the equal
         ;; bindings would give unequal keys and the reading would depend on which fact
         ;; fired it.  Sorted into a vector of pairs, which `nm/compare-form` walks — a map
         ;; is not sequential to it.
         (when-let [b (:bindings j)] (mapv (fn [[k v]] [k v]) (into (sorted-map) b)))
         (:sentence c) (:context c)]))))

;; ---- the equality closure: reading and rewriting -------------------------
;; The closure itself is `vaelii.impl.taxonomy`'s; the *machinery* that runs when two
;; names turn out to denote one thing (migration, supersession) lives in
;; `vaelii.impl.special`.  What lives here is the read/rewrite half — which terms an
;; equality sentence merges and how a sentence or goal is restated under the class
;; representatives — because `sentexes-matching` needs it, and everything above
;; needs it in turn.

(defn equality-sentence?
  [sentence] (contains? equality-predicates (nm/functor sentence)))

(defn preferred-term
  "The term this equality sentence puts on top, or nil.  `rewriteOf` deprecates its
  second argument in favour of its first; `sameAs` and `equals` deprecate neither."
  [[f a _]] (when (= f 'rewriteOf) a))

(defn rewrite-term*
  "`term` (a sentence or a term) rewritten to its **normal form**: first every symbol
  replaced by its class representative (ground congruence, `res/representative-term`), then its
  argument terms normalized under any schematic rewrite rules (the oriented equational
  rewriting of docs/equality.md — `(equals (fatherOf (fatherOf ?x)) (grandfatherOf
  ?x))` reduces `fatherOf∘fatherOf` to `grandfatherOf`).

  Both halves are belief-following and both are gated: a KB with no merges pays a
  representative lookup per symbol, and one with no schematic equations skips
  normalization entirely (`tax/rewrite-rules` is empty).  Migration and query both go
  through here, so a stored term and a goal meet at one normal form.

  **With a `context`, both halves apply only where they are visible.**  A merge is a
  sentex, so it rewrites the contexts that inherit it and no others — the same
  filter `migrate-sentex` puts on the twins it creates, now on the question as well as
  on the answer.  Without it the two disagree: a rewrite migration correctly declined
  to make still renames the goal, and a context loses the ability to retrieve a fact it
  believes, under either spelling.  The two-arity is the **unscoped** read, which asks
  about the KB rather than from a vantage.

  `rewrite-term*` takes the visibility predicate **already built**, for a caller
  normalizing many sentences under one reader.  Deciding visibility costs a record fetch
  per equality supporter, and `res/visible-supporter-fn` memoizes those — but only within
  the one predicate it returns, so a caller that builds a fresh one per sentence re-fetches
  the same handful of records once per sentence.  `supersession-map` is that caller: it
  re-examines every entry the closure displaces on each merging assert.

  One definition, in `resolution` beside the `representative-in` its congruence half
  recurses with, because `BeliefProjectionProver` normalizes a projected proposition the
  same way and two copies of that is one copy too many."
  ([kb term visible?] (res/normal-form kb term visible?)))

(defn rewrite-term
  "`rewrite-term*` for a caller that has a context rather than a built predicate — the
  ordinary spelling.  Its docstring above owns the semantics."
  ([kb term] (rewrite-term* kb term nil))
  ([kb term context] (rewrite-term* kb term (res/visible-supporter-fn kb context))))

(defn displaced-terms*
  "The `{old-term representative}` rewrites a sentence undergoes, given the visibility
  predicate already built — empty when nothing in it has merged.  Mention-aware: a term
  quoted inside a `quotingFunction` is recorded displaced only by a spelling rename, never
  by a `sameAs` merge of its referent, matching what `rewrite-term*` actually rewrites (so
  `why-not` does not over-report a held-opaque mention).  Delegates to `res/displaced-terms-in`,
  which is the flat walk when no `quotingFunction` is declared."
  [kb sentence visible?]
  (res/displaced-terms-in kb visible? sentence))

(defn displaced-terms
  "The `{old-term representative}` rewrites a sentence undergoes — empty when nothing
  in it has merged.  This is what a supersession *records*, so `why-not` can name the
  representative that displaced a spelling rather than merely reporting that one did.

  Scoped by `context` like every other class read: the spelling that displaced this one
  is the one *its own* context elected, and naming a representative elected by an edge
  that context cannot see would make `why-not` cite a merge nobody there has heard of.
  The `visible?` arity is `rewrite-term*`'s, and for the same caller."
  ([kb sentence] (displaced-terms* kb sentence nil))
  ([kb sentence context] (displaced-terms* kb sentence (res/visible-supporter-fn kb context))))

(defn rewrite-goal
  "A query goal with its terms rewritten to their class representatives.

  A caller who has not heard about a merge still asks under the old spelling, and
  that spelling's own sentexes are no longer believed — so the goal is rewritten
  before lookup and migration stays invisible to them.  Rewriting is a *question*
  transformation only: `handle-of` and the `lookup` levels deliberately do **not** do
  it, because they answer about storage rather than about truth.

  **`different` is exempt.**  Rewriting its arguments would map each to its class
  representative, so a merged pair would compare equal — and since reading class
  membership is the entire job of `different`, every `different` goal would go false
  the moment anything merged.  The prover normalizes its own arguments instead, with
  the same recursive walk (`res/representative-term`) and then compares the results, so
  the exemption is explicit here rather than resting on the rewrite happening to be a
  no-op.

  **A `modalPredicate`'s proposition is exempt too**, and by the same kind of reason: it
  is what the *agent* holds true, so the asker's merges must not rewrite it.  That one is
  not spelled here — it is congruence opacity, held inside `res/representative-term` so
  the stored belief and the question move together (docs/belief.md).

  Rewritten only by the merges `context` can see (`rewrite-term`'s three-arity): a
  question asked from a context is a question about what that context holds,
  so a merge it does not inherit must not rename what it asked."
  ([kb goal] (rewrite-goal kb goal nil))
  ([kb goal context] (res/goal-normal-form kb goal context)))

(defn- rule-touches-merged-predicate?
  "Does rewriting this rule change a **predicate or type** — a non-individual symbol
  it mentions — rather than only an individual constant?  That is the case a
  predicate/type merge (docs/equality.md, round two) must migrate a rule for, since
  it changes a functor the rule reasons over; an individual-only rewrite is held
  back.  `displaced-terms` already computes the `{changed rep}` map, so this only
  asks whether any changed spelling is a non-individual."
  [kb sentence]
  (boolean (some #(not (nm/individual? %)) (keys (displaced-terms kb sentence)))))

(defn rewritable-sentex?
  "May this stored sentex be migrated by an equality merge?

  A **rule** is held back for an *individual* merge — rewriting a rule's individual
  constant is congruence over a schema rather than over ground content, and the
  rewritten copy would fire alongside its original — but **migrated for a predicate
  or type** merge, which changes a functor the rule reasons over (`birthplaceOf ⇒
  bornIn`, `dog ⇒ canine`): the original is superseded and the twin carries the
  inference (docs/equality.md, round two).  A rule's `exceptWhen` exceptions ride
  separate meta-sentexes keyed by the rule's handle; migration re-points them onto the
  twin (`special/migrate-handle-metas`, the same path that carries an `except` or a
  target-following reply), and a NAF (`unknown`) antecedent lives *in* the rule
  sentence, so it rewrites with the rule and re-posts through the twin's own
  `index-rule-sentex` — so an exception/NAF rule migrates with its guard intact.

  A non-rule is migratable unless it is one of the equality relations themselves:
  rewriting `(rewriteOf Pref Dep)` yields `(rewriteOf Pref Pref)`, the self-edge
  `wff` exists to refuse."
  [kb sentex]
  (if (rules/rule? sentex)
    (rule-touches-merged-predicate? kb (:sentence sentex))
    (let [s (:sentence sentex)]
      (and (not (equality-sentence? s))
           (not (equality-sentence? (sx/positive-body s)))))))

;; ---- matching ------------------------------------------------------------

(defn- stored-once-per-handle
  "The stored sentex of each match, **one per handle**, keeping the first.

  The matcher answers in bindings and this reader answers in sentexes, and for one shape
  those disagree about how many answers there are: a symmetric literal with two variable
  arguments matches one stored fact twice and differently — `(sibOf ?a ?b)` binds a stored
  `(sibOf Rex Tib)` both ways round — and both bindings are answers a join or a prover
  needs (`res/raw-match` says why).  Neither is a second *sentex*: there is one record,
  and a caller asking which sentexes match is told about it once.

  Lazily, because these readers are lazy over live state on purpose — the browser shows
  fifty of an imported ontology's hundred thousand `comment`s by taking fifty, and a
  realized reader would fetch them all per page.  So the `seen` set grows with what the
  consumer walks rather than with the extent.

  **Only a literal that can duplicate pays for it.**  The mirror probe is the only thing
  that answers one handle twice, and `raw-match` runs it for a symmetric literal alone —
  so for every other sentence the set would be built, grown per element and never consulted
  to any purpose.  That is not free where it matters: `settle`'s walk over the P/¬P
  coincidence set reads this twice per opposed body, and paying a set insert per member
  there turns an arbitration that is bookkeeping into one that allocates with the standing
  set (`negation-arbitration`)."
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
  "*Believed* sentexes matching `sentence` **as spelled**, in `context` —
  `sentexes-matching` without the equality goal rewrite.

  For a caller iterating the engine's own storage rather than asking a question about the
  world.  `sentexes-matching` rewrites a goal to the class representative, which is right for a
  *question* — a caller who has not heard about a merge still gets its answer — and wrong
  for an iteration, because it silently redirects: asking about a body an equality has
  retired hands back the *representative's* sentexes, and the caller then reports them
  under the spelling it asked with.  `settle`'s walk over the P/¬P coincidence set is that
  caller, and a superseded body has to answer *nothing* there, which is what it does here:
  its own sentexes are no longer believed, so the belief filter empties it and the
  representative's body reports the pair once, under its own name.

  Everything else is `sentexes-matching`'s: literal (no subtype expansion), both
  symmetric argument orders, belief-sensitive, clear of the `exceptWhen`
  meta-sentexes."
  ([kb sentence] (sentexes-matching-as-stored kb sentence '?ctx))
  ([kb sentence context]
   ;; This *is* the level-2 (`:local`) matcher — one literal context, no subtype
   ;; fan-out, both symmetric argument orders, belief-filtered, clear of the
   ;; exceptWhen meta-sentexes.  `res/raw-match` is exactly that, so routing
   ;; through it (rather than a bare `p/lookup`) shares `match-one`'s argument-root
   ;; retrieval: a pattern pinning an argument *after* a variable — `(parentOf ?x
   ;; Tom)` — is answered from the predicate-scoped argument root
   ;; (`[:argument-root parentOf 2 Tom]`), not a full leading-variable trie fan-out.  `without-excepted` then drops
   ;; what a visible `except` hides here (docs/contexts.md).  Both halves are
   ;; belief-following; the stored record already fetched to unify against rides
   ;; along as the third element, so this costs no extra round trip.
   (->> (res/raw-match kb sentence context)
        (res/without-excepted kb context)
        (res/without-retired kb context)
        (stored-once-per-handle
         (sx/symmetric-literal? sentence #(tax/has-prop? (:taxonomy kb) :symmetric %))))))

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
