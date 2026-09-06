;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.catalog
  "What knowledge bases this process can load, and the lifecycle of loading one.

  Everything above the engine assumes it is holding *the* KB.  A browser that lists the
  KBs available, loads one while you watch, and switches to it needs two things the
  engine does not have: a description of a KB that has not been loaded yet, and somewhere
  for a load that takes minutes to run while the pages keep answering.  Those are the two
  halves here.

  **A source** is a KB you could load, as data — a kind, a name, and wherever the content
  comes from.  Six kinds:

  | kind         | content                                             | loader |
  |--------------|-----------------------------------------------------|--------|
  | `:core`      | the CxCore vocabulary head alone               | `vaelii.impl.core-context` |
  | `:starter`   | the shipped schema-only ontology                    | `vaelii.impl.starter` |
  | `:generated` | synthesized from numbers — types, rules, a fwd mix  | `vaelii.impl.io.generate` |
  | `:corpus`    | a translated sentence corpus (OpenCyc)              | a foreign reader, `:cyc-corpus` |
  | `:dump`      | a vaelii export dump                                | `vaelii.impl.io.import` |
  | `:store`     | an on-disk KB already in vaelii's own format        | opened in place |

  The first three ship in this repo and are always offered.  The last three are **found**:
  each directory on the search path (`VAELII_KB_PATH`, else `./kbs` and `~/.vaelii/kbs`)
  is probed, and what marks it — a corpus `meta.edn`, a dump `meta.edn`, a `records/` +
  `index/` pair — decides its kind.  A `catalog.edn` (`VAELII_KB_CATALOG`, else
  `~/.vaelii/catalog.edn`) names sources outside the search path.  Nothing about a
  machine's paths is baked into the repo.

  **An entry** is a source that has been loaded, or is loading: a KB, a status, and a
  progress reading the loaders report into (`:on-progress`, reported by every loader —
  the corpus reader, `io.import/import-dump` and `io.generate/load-into`).  The running
  half of that is not here: a load is a **job** (`vaelii.impl.jobs`), which is what gives
  it a thread of its own, the progress reading, the cancel flag and the report — so an
  entry carries the job's id and reads its status rather than keeping one.  One load runs
  at a time, since a load claims this process's writer, and cancelling one is cooperative:
  the loaders have no other safe interruption point, and an import is not a transaction,
  so a cancelled load leaves the KB holding what had already landed.

  **A KB is readable before it is finished.**  `activate` asks only that an entry hold a
  KB, so the one arriving can be the one every page reads — a corpus is browsable from
  its first thousand sentexes, and a store that opens in seconds is browsable while
  belief is still being rebuilt behind it.  What that costs a reader is completeness, not
  correctness, and `active-caveat` is what says so.

  **And a KB can go back out.**  `export-entry!` writes a loaded one as an export dump as
  a job like any other, which closes the loop: a dump written under the search path is a
  `:dump` source the moment its `meta.edn` lands, so exporting and reloading needs nothing
  outside this namespace.

  **Unloading never deletes an on-disk KB.**  A memory-backed entry has its stores
  cleared (they would otherwise hold the corpus for the life of the JVM); a disk-backed
  one is *closed* — the file lock released, the directory left exactly as it was.  The
  same directory can then be loaded again, or opened by another process."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.generate :as generate]
            [vaelii.impl.io.import :as import]
            [vaelii.impl.jobs :as jobs]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.starter :as starter])
  (:import (java.io File)))

;; ---- the shipped sources -------------------------------------------------

(def built-in
  "The sources that need no files beyond the ones in this repo.  `:options` is what the
  UI offers per source, as data: each entry is a form control, and `load-source` reads
  the same keys back out of the params map."
  [{:id      "core"
    :kind    :core
    :name    "Core vocabulary"
    :blurb   "CxCore alone — the predicates the engine interprets, and nothing else."
    :scale   "392 sentexes"
    :options [{:key :chain? :type :flag :label "Forward-chain after loading" :default false}]}
   {:id      "starter"
    :kind    :starter
    :name    "Starter ontology"
    :blurb   "The shipped schema: the vocabulary head, the definitional upper band, and the middle theories. No individuals."
    :scale   "~3,310 sentexes"
    :default? true
    :options [{:key :chain? :type :flag :label "Forward-chain after loading" :default false}]}
   {:id      "generated"
    :kind    :generated
    :name    "Generated corpus"
    :blurb   "A synthetic KB of a chosen shape — types, individuals, rules, a forward/backward mix — deterministic in its seed."
    :scale   "as large as you ask for"
    :repeat? true                                        ; loadable many times over, at different shapes
    :options (concat
              [{:key :base :type :choice :label "Base vocabulary" :default "core"
                :choices [["core" "Core vocabulary"] ["starter" "Starter ontology"]]}]
              (for [k generate/knobs] (assoc k :type :slider))
              [{:key :seed :type :number :label "Seed" :default 1 :min 0 :max 1000000}
               {:key :chain? :type :flag :label "Forward-chain after loading" :default false}
               {:key :max-derivations :type :number :label "Derivation cap" :default 100000
                :min 1000 :max 100000000 :step 1000
                :help "chaining is by far the longest phase of a chained load — this is what bounds it (a run overshoots by the last datum's fan-out)"}])}])

(def ^:private corpus-options
  [{:key :profile :type :choice :label "Profile" :default "ontology"
    :choices [["ontology" "Ontology (drops the lexical layers)"]
              ["core" "Core (Cyc's own upper vocabulary)"]
              ["full" "Full (everything, including natural language)"]]}
   {:key :dir :type :path :label "Target directory" :default ""
    :help "empty loads into memory; a path makes it a durable :disk-log KB"}
   {:key :bulk? :type :flag :label "Bulk load (skip the per-fact checks)" :default false}
   {:key :chain? :type :flag :label "Forward-chain after loading" :default false}
   ;; Bounded for the reason the generator's is, and harder: a generated KB's layer count
   ;; bounds its own chain, and a corpus of a million assertions has nothing playing that
   ;; part, so the cap is the whole bound.
   {:key :max-derivations :type :number :label "Derivation cap" :default 100000
    :min 1000 :max 100000000 :step 1000
    :help "chaining a corpus is by far the longest thing a load can do — this is what bounds it, and a run that hits it is reported as truncated"}])

;; `recover` rebuilds two things, not one — the JTMS *and* the cached taxonomy — so
;; skipping it costs more than belief.  A dump loaded without it has no genl or
;; genlCx closure at all: `types` and `contexts` are empty, `genls` answers only the
;; term it was asked about, and the ontology page has nothing to draw.  On the OpenCyc
;; import `docs/kbs.md` measures: off gives 0 types and 0 contexts, on gives its 132,391
;; and 13,202.  The flag has to say that, or an operator reads "not belief-queryable", leaves
;; it off, and concludes the KB imported wrong.
;; Three values rather than a checkbox, because the middle one is the answer for a corpus
;; that cannot afford the rebuild *today* and should not be made to throw its
;; justifications away to say so — and for a foreign dump it is the only value that keeps
;; them at all (see `import-records-only!`).
(defn- belief-mode
  "What the form's `:belief?` choice means to `import-dump`.

  The form speaks in verbs (`:rebuild` / `:stored` / `:skip`) because a checkbox cannot
  offer three answers and a tri-state named `true`/`:stored`/`false` is indistinguishable from a typo in a
  dropdown.  A caller that already speaks the importer's own vocabulary is passed through,
  so this is a widening rather than a translation layer.

  **Anything else is handed on unchanged**, which is what leaves `import-dump`'s own
  refusal (`:unknown-option`, `import/belief-modes`) reachable through this entry point.
  Defaulting it here would swallow that refusal and pick the *cheapest* load instead:
  `{:belief? :store}` — one letter off `:stored` — reads as records-only, and that path
  never opens the justification stream, so what the typo drops is dropped for good.  An
  **absent** choice is the one thing that takes a default here, and it takes the form's."
  [v]
  (case v
    (:rebuild true)  true
    :stored          :stored
    (:skip false nil) false
    v))

(def ^:private dump-options
  [{:key :belief? :type :choice
    :label "Belief and the taxonomy"
    :default :skip
    :choices [[:rebuild "Rebuild now (slow — a JTMS node per sentex)"]
              [:stored  "Store it, rebuild later"]
              [:skip    "Skip it (records and index only)"]]
    :help "\"rebuild now\" is the finished KB. \"store it\" reads and stores every justification and premise mark but leaves the TMS and the genl/genlCx closures empty, so the KB is findable and countable now and can be recovered later without re-reading the dump. \"skip it\" never reads the justification stream, and for a dump in a foreign dialect that is permanent — nothing a later recover could rebuild belief from is stored"}
   {:key :dir :type :path :label "Target directory" :default ""
    :help "empty loads into memory; a path makes it a durable :disk-log KB"}])

(def ^:private store-options
  [{:key :recover? :type :flag :label "Recover belief and the taxonomy on open (slow)" :default false
    :help "off opens the records and index as they stand: no genl/genlCx closure, and belief-filtered queries answer nothing"}])

;; ---- discovery -----------------------------------------------------------

(defn- file-at ^File [dir & parts] (apply io/file dir parts))

(defn- readable-edn
  "`f` read as EDN, or nil — a malformed or unreadable file makes a directory *not* a
  source rather than an error, since discovery runs over directories nobody promised
  anything about.

  **The size bound is the one thing that is an error.**  Discovery reads the manifest of
  every directory on the search path, so a file that merely *has* the right name decides
  how much is pulled into a string; `import/read-edn-manifest` refuses past
  `import/manifest-bytes`, and that refusal travels rather than reading as \"this is not
  a KB\".  A gigabyte named `meta.edn` is either a mistake or an attempt, and both are
  worth a line naming the file — a silent skip would report the directory as holding
  nothing and say nothing about why.  Its other refusal, a manifest that is not readable
  EDN, is exactly the \"not a source\" case above and is answered as one."
  [^File f]
  (when (.isFile f)
    (try (import/read-edn-manifest f)
         (catch clojure.lang.ExceptionInfo e
           (if (= :manifest-too-large (:type (ex-data e))) (throw e) nil))
         (catch Exception _ nil))))

(defn classify
  "The kind of KB in directory `d`, or nil.  Reads the marker each writer leaves: a
  corpus's `meta.edn` carries the context order it was written in, a dump's carries a
  `:format-version`, and a vaelii store is a `records/` directory the record writer has
  stamped with its own `format.edn`.

  **The records half is the whole marker**, and requiring an `index/` beside it hid
  exactly the stores worth finding.  Only `:disk-log` keeps a durable index on disk;
  `:disk-columnar`, `:disk-dense` and `:disk-memory` derive theirs and write no `index/`
  at all — so a large store classified as nothing and could not be
  offered.  Those are the backends a corpus past a few million records is loaded into,
  `:disk-log`'s index being a map held in RAM whatever else is on disk."
  [^File d]
  (when (.isDirectory d)
    (let [m (readable-edn (file-at d "meta.edn"))]
      (cond
        (and (map? m) (:context-order m))                                :corpus
        (and (map? m) (or (:format-version m) (:variant m)))             :dump
        (some? (readable-edn (file-at (file-at d "records") "format.edn"))) :store))))

(defn- corpus-scale
  "How big a found corpus says it is — from the report its writer left beside it, which
  is the only thing that knows before a load."
  [^File d]
  (when-let [r (readable-edn (file-at d "report.edn"))]
    {:sentences (:sentences r) :contexts (:contexts r)}))

(defn- dump-scale
  "What a found dump says it holds, and **whose** it is.  The two dialects spell the
  second count differently — a pure dump has justifications where an engine dump has
  deductions — and the dialect decides how much re-canonicalization an import faces, so
  a card that did not name it would leave the operator guessing at the slow part.

  `:index?` says the dump carries its index as well.  That is a claim about what is on
  disk, never a promise it will be used: the importer replays those entries only if it
  can prove they describe the records beside them, and rebuilds otherwise."
  [^File d]
  (when-let [m (readable-edn (file-at d "meta.edn"))]
    {:sentences (:sentex-count m)
     :supports  (or (:justification-count m) (:deduction-count m))
     :index?    (= :records+index (:variant m))
     :dialect   (if (= :vaelii/export (:format m)) :vaelii :engine)}))

(defn- du
  "Bytes on disk under `d`, or nil.  A store carries no count of what it holds, so its
  size on disk is the honest thing to show instead."
  [^File d]
  (when (.isDirectory d)
    (reduce + 0 (map #(.length ^File %) (filter #(.isFile ^File %) (file-seq d))))))

(defn human-bytes
  "A byte count as something to read at a glance.  Public because the browser shows byte
  counts of its own (a KB's estimated footprint, the heap) and there is no reason for two
  spellings of the same figure."
  [n]
  (cond (nil? n)        nil
        (< n 1048576)   (format "%.0f kB" (/ (double n) 1024))
        (< n 1073741824) (format "%.0f MB" (/ (double n) 1048576))
        :else            (format "%.1f GB" (/ (double n) 1073741824.0))))

(defn- discovered-source
  "A source map for the KB directory `d`, or nil when it holds none.

  A found KB is offered whether or not this build has a reader for it: a corpus and a
  foreign-dialect dump each need one that ships as a plugin rather than in-tree
  (`vaelii.impl.foreign`), and the honest answer to \"I cannot read this\" is a load that
  fails saying so, not a KB that silently stops being listed."
  [^File d]
  (when-let [kind (classify d)]
    (let [name* (.getName d)
          path  (.getAbsolutePath d)]
      (merge {:id (str (clojure.core/name kind) ":" name*)
              :kind kind
              :name name*
              :path path
              :found? true}
             (case kind
               :corpus (let [{:keys [sentences contexts]} (corpus-scale d)]
                         {:blurb (str "A translated sentence corpus"
                                      (when contexts (str " over " contexts " contexts")) ".")
                          :scale (if sentences (str (format "%,d" (long sentences)) " sentences")
                                     (human-bytes (du d)))
                          :total sentences
                          :options corpus-options})
               :dump   (let [{:keys [sentences supports dialect index?]} (dump-scale d)]
                         {:blurb (str (if (= :vaelii dialect)
                                        "A vaelii export dump, in our own dialect"
                                        "An engine-dialect dump, re-canonicalized on the way in")
                                      (when supports
                                        (str " — " (format "%,d" (long supports))
                                             (if (= :vaelii dialect) " justifications" " deductions")))
                                      (when index? ", with its index")
                                      ".")
                          :dialect dialect
                          :index?  index?
                          :scale (if sentences (str (format "%,d" (long sentences)) " sentexes")
                                     (human-bytes (du d)))
                          :total sentences
                          :options dump-options})
               :store  {:blurb "An on-disk vaelii KB, opened in place — no import, no copy."
                        :scale (human-bytes (du d))
                        :options store-options})))))

(defn- set-to
  "A switch's value, or nil when it is unset.  **Blank is unset**, which is the one
  vocabulary every other switch this build reads holds to (`vaelii.impl.config`'s `raw`,
  `guard/api-token`): an exported-but-empty variable is the shell's way of saying
  nothing.  Read as a value instead, an empty `VAELII_KB_PATH` splits to nothing and
  leaves discovery with **no** directory at all — so `/kbs` offers the built-ins and
  reports nothing else found, which is the one answer a KB list must not give by
  accident (`max-discovered` below).

  Spelled as a fn over the value rather than over the switch's *name*, because the
  configuration-surface scan reads `System/getenv \"VAELII_…\"` literals: a helper taking
  the name as an argument hides the switch from it, and the two names here appear in no
  other read."
  [v]
  (not-empty (str/trim (str v))))

(defn search-path
  "The directories discovery walks: `VAELII_KB_PATH` (`:`-separated) when set, else the
  `vaelii.kb.path` system property, else `./kbs` and `~/.vaelii/kbs`.  A path entry that
  *is* a KB directory counts as one source; otherwise its children are probed, one level
  down.  (The property mirrors `vaelii.disk.dir`, and is what a test sets — a JVM cannot
  change its own environment.)  Either spelling **blank** is unset — `set-to` for why."
  []
  (if-let [p (or (set-to (System/getenv "VAELII_KB_PATH"))
                 (set-to (System/getProperty "vaelii.kb.path")))]
    (remove str/blank? (str/split p #":"))
    [(str (System/getProperty "user.dir") "/kbs")
     (str (System/getProperty "user.home") "/.vaelii/kbs")]))

(defn- catalog-file ^File []
  (io/file (or (set-to (System/getenv "VAELII_KB_CATALOG"))
               (set-to (System/getProperty "vaelii.kb.catalog"))
               (str (System/getProperty "user.home") "/.vaelii/catalog.edn"))))

(defn- configured-sources
  "Sources named by the catalog file: a vector of `{:id :name :path}` maps, each of which
  may state its `:kind` or leave it to be classified from what is at `:path`.  This is
  how a KB outside the search path is offered — and the only place a machine's own paths
  live, since the repo holds none."
  []
  (let [f (catalog-file)]
    (when-let [entries (readable-edn f)]
      (for [e entries
            :when (and (map? e) (:path e))
            :let  [d (io/file (:path e))
                   found (discovered-source d)]]
        (merge (or found {:id (str "missing:" (:path e))
                          :kind (:kind e :store)
                          :scale "not found"
                          :blurb (str "Nothing readable at " (:path e) ".")
                          :missing? true
                          :options []})
               ;; No `:load` key: nothing reads one, and carrying it forward made the
               ;; catalog file look like it could name what to run rather than only
               ;; what to read.  A source says where it is and what it is; how it
               ;; loads is this namespace's business.
               (select-keys e [:id :name :blurb :kind :options]))))))

(def max-discovered
  "How many directories one search-path entry is probed for, at most.

  A search-path entry is probed one level down, and every candidate under it costs a
  `classify` (a `meta.edn` read) and, for a `:store`, a size estimate — on **every**
  `/kbs` request, since `sources` is recomputed per call so a corpus dropped in appears
  with no restart.  That is the trade, and it is a good one at the handful of KBs a
  machine usually holds; it is not a good one unbounded, and a directory of converted
  corpora is exactly what accumulates over time.  Nothing else in the browser renders an
  uncapped list (docs/web.md, \"Long lists continue\"), and this is the number that makes
  the KB list no exception.

  Generous rather than tight: the cap exists to bound the cost, not to curate."
  200)

(defn sources
  "Every KB this process can load, built-ins first: the shipped ontologies and the
  generator, then whatever the catalog file names, then whatever the search path holds.
  Recomputed per call — dropping a corpus into a search-path directory makes it appear on
  the next page load, with no restart.

  A search-path entry holding more than `max-discovered` candidates is probed for the
  first `max-discovered` by name, and what was passed over is **named** — on the returned
  vector's metadata as `:truncated`, and in the log.  A silent cap here would read as
  \"this machine has no other KBs\", which is the one answer a KB list must not give by
  accident.  The built-ins and the catalog file's own entries are never capped: each is
  named explicitly rather than found, and a caller that wrote a path down is owed it."
  []
  (let [dropped (volatile! [])
        probe   (fn [^File d]
                  (if (classify d)
                    [d]
                    (let [kids (sort-by #(.getName ^File %) (.listFiles d))
                          n    (count kids)]
                      (when (> n max-discovered)
                        (vswap! dropped conj {:dir (.getPath d)
                                              :passed-over (- n max-discovered)
                                              :probed max-discovered}))
                      (take max-discovered kids))))
        found   (for [p (search-path)
                      :let [d (io/file p)]
                      :when (.isDirectory d)
                      d2 (probe d)
                      :let [s (discovered-source d2)]
                      :when s]
                  s)
        result  (into [] (->> (concat built-in (configured-sources) found)
                              (reduce (fn [[seen acc] s]    ; first spelling of an id wins
                                        (if (contains? seen (:id s))
                                          [seen acc]
                                          [(conj seen (:id s)) (conj acc s)]))
                                      [#{} []])
                              second))]
    (when-let [t (seq @dropped)]
      (trove/log! {:level :warn :id ::search-path-truncated
                   :msg  (str "probed the first " max-discovered " entries of "
                              (str/join ", " (map :dir t))
                              " — a KB below that cut is not listed.  Name it in the "
                              "catalog file to list it regardless (docs/catalog.md).")
                   :data {:truncated (vec t)}}))
    (with-meta result {:truncated (vec @dropped)})))

(defn source
  "The source with this id, or nil."
  [id]
  (first (filter #(= id (:id %)) (sources))))

;; ---- the registry --------------------------------------------------------
;;
;; One atom holds every loaded (and loading) KB, which of them is active, and the next
;; free memory space.  A memory-backed KB is keyed by space number for the life of
;; the JVM (`vaelii.impl.memory`), so two resident KBs must be given different ones —
;; and the numbers below start well clear of the block the test suite owns.

(def ^:private first-space 100)

(defonce ^:private state (atom {:active nil :entries {} :order [] :next-space first-space}))

;; `load-source`'s claim is a read-test-write across two touches of `state`, which one
;; `swap!` cannot express (it throws rather than retrying, and a `swap!` fn must be
;; retryable).  This makes the two one step — the entry key it picks, the already-loaded
;; test and the registration.  `export-entry!`'s one-export-at-a-time check is the same
;; shape over the job registry (`exporting?`, then `jobs/submit`) and takes the same
;; monitor, so two export requests arriving together cannot both pass it.  `unload!`'s
;; export test is the third, and takes it for a reason the first two do not have: its
;; check and `export-entry!`'s read *different* registries, so the two are serialized only
;; by sharing this.  The *other* claim — that only one job writes at a time — is the
;; registry's, under its own monitor, and nothing here takes them in the other order.
(defonce ^:private start-monitor (Object.))

(defn- now [] (System/currentTimeMillis))

(defn- claim-space!
  "The next free `:space` number."
  []
  (dec (:next-space (swap! state update :next-space inc))))

(defn- put-entry!
  "Apply `f` to entry `key` — **and only while the registry still holds it**.  Nothing here
  creates an entry (`load-source` and `register!` both do that with their own `assoc-in`),
  so an update reaching a dropped key would not fail: it would *recreate* the entry as a
  fragment with no `:key` and no `:started`, which `view` subtracts from.  Reachable
  because a load's own thread writes here as it unwinds, and `unload!` may have dropped
  the entry in between."
  [key f]
  (swap! state (fn [s] (cond-> s (contains? (:entries s) key) (update-in [:entries key] f))))
  key)

(defn- with-job
  "An entry's own fields, plus the four its **job** owns: where the load has got to, what
  became of it, and when.  An entry has no status of its own to disagree with the job's —
  a load reports through the registry like every other long operation, and one place
  holding the answer is what stops the panel and the loader from telling two stories.

  An entry `register!` filed has no job (it was handed a KB that was already built) and
  carries its own settled status; so does one whose job has aged out of the registry, which
  is why a load files its terminal status onto the entry as it finishes rather than leaving
  the placeholder it registered with — see `load-source`."
  [e]
  (if-let [j (jobs/job (:job e))]
    (merge e (select-keys j [:status :progress :error :finished]))
    e))

(defn entry
  "One entry, whole (`:kb` included) — for a caller that wants the KB itself."
  [key]
  (with-job (get-in @state [:entries key])))

(defn- view
  "An entry as something safe to render or send: the KB dropped, elapsed time filled in.

  `:kb?` survives the dropping because it is what decides whether an entry can be read
  at all — a load registers before it opens anything, and until then there is no KB to
  activate however healthy the entry looks."
  [e]
  (when e
    (let [e (with-job e)]
      (-> (dissoc e :kb)
          (assoc :elapsed-ms (- (or (:finished e) (now)) (:started e))
                 :kb?        (some? (:kb e)))))))

(defn entries
  "Every entry, in load order, as views."
  []
  (let [{:keys [entries order]} @state]
    (into [] (keep #(view (get entries %))) order)))

(defn active
  "The key of the active entry, or nil."
  []
  (:active @state))

(defn active-entry [] (view (entry (active))))

(defn in-process?
  "Does entry `key` hold a KB in *this* JVM?  A KB is a map with a record store in it; an
  attached daemon is registered as an entry too, and its KB is somewhere else — which is
  why `stats` and `footprint` have nothing to say about one, and why an export of one is
  written on that daemon's host rather than here."
  [key]
  (boolean (:records (:kb (entry key)))))

(defn active-kb
  "The KB the browser should be reading, or nil when nothing is loaded."
  []
  (:kb (entry (active))))

(defn name-of
  "What to call `kb` — the name of the entry holding it, or nil for a KB this registry
  never heard of.  By identity, like `exporting-kb?` and `write-blocked?`.

  A page that has *resolved* a KB and judged it asks this rather than `active-entry`:
  `activate` re-points the holder at any moment and takes no monitor, so the active entry
  a moment later can be a different KB — and a refusal that named it would name the KB it
  did not judge."
  [kb]
  (when kb
    (let [{:keys [entries order]} @state]
      (some #(let [e (get entries %)] (when (identical? kb (:kb e)) (:name e))) order))))

(defn loading?
  "Is a load running?  One runs at a time: a load claims this process's writer, and two at
  once would make each other's timings meaningless.  Asked of the registry, since that is
  where a running load lives."
  []
  (boolean (some #(= :load (:kind %)) (jobs/running))))

(defn exporting?
  "Is an export running?  One at a time, as with loads."
  []
  (boolean (some #(= :export (:kind %)) (jobs/running))))

(defn exporting-kb?
  "Is `kb` the one a running export is still walking?  Asked by identity, like
  `write-blocked?`, and it is that question's reciprocal: `export-entry!` refuses to
  *start* while a loader writes the KB, and this is what lets the write entry points refuse
  while the walk runs — the walk fetches record by record with no snapshot to walk
  instead, so a write landing mid-walk gives the dump no single state to be of.

  `unload!` reads it for the same reason and one more: a release is not a write but the
  end of the KB, and a walk whose records stop existing halfway through is worse off than
  one that merely raced a write.  That is why both predicates sit here beside `loading?`
  rather than down with `export-entry!` — three registry reads of the same shape, asked
  by everything that has to know whether a KB is somebody's."
  [kb]
  (boolean (and kb
                (some #(and (= :export (:kind %))
                            (identical? kb (:kb (entry (:entry %)))))
                      (jobs/running)))))

(defn holder
  "A deref-able that always yields the KB to read — the active entry's, or `fallback`
  when nothing is loaded.  This is what the browser is built against: `app` holds one of
  these instead of a KB, so activating another entry re-points every page at once."
  [fallback]
  (reify clojure.lang.IDeref
    (deref [_] (or (active-kb) fallback))))

;; ---- stats ---------------------------------------------------------------

(defn stats
  "The headline counts for a loaded KB.  `term-count` is one set-size read and the
  context sizes are one each, so this is cheap even on a corpus of millions — deliberately
  so, since it runs every time the page lists the entries.

  Nil for anything that is not an in-process KB (an attached daemon is registered as an
  entry too, and its counts are the daemon's to report)."
  [kb]
  (when (:records kb)
    (try
      {:contexts (count (v/contexts kb))
       :sentexes (v/sentex-count kb)
       :types    (count (v/types kb))
       :terms    (v/term-count kb)}
      (catch Exception e
        {:error (.getMessage e)}))))

;; ---- memory --------------------------------------------------------------
;;
;; Two different kinds of number, deliberately kept apart.  `heap` is a **measurement**
;; of the whole JVM — every KB in this process, the browser itself, and whatever garbage
;; has not been collected yet, in one figure that cannot be attributed to anybody.
;; `footprint` is an **estimate** for one KB, and the only way to attribute anything: the
;; alternative is to unload it and diff the heap, which is not a thing a page can do to a
;; KB somebody is reading.

(def resident-bytes-per-sentex
  "What one stored sentex costs in RAM, per resident component — the coefficients
  `footprint` multiplies out.  Measured on a real-assert load through `bench-scale` and
  `bench-memory`; resident size is linear in
  the sentex count (one record, one index path and one node per sentex, and trie prefix
  sharing only *reduces* the per-sentex cost), which is what makes a single coefficient
  the right shape for an estimate.

  Shape-dependent, and that is the estimate's main error term: a fact of arity 2 with no
  compound arguments indexes at ~1,549 B while a richer one measured ~2,158 B.  The
  leaner figure is used, so a corpus of fat sentences reads low.

  The `:tms` figure is the **dense** network's, since that is the default (the reference
  map costs ~467 B/sentex — ~3.8× more — and is now the pinned baseline).  It is a second
  shape term: the dense JTMS is `18 B/node + 166 B/justification` (bench-scale, item 09),
  so per *stored* sentex it is 18 + (j/n)·166 — ~101 at a moderate j/n≈0.5, the basis the
  467 was taken on.  A justification-heavy KB (j/n≈1) reads low here for the same reason a
  fat-sentence corpus reads low above; the single coefficient trades that error for an
  O(1) estimate that never counts justifications on the render path."
  {:index   1549
   :records 279
   :tms     101})

(defn heap
  "What this JVM's heap is doing **right now** — `{:used :committed :max}` in bytes, read
  off the memory MX bean.

  A measurement, not an estimate, but a coarse one: `:used` includes garbage that has not
  been collected, so it drifts up between collections and drops without anything being
  freed.  Read it as the structure of the curve, not as a number to subtract KBs from."
  []
  (let [u (.getHeapMemoryUsage (java.lang.management.ManagementFactory/getMemoryMXBean))]
    {:used      (.getUsed u)
     :committed (.getCommitted u)
     :max       (let [m (.getMax u)] (when (pos? m) m))}))

(defn footprint
  "An estimate of what the KB in entry `key` costs in RAM, by component:
  `{:sentexes :index :records :tms :total :estimated? true}` (bytes), or nil for an entry
  with no in-process KB.

  Nothing is measured — see `resident-bytes-per-sentex` for where the coefficients come
  from and how wrong they can be — and the sentex count is the trie's own root count,
  O(1).  The belief check is not free, though this runs on every render of a page that
  polls: `first` over `jtms/datums` is one `keys` on the reference TMS, but the dense one
  answers `-datums` by draining its whole node bitmap into a vector of boxed Longs before
  `first` can look at one.  So a `{:tms :dense}` KB pays an allocation per stored sentex
  per render, to learn whether the network holds anything at all.

  Two adjustments make it a statement about *this* KB rather than about a generic one:
  a `:disk-log` KB pages its records, so the record term is dropped (what stays resident is
  the bounded hot-record LRU, which does not grow with the corpus), and a KB loaded
  without belief — an import with `:belief? false`, a store opened without `:recover?` —
  has no truth-maintenance network at all, so that term goes too.

  Nil for an entry that is not an in-process KB, as `stats` is: an attached daemon holds
  its corpus in *another* process, so nothing here is about this one's memory — and asking
  it would be a round trip per render."
  [key]
  (let [e  (entry key)
        kb (:kb e)]
    (when-let [n (when (:records kb) (try (v/sentex-count kb) (catch Exception _ nil)))]
      (let [paged?   (= :disk-log (:backend (:where e)))
            belief?  (jtms/any-node? (:tms kb))
            {:keys [index records tms]} resident-bytes-per-sentex
            parts    {:index   (* n index)
                      :records (if paged? 0 (* n records))
                      :tms     (if belief? (* n tms) 0)}]
        (assoc parts
               :sentexes   n
               :paged?     paged?
               :belief?    belief?
               :estimated? true
               :total      (reduce + 0 (vals parts)))))))

(defn predicted-footprint
  "What a source would cost in RAM if it were loaded, in bytes — its own count of what it
  holds put through the same coefficients — or nil for a source that does not know how
  big it is (the generator, whose size is whatever the sliders say).

  A load builds belief and holds its records in RAM unless a directory is named, so this
  is the full three-component figure: the ceiling, not the floor."
  [{:keys [total]}]
  (when (and (number? total) (pos? total))
    (long (* total (reduce + 0 (vals resident-bytes-per-sentex))))))

(defn memory
  "The memory picture the browser shows: the JVM heap as measured, every loaded entry's
  estimated footprint, and their sum."
  []
  (let [fps (into [] (keep (fn [k]
                             (when-let [f (footprint k)]
                               (assoc f :key k :name (:name (entry k)))))
                           (:order @state)))]
    {:heap    (heap)
     :entries fps
     :total   (reduce + 0 (map :total fps))}))

;; ---- loading -------------------------------------------------------------

(defn- open-kb-for
  "The KB an entry loads into: an in-memory one over a freshly claimed space, or —
  when the params name a directory — a durable `:disk-log` one there.  Returns
  `[kb where]`, `where` being what `unload!` needs to take it down again."
  [{:keys [dir]}]
  (if (str/blank? (str dir))
    (let [s (claim-space!)]
      [(v/open-kb {:backend :memory :space s :recover? false})
       {:backend :memory :space s}])
    [(v/open-kb {:backend :disk-log :dir (str dir) :recover? false})
     {:backend :disk-log :dir (str dir)}]))

(defn- check-readable!
  "Refuse a store whose records do not come back as sentexes.

  A record is frozen with its class name in it, so a store whose frames name a class this
  build does not resolve thaws to nippy's `{:nippy/unthawable …}` placeholder — every read
  succeeds and every answer is empty, the worst way for this to go wrong.  One record is
  enough to tell, and an empty store is fine (there is nothing to disagree about)."
  [kb path]
  (when-let [h (cap/some-sentex-id (:records kb))]
    (let [r (p/get-sentex (:records kb) h)]
      (when-not (:sentence r)
        (throw (ex-info (str "the store at " path " holds records this build cannot read"
                             " — they thaw as " (pr-str (some-> r keys vec))
                             ", not as sentexes.  It was written by a build whose record"
                             " classes differ; re-import it from a dump.")
                        {:type :unreadable-store :path path}))))))

(defn- chain-asked
  "Forward-chain `kb` when the form asked for it, folding what it derived into `summary`.

  **After** loading, which is what the option says and the only shape that pays: chaining
  per assertion derives against a KB whose rules are half there, costs more, and reaches
  the same fixpoint — so every loader here asserts with `:chain? false` and a chained load
  is one pass at the end.  That is also the only point at which chaining can be *reported*,
  which is why it is a phase of its own, with no total: a fixpoint's agenda grows as it
  derives, so there is nothing for `done` to be a fraction of.

  `:max-derivations` bounds it.  A corpus-sized rule set has no layer count to bound a run
  by the way a generated KB does, so a cap is what stands between a chained load and one
  that never comes back — a truncated run says so in the summary."
  [kb params progress! summary]
  (if-not (:chain? params)
    summary
    (let [note (fn [pending] (if pending
                               (format "derived · %,d on the agenda" (long pending))
                               "forward chaining to a fixpoint"))
          _    (progress! {:phase :chaining :done 0 :total nil :note (note nil)})
          r    (v/forward-chain
                kb (cond-> {:on-progress (fn [{:keys [derived pending]}]
                                           (progress! {:phase :chaining :total nil
                                                       :done (or derived 0)
                                                       :note (note pending)}))}
                     (:max-derivations params) (assoc :max-derivations
                                                      (:max-derivations params))))]
      (assoc summary :derived (:derived r 0) :truncated? (boolean (:truncated? r))))))

(defn- run-load
  "Load `source` into a fresh KB under `params`, reporting through `progress!`.  Returns
  the loader's summary.

  `note-kb!` is called with `[kb where]` the moment the KB exists — *before* anything is
  loaded into it — so a load that then fails or is cancelled still leaves an entry that
  knows what it opened, and `unload!` can release it.  Without that, a cancelled corpus
  load would strand its memory space or its file lock with nothing pointing at them."
  [{:keys [kind path]} params progress! note-kb!]
  (let [open! (fn [] (let [[kb where] (open-kb-for params)] (note-kb! kb where) kb))]
    (case kind
      :core     (let [kb (open!)]
                  (progress! {:phase :vocabulary :done 0 :note "CxCore"})
                  (core-context/load-into kb)
                  (chain-asked kb params progress! {}))
      :starter  (let [kb (open!)]
                  (progress! {:phase :ontology :done 0 :note "the shipped schema"})
                  (starter/load-into kb)
                  (chain-asked kb params progress! {}))
      :generated (generate/load-into (open!) params {:on-progress progress!})
      :corpus   (let [kb (open!)]
                  (progress! {:phase :vocabulary :done 0 :note "CxCore"})
                  (core-context/load-into kb)
                  ;; the corpus reader ships as a plugin, so it is asked for rather
                  ;; than required (vaelii.impl.foreign).  Its own `:chain?` chains per
                  ;; assertion, which is not what the option offers — `chain-asked` says
                  ;; why the pass belongs at the end
                  (chain-asked
                   kb params progress!
                   ((:load-dir! (foreign/reader! :cyc-corpus))
                    kb path
                    {:profile     (keyword (or (:profile params) "full"))
                     :bulk?       (boolean (:bulk? params))
                     :chain?      false
                     :on-progress progress!})))
      ;; passed through rather than coerced: `:belief?` has three values and a `boolean`
      ;; here would read `:stored` as `true` and run the recover the caller asked to defer
      :dump     (import/import-dump (open!) path {:belief?     (belief-mode (:belief? params))
                                                  :on-progress progress!})
      ;; a store is already a KB — opening it *is* the load.  Opening is not quick at
      ;; scale (the record log is scanned and the index map rebuilt in RAM) and it
      ;; reports nothing while it runs, so say what is happening before going in
      :store    (let [_  (progress! {:phase :open :done 0
                                     :note "scanning the record log and rebuilding the index"})
                      kb (v/open-kb {:backend :disk-log :dir path :recover? false})]
                  (note-kb! kb {:backend :disk-log :dir path :attached? true})
                  (check-readable! kb path)
                  (when (:recover? params)
                    (progress! {:phase :recover :done 0 :note "rebuilding belief"})
                    (v/recover kb))
                  {})
      (throw (ex-info (str "unknown KB source kind " (pr-str kind) " — want :core,"
                           " :starter, :generated, :corpus, :dump or :store")
                      {:type :unknown-source :kind kind})))))

(defn- entry-key
  "The key an entry is filed under: the source id, suffixed when that source can be
  loaded more than once (the generator, at several shapes).  The suffix is one past
  the highest still loaded, not a count — after `generated#1` of two is unloaded, a
  count would name `generated#2` again and collide with the live entry."
  [{:keys [id repeat?]}]
  (if-not repeat?
    id
    (let [prefix (str id "#")
          taken  (keep #(when (str/starts-with? % prefix) (parse-long (subs % (count prefix))))
                       (:order @state))]
      (str prefix (inc (reduce max 0 taken))))))

(defn- drop-entry!
  "Forget entry `key` — the registry half of `unload!`, and what a load that never started
  leaves behind."
  [key]
  (swap! state (fn [s]
                 (-> s
                     (update :entries dissoc key)
                     (update :order #(vec (remove #{key} %)))
                     (update :active #(when (not= % key) %))))))

(defn load-source
  "Start loading the source with id `source-id` under `params`, as a job.  Returns the
  entry key, or throws when the id names no source, the source is already loaded, or
  another job holds this process's writer.

  The entry is registered `:running` before this returns, so the caller can render it
  immediately; `entries` then reports the job's progress until it settles into `:done`
  (the KB is queryable, and activated when nothing else is) or `:failed` / `:cancelled`."
  ([source-id] (load-source source-id {}))
  ([source-id params]
   (let [src (or (source source-id)
                 (throw (ex-info (str "no KB source " (pr-str source-id) " — the built-in"
                                      " ids are \"core\", \"starter\" and \"generated\";"
                                      " anything else is named in the catalog file or"
                                      " found on the search path (docs/catalog.md)")
                                 {:type :unknown-source})))]
     ;; Pick the key, check and claim under one monitor.  The already-loaded test and the
     ;; `swap!` that registers the entry are two separate touches of `@state`, and two
     ;; requests arriving together on Jetty's pool can each pass both — both spawn a
     ;; loader, and two background loaders then write the same stores.  The key is picked
     ;; inside for the same reason: a `:repeat?` source's suffix is one past the highest
     ;; *registered*, so two generated loads keyed outside the monitor both read
     ;; `generated#1` and the second's registration overwrites the first's.  A *second
     ;; load* is refused a layer down, by the writer claim in the registry.
     (locking start-monitor
       (let [key (entry-key src)]
         (when (entry key)
           (throw (ex-info (str (:name src) " is already loaded — unload it first")
                           {:type :already-loaded :key key})))
         ;; The status and progress here are what an entry reads for the moment between being
         ;; registered and its job's id landing on it — `with-job` prefers the job the instant
         ;; there is one.  Not redundant: a caller rendering an entry in that window would
         ;; otherwise be handed a nil status, and the page names it.
         (swap! state (fn [s]
                        (-> s
                            (assoc-in [:entries key]
                                      {:key key :source (dissoc src :options) :name (:name src)
                                       :params params :status :running :started (now)
                                       :progress {:phase :starting :done 0 :total (:total src)}})
                            (update :order #(vec (distinct (conj % key)))))))
         (try
           (let [id (jobs/submit
                     {:label      (str "Load " (:name src))
                      :kind       :load
                      ;; the KB does not exist yet — `run-load` opens it — so the claim is
                      ;; made without naming it, and `write-blocked?` reads the entry for
                      ;; the identity once there is one
                      :writes     true
                      :progress   {:phase :starting :done 0 :total (:total src)}
                      :result-url "/kbs"
                      :entry      key}
                     (fn [progress!]
                       ;; The entry outlives its job's report — a settled job ages out of the
                       ;; registry after an hour — so the status the entry keeps *of its own*
                       ;; has to be the settled one.  `with-job` prefers the job while there is
                       ;; one and falls back to this; a fallback still reading `:running` is an
                       ;; entry that never finishes loading, and two callers act on that: the
                       ;; browser refuses every write to the KB (`write-blocked?`) and `unload!`
                       ;; refuses `:still-stopping`, both of them for ever.
                       (try
                         (let [note-kb! (fn [kb where] (put-entry! key #(assoc % :kb kb :where where)))
                               summary  (run-load src params progress! note-kb!)]
                           ;; a cancelled or failed load leaves whatever had landed in its
                           ;; stores; `unload!` is what takes those down
                           ;; `:progress` settles with the status, as it does on the job
                           ;; itself: the placeholder this entry registered with reads
                           ;; `:starting`, and an hour on that is the only reading left
                           ;; `stats` is a four-read census, so it runs BEFORE the swap —
                           ;; a swap! fn must be cheap and retryable (`start-monitor`'s
                           ;; own argument), and under contention it re-runs per retry
                           (let [ks (some-> (get-in @state [:entries key]) :kb stats)]
                             (put-entry! key #(assoc % :summary summary :stats ks
                                                     :status :done :finished (now)
                                                     :progress {:phase :done})))
                           (swap! state (fn [s] (cond-> s (nil? (:active s)) (assoc :active key))))
                           (trove/log! {:level :info :id ::loaded
                                        :msg (str "loaded KB " key) :data summary})
                           summary)
                         (catch Throwable t
                           (put-entry! key #(assoc % :status (if (jobs/cancelled? t) :cancelled :failed)
                                                   :finished (now)
                                                   :error (or (.getMessage t) (str (class t)))))
                           (throw t)))))]
             (put-entry! key #(assoc % :job id))
             key)
           (catch Throwable t
             ;; nothing is running, so the entry is a claim on a KB that will never exist
             (drop-entry! key)
             (throw t))))))))

(defn cancel!
  "Ask a running load to stop at its next progress report.  `!` because what it leaves
  behind is a half-loaded KB — the loaders write as they go and none of them is a
  transaction."
  [key]
  (boolean (some-> (:job (entry key)) jobs/cancel!)))

(defn- fall-back-active!
  "Nothing active but something loaded — fall to the most recent *finished* entry, so the
  browser is never left pointing at nothing while a KB is sitting right there.  `:done` and
  not merely \"has a KB\": an entry whose release failed is the one thing here nobody can
  vouch for, and falling to it would put the browser straight back on it."
  []
  (when-not (active)
    (swap! state assoc :active
           (last (filter #(= :done (:status (entry %))) (:order @state))))))

(defn unload!
  "Take an entry down: cancel it if it is still loading, release what it held, and drop it
  from the registry.

  **A memory-backed KB is cleared** — its stores are keyed by space number and would
  otherwise hold the corpus for the life of the JVM.  **A disk-backed one is closed, not
  cleared**: the file lock is released and the directory is left exactly as it was, so
  unloading an on-disk KB never destroys it.  The `!` is for the memory case, which does.

  Three ways it declines to do that, each about a KB something else is still holding:

  - **its loader has not stopped.**  Cancellation is cooperative, so the stores are still
    the loader's until its thread returns.  Refused as `:still-stopping`, and retryable.
  - **an export is walking it.**  `export!` fetches record by record with no snapshot to
    walk instead, so a release landing mid-walk leaves the dump a dump of a KB that
    stopped existing halfway through.  Refused as `:still-exporting` — the walk finishes
    against a live KB, and the retry is one the operator makes after it does.  **That test
    and the release are one step under `start-monitor`**, the monitor `export-entry!`
    checks and submits under: two touches of separate registries otherwise, so an unload
    and an export arriving together each pass their own check, and if the unload wins the
    race for the stores the walk dumps an emptied KB and reports `{:ok true}` over a
    summary that looks exactly right.  The entry is dropped inside the monitor too, so an
    export that was waiting on it finds no entry rather than a released one.
  - **the release itself failed.**  Reported rather than logged and forgotten: the entry
    keeps its place with status `:unreleased` and the reason on it, is not active (a KB
    whose stores half-closed is the one thing here nobody can vouch for), and the throw
    is what stops the caller reporting a clean unload over a directory that did not
    close.  Unloading again retries the release.

  `opts` takes `:run-in`, a wrapper the release runs inside — `export-entry!`'s own
  option, and here for the same reason: the browser hands its write monitor, so a
  synchronous write already past the write entry points drains before the stores go rather than
  interleaving with the clear."
  ([key] (unload! key nil))
  ([key {:keys [run-in]}]
   (when-let [e (entry key)]
     ;; A running load owns the stores this is about to clear or close, so nothing is
     ;; released until its thread has actually stopped.  Cancellation lands at the next
     ;; progress report, and a phase that reports none (opening a large store scans its
     ;; whole record log before it says anything) can outlast the wait — so say the entry
     ;; is still stopping and leave it whole rather than pulling the stores out from under
     ;; a live writer.  `:cancelling` is still that writer — a previous unload's cancel
     ;; whose thread has not stopped yet — so it takes the same wait, or the retry the
     ;; refusal below asks for would skip straight to the release.
     (when (#{:running :cancelling} (:status e))
       (cancel! key)
       ;; A job the registry has already dropped — one still running six hours later is
       ;; presumed wedged — answers no status at all, which is not a settled one either, so
       ;; this refuses for the same reason: its thread is still going, and the stores are
       ;; still its.
       (when-not (#{:done :cancelled :failed} (:status (jobs/wait (:job e) 30000)))
         (put-entry! key #(assoc % :error (str "still stopping — its loader has not "
                                               "reached a point at which it can be "
                                               "interrupted")))
         (throw (ex-info (str (:name e) " is still stopping — its loader has not reached a"
                              " point at which it can be interrupted; unload it again in a"
                              " moment")
                         {:type :still-stopping :key key}))))
     ;; and an export is a reader of exactly this KB, mid-request.  Not cancelled for the
     ;; operator: a dump takes minutes and is nobody's to throw away on the way past, so
     ;; the unload is what gives way.
     ;;
     ;; Checked and acted on under `start-monitor` — `export-entry!`'s monitor — because
     ;; the test and the release are two touches of two separate registries, and the export
     ;; that has to lose this race is the one that has not submitted yet.  Outside it, both
     ;; requests pass their own check, the release lands first, and the walk dumps an
     ;; emptied KB under a summary that is indistinguishable from a clean export.  `drop-entry!` is inside
     ;; for the other half of the same reason: an export blocked here must find the entry
     ;; *gone* rather than find it released.  The loader wait above stays outside — it is
     ;; about the load, it can take thirty seconds, and an export cannot start against a
     ;; KB a loader is still writing anyway.
     (locking start-monitor
       (when (exporting-kb? (:kb (entry key)))
         (throw (ex-info (str (:name e) " is being exported — the dump walks its records one"
                              " by one, so releasing them now would leave it a dump of a KB"
                              " that stopped existing halfway through.  Wait for the export,"
                              " or cancel it, then unload.")
                         {:type :still-exporting :key key})))
       (let [{:keys [backend dir]} (:where (entry key))
             run-in (or run-in (fn [work] (work)))]
         (try
           (run-in (fn []
                     (case backend
                       :memory  (when-let [kb (:kb (entry key))] (v/clear! kb))
                       :disk-log (disk/close-dir! dir)
                       nil)))
           (catch Exception ex
             (let [why (or (.getMessage ex) (str (class ex)))]
               (trove/log! {:level :warn :id ::unload-problem
                            :msg (str "releasing KB " key ": " why)})
               ;; the entry's own status, and the load job's dropped with it: that job
               ;; finished `:done` and `with-job` prefers it while it is there, so leaving it
               ;; on would report the settled load over the failed release
               (put-entry! key #(-> (dissoc % :job)
                                    (assoc :status :unreleased :finished (now)
                                           :error (str "did not release cleanly — " why))))
               (swap! state update :active #(when (not= % key) %))
               (fall-back-active!)
               (throw (ex-info (str (:name e) " did not release cleanly — " why
                                    ".  It is still listed, and unloading it again retries"
                                    " the release.")
                               {:type :unreleased :key key :backend backend} ex))))))
       (drop-entry! key)
       (fall-back-active!))
     true)))

(defn activate
  "Make entry `key` the one the browser reads.  Anything **holding a KB** can be
  activated, a load still running included; only an entry with no KB yet is refused,
  and that is a statement about there being nothing there rather than about the load.

  A half-loaded KB answers about what has landed, which is a *prefix* and not a wrong
  answer — the ordinary open-world condition this engine is built on, where an absent
  fact never means a false one.  Reading beside the loader is sound for the same reason
  a reader thread beside the writer is: one writer, and every store mutation lands
  atomically (docs/storage.md, the single-writer contract).  What a reader is owed is
  being *told*, which is `active-caveat`'s job and the browser's — not being refused."
  [key]
  (let [e (entry key)]
    (when (:kb e)
      (swap! state assoc :active key)
      true)))

(defn write-blocked?
  "Is `kb` one a loader is still **writing**?

  Reading beside a loader is sound; writing beside one is not.  A store mutation lands
  atomically, so a reader sees a consistent prefix — but two interleaved writers are not
  serializable at all, and this process's one writer is already spoken for while a load
  runs (docs/storage.md, the single-writer contract).  So activating a KB mid-load buys
  a reader everything except the right to change it.

  Asked of the **KB itself** rather than of the active entry, and by identity, because
  those are not the same question: loading a second KB in the background is no reason to
  stop writing to the one on screen, and a caller holding a KB the catalog never heard of
  (a test, an embedding, an `--attach`) is nobody's loader's business.

  Two halves, because a writing job names its KB at two different times.  A job handed one
  — a chaining run — says so at `submit` and the registry answers for it (`jobs/writes-kb?`).
  A **load** opens its own, so the identity is on the entry rather than in the job, and the
  entries are what is walked for those."
  [kb]
  (boolean (and kb
                (or (jobs/writes-kb? kb)
                    (some (fn [e] (and (#{:running :cancelling} (:status (with-job e)))
                                       (identical? kb (:kb e))))
                          (vals (:entries @state)))))))

(defn active-caveat
  "What is provisional about the KB the browser is reading, or nil when nothing is.
  `{:key :name :status :progress :belief?}`.

  Two independent reasons an answer can be less than the whole truth, and a reader is
  owed both:

  - the load is **still running** (or stopped part-way), so what is stored is a prefix
    of what was asked for;
  - **belief and the taxonomy are not built**, which `recover` builds together and
    `:belief? false` skips together.  That empties more than queries: with no JTMS every
    believed answer is empty, and with no genl/genlCx closures there is no type
    hierarchy either, so a fully stored KB renders as one with no types and no contexts
    at all.

  The second outlives the first: a store opened without `:recover?` is `:done` and stays
  that way, and a `:dump` imported with `:belief? false` likewise.  That is why it is
  reported beside the status rather than folded into it — the dangerous case is the one
  that looks finished.  The TMS is what is probed, since the two are built as a pair.

  An empty KB is not beliefless, it is empty; and an entry that is not an in-process KB
  (an attached daemon) has nothing here to report, exactly as `stats` and `footprint`
  have nothing to say about it."
  []
  (let [key (active)
        e   (entry key)
        kb  (:kb e)]
    (when (:records kb)
      ;; a store that cannot even be counted is the *most* caveated state, not the
      ;; least: folded into 0 it read as "nothing stored, nothing to miss" and the
      ;; page rendered a damaged KB as a healthy, fully settled one
      (let [n        (try (v/sentex-count kb) (catch Exception _ ::unreadable))
            ;; `in-datums`, not `datums`: the question is whether anything is
            ;; *believed*, and a node exists per handle after any `recover` — a
            ;; recover over a strength-less store builds every node OUT, which is
            ;; precisely the state this caveat exists to point at
            belief?  (if (= ::unreadable n)
                       false
                       (or (zero? (long n)) (jtms/any-belief? (:tms kb))))
            settled? (and (not= ::unreadable n) (= :done (:status e)))
            ;; Which repair a beliefless KB needs, and the store is the only thing that
            ;; knows.  `recover` reads the premise roster and the justifications out of
            ;; the record store, so a store holding either has everything it needs and
            ;; wants a `recover`; one holding neither cannot be recovered into belief at
            ;; all and has to be loaded again.  Two different instructions, and telling
            ;; the first case to reload sends it back through hours of work for nothing.
            recoverable? (and (not= ::unreadable n)
                              (boolean (or (cap/some-premise-id (:records kb))
                                           (cap/some-justification-id (:records kb)))))]
        (when-not (and settled? belief?)
          {:key key :name (:name e) :status (if (= ::unreadable n) :unreadable (:status e))
           :progress (:progress e) :belief? belief? :recoverable? recoverable?})))))

;; ---- exporting -----------------------------------------------------------
;;
;; The other direction of the same loop.  A dump this process writes is a *source* it can
;; discover, so exporting and reloading is a round trip that never leaves the browser —
;; which is the whole reason export is here rather than only in the CLI.
;;
;; It runs the way a load runs, and for the same reason: it is a job like any other
;; (`vaelii.impl.jobs`) — minutes on a corpus, progress recorded where the panel looks for
;; it, cancelled by the progress callback throwing (`export!` calls it at each chunk
;; boundary, and there is no other point at which stopping leaves a directory rather than a
;; file half-written).  What it is *not* is an entry: an export produces no KB, and filing
;; it as one would put a second handle on a KB somebody could then unload out from under
;; the writer.  Nor does it claim the writer: a dump is written to the filesystem, so a
;; load filling some other KB may run beside it.
;;
;; The two predicates that say an export is running — `exporting?` and `exporting-kb?` —
;; are registry reads and sit up with `loading?`, since `unload!` asks one of them before
;; it releases anything.  It asks under `start-monitor`, which is the monitor the check
;; and the submit below are one step under: an unload and an export are a race over the
;; same stores, and the loser has to be the one that has not started.

(defn export-entry!
  "Write the KB in entry `key` out as a dump in `dir`, on its own thread, and return the
  job.  `opts` are `vaelii.core/export!`'s (`:variant`, `:compression`), plus
  `:run-in` — a wrapper the walk runs inside, which is how the browser hands its write
  monitor so a synchronous write already past the refusals drains before the walk
  starts rather than interleaving with it.

  Three refusals, each about something an export cannot be correct in the face of:

  - **another export is running.**  One at a time, as with loads.  A *load* is not
    refused, and does not refuse this: a load fills some other KB, and blocking on it
    would be a rule about this process's busyness rather than about the dump.
  - **the entry is not an in-process KB.**  A daemon serves its KB from another host, and
    that is where its dump would be written — so the export belongs to that daemon's own
    surface, not to a form here that would name a path on the wrong machine.
  - **the KB is still loading.**  `export!` walks it record by record with no snapshot to
    walk instead, so a dump of a KB something is still writing is a dump of no single
    state.

  The last refusal runs the other way too: while the walk runs, `exporting-kb?`
  answers true for this KB, and the browser's write entry point refuses with it — the job
  claims no writer, so the claim registry cannot say it.  (A daemon's export needs no
  such flag: `serve` files `:export` with the writes, under its own monitor.)

  `!` for what a cancelled one leaves behind: a directory holding part of a dump.  It is
  not a *loadable* dump — `meta.edn` is written last and is what `classify` keys on — but
  it is bytes on disk that nothing here will clean up."
  [key dir opts]
  (when (str/blank? (str dir))
    (throw (ex-info "an export needs a destination directory" {:type :no-destination})))
  ;; the one-at-a-time check and the submit are one step under the monitor: the export
  ;; claims no writer, so the registry's own claim cannot refuse a second one, and two
  ;; requests arriving together would otherwise each read `exporting?` false and both start
  (locking start-monitor
    (when (exporting?)
      (throw (ex-info (str "an export is already running — one runs at a time, since it"
                           " claims no writer and two would interleave over one"
                           " destination.  Wait for it to finish, or cancel it, then"
                           " export")
                      {:type :export-busy})))
    (let [e  (entry key)
          kb (:kb e)]
      (when-not e
        (throw (ex-info (if key
                          (str "no loaded KB " (pr-str key) " — loaded now: "
                               (if-let [ks (seq (map :key (entries)))]
                                 (str/join ", " ks)
                                 "none"))
                          "nothing is loaded to export — load a KB first")
                        {:type :unknown-entry :key key})))
      (when-not (in-process? key)
        (throw (ex-info (str (:name e) " is served by a daemon, so its dump is written on"
                             " that daemon's own host — export it from there")
                        {:type :not-in-process :key key})))
      (when (write-blocked? kb)
        (throw (ex-info (str (:name e) " is still loading — a dump of a KB something is"
                             " still writing is a dump of no single state.  Wait for the"
                             " load to finish, or cancel it, then export")
                        {:type :still-loading :key key})))
      (let [run-in (:run-in opts (fn [work] (work)))
            opts   (dissoc opts :run-in)
            id (jobs/submit
                {:label      (str "Export " (:name e))
                 :kind       :export
                 ;; a dump is bytes on the filesystem, so this claims no writer — claiming
                 ;; one would refuse a load of some *other* KB, which has no bearing on the
                 ;; dump; `exporting-kb?` is how the write entry points refuse for this one.  It is
                 ;; never hard-interrupted either, for the same reason a KB-writing job is
                 ;; not: an interrupt mid-frame leaves a file torn rather than short
                 :result-url "/kbs"
                 :entry      key :name (:name e) :dir (str dir)
                 :variant    (:variant opts :records)
                 :progress   {:phase :starting :done 0}}
                (fn [progress!]
                  (let [summary (run-in #(v/export! kb (str dir) (assoc opts :on-progress progress!)))]
                    (trove/log! {:level :info :id ::exported
                                 :msg (str "exported KB " key " to " (:dir summary))
                                 :data summary})
                    summary)))]
        (jobs/job id)))))

(defn cancel-export!
  "Ask the export that is **running** to stop at its next chunk boundary, and answer
  whether there was one to ask.  `!` because what it leaves behind is a directory holding
  part of a dump.

  Asked of the running set rather than of `jobs/latest`: the panel shows the last export's
  report for an hour after it settles, so the newest export of any status is routinely one
  that finished this morning, and this reports on the dump that is still being written
  rather than on whichever one the panel happens to be showing."
  []
  (boolean (some-> (first (filter #(= :export (:kind %)) (jobs/running)))
                   :id jobs/cancel!)))

(defn register!
  "File an already-built KB as a settled entry and make it active if nothing else is —
  how the browser's own startup KB, and an attached daemon, get into the list beside the
  ones the catalog loads.

  `opts`: `:where` says what unloading it should release (nil for a KB this process does
  not own — an attached daemon is nobody's to close); `:source` names the source it came
  from, so a KB registered at startup shows as *loaded* rather than being offered again."
  ([key name kb] (register! key name kb nil))
  ([key name kb {:keys [where source]}]
   ;; `stats` is a four-read census, computed before the swap for the same reason as
   ;; `load-source`'s: a swap! fn re-runs per retry under contention
   (let [ks (stats kb)]
     (swap! state (fn [s]
                    (-> s
                        (assoc-in [:entries key]
                                  {:key key :name name :status :done :kb kb :where where
                                   :source (or source {:kind :registered}) :started (now)
                                   :finished (now) :stats ks :progress {:phase :done}})
                        (update :order #(vec (distinct (conj % key))))
                        (update :active #(or % key))))))
   key))

(defn reset-registry!
  "Forget every entry, releasing each as `unload!` does, and stop every job.  For a process
  shutting down and for tests; nothing in the browser calls it.

  The export is stopped **first** and waited for, and the entries come second: `unload!`
  clears the stores an entry holds, and an export still walking one of them would be
  reading a KB as it emptied.  `unload!` refuses that outright, so a walk not waited for
  here would take the whole reset down with it rather than merely corrupting a dump.

  One entry refusing to release does not stop the rest: this is what a process shutting
  down calls, and stranding four KBs because the first would not close is the wrong
  trade.  Each refusal is logged and the sweep goes on."
  []
  ;; through `cancel-export!` — its docstring says why `jobs/latest` is the wrong ask
  ;; (the newest export of any status is routinely one that settled this morning)
  (when-let [id (:id (first (filter #(= :export (:kind %)) (jobs/running))))]
    (jobs/cancel! id)
    (jobs/wait id 30000))
  (doseq [k (:order @state)]
    (try (unload! k)
         (catch Exception ex
           (trove/log! {:level :warn :id ::reset-problem
                        :msg (str "resetting the registry, KB " k ": " (.getMessage ex))}))))
  (jobs/reset-registry!)
  (reset! state {:active nil :entries {} :order [] :next-space first-space}))
