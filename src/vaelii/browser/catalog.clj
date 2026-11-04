;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.catalog
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
  | `:core`      | the upper ontology alone, in CxUniverse             | `vaelii.host.core-context` |
  | `:starter`   | the shipped schema-only ontology                    | `vaelii.host.starter` |
  | `:generated` | synthesized from numbers — types, rules, a fwd mix  | `vaelii.host.io.generate` |
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
  half of that is not here: a load is a **job** (`vaelii.browser.jobs`), which is what gives
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
  cleared (they would otherwise hold the corpus for the life of the JVM); every other
  backend is *closed* — the file lock released, the directory left exactly as it was, an
  adapter's connection closed.  The same directory can then be loaded again, or opened by
  another process."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.browser.jobs :as jobs]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.io.generate :as generate]
            [vaelii.host.starter :as starter]
            [vaelii.host.sync :as sync])
  (:import (java.io File)))

;; ---- the shipped sources -------------------------------------------------

(def built-in
  "The sources that need no files beyond the ones in this repo.  `:options` is what the
  UI offers per source, as data: each entry is a form control, and `load-source` reads
  the same keys back out of the params map."
  [{:id      "core"
    :kind    :core
    :name    "Upper vocabulary"
    :blurb   "The upper ontology alone — the predicates the engine interprets and the upper types, all in CxUniverse."
    :scale   "4,500+ sentexes"
    :options []}
   {:id      "starter"
    :kind    :starter
    :name    "Starter ontology"
    :blurb   "The shipped schema: the upper ontology in CxUniverse and the middle theories below it. No individuals."
    :scale   "3,700+ asserted / 4,900+ stored"
    :default? true
    :options []}
   {:id      "generated"
    :kind    :generated
    :name    "Generated corpus"
    :blurb   "A synthetic KB of a chosen shape — types, individuals, rules, a forward/backward mix — deterministic in its seed."
    :scale   "as large as you ask for"
    :repeat? true                                        ; loadable many times over, at different shapes
    :options (concat
              [{:key :base :type :choice :label "Base vocabulary" :default "core"
                :choices [["core" "Upper vocabulary"] ["starter" "Starter ontology"]]}]
              (for [k generate/knobs] (assoc k :type :slider))
              [{:key :seed :type :number :label "Seed" :default 1 :min 0 :max 1000000}
               {:key :chain? :type :flag :label "Forward-chain after loading" :default false}
               {:key :max-derivations :type :number :label "Derivation cap"
                :min 1000 :max 100000000 :step 1000 :placeholder "generator default"
                :help "chaining is by far the longest phase of a chained load; left empty, the generator's own default applies (`vaelii.host.io.generate/defaults`)"}])}])

(def ^:private corpus-options
  [{:key :profile :type :choice :label "Profile" :default "ontology"
    :choices [["ontology" "Ontology (drops the lexical layers)"]
              ["core" "Core (Cyc's own upper vocabulary)"]
              ["full" "Full (everything, including natural language)"]]}
   {:key :bulk? :type :flag :label "Bulk load (skip the per-fact checks)" :default false}
   {:key :chain? :type :flag :label "Forward-chain after loading" :default false}
   ;; no default: a load chains to its fixpoint unless the reader sets a cap
   {:key :max-derivations :type :number :label "Derivation cap"
    :min 1000 :max 100000000 :step 1000 :placeholder "to a fixpoint"
    :help "chaining a corpus is by far the longest thing a load can do; left empty, it runs to its fixpoint, and a run that hits a cap is reported as truncated"}])

;; `recover` rebuilds the JTMS *and* the cached taxonomy, so skipping it costs more than
;; belief: a dump loaded without it has no genl or genlCx closure, `types` and `contexts`
;; are empty and the ontology page has nothing to draw (on the OpenCyc import `docs/kbs.md`
;; measures, off gives 0 types and 0 contexts, on gives 132,391 and 13,202).  Three values,
;; not a checkbox: the middle one serves a corpus that cannot afford the rebuild *today*
;; and keeps its justifications, and for a foreign dump it is the only value that does (see
;; `import-records-only!`).
(defn- belief-mode
  "What the form's `:belief?` choice means to `import-dump`.  The form speaks in verbs
  (`:rebuild` / `:stored` / `:skip`), since a checkbox cannot offer three answers; the
  importer's own vocabulary passes through.  **Anything else is handed on unchanged**, so
  `import-dump`'s refusal (`:unknown-option`, `import/belief-modes`) stays reachable:
  defaulting would turn `{:belief? :store}`, one letter off `:stored`, into the cheapest
  records-only load.  Only an **absent** choice takes the form's default."
  [v]
  (case v
    (:rebuild true)  true
    :stored          :stored
    (:skip false nil) false
    v))

(def ^:private sync-option
  {:key :sync? :type :flag :label "Sync the shipped contexts into it (writes; slow on a large KB)"
   :default false
   :help "off leaves the KB as it was written; on brings its CxUniverse and kb/middle contexts to what this engine ships, one edit and one settle over the whole KB, which on a corpus of millions of sentexes can outlast the session and leaves a store's images stale"})

(def ^:private dump-options
  [{:key :belief? :type :choice
    :label "Belief and the taxonomy"
    :default :skip
    :choices [[:rebuild "Rebuild now (slow — a JTMS node per sentex)"]
              [:stored  "Store it, rebuild later"]
              [:skip    "Skip it (records and index only)"]]
    :help "\"rebuild now\" is the finished KB. \"store it\" reads and stores every justification and premise mark but leaves the TMS and the genl/genlCx closures empty, so the KB is findable and countable now and can be recovered later without re-reading the dump. \"skip it\" never reads the justification stream, and for a dump in a foreign dialect that is permanent — nothing a later recover could rebuild belief from is stored"}
   sync-option])

(defn request-paths?
  "May a request name a directory for this process to write (`VAELII_REQUEST_PATHS`,
  default off)?  Off, a durable load's store and an export's dump go under `write-root`
  with a name `server-dir` picks, and the browser refuses a request that names one."
  []
  (v/switch-value "VAELII_REQUEST_PATHS"))

(defn- target-options
  "The controls that say where a corpus or dump load goes: `:durable?`, plus a `:dir`
  path when `request-paths?` is on."
  []
  (cond-> [{:key :durable? :type :flag :label "Durable (a :disk-log KB on disk)" :default false
            :help "off loads into memory; on writes a :disk-log store under the KB directory, named by the server"}]
    (request-paths?)
    (conj {:key :dir :type :path :label "Target directory" :default ""
           :help "a path on this machine for the :disk-log store; empty leaves the choice to the durable flag"})))

(def ^:private store-options
  [{:key :recover? :type :flag :label "Recover belief and the taxonomy on open (slow)" :default false
    :help "off opens the records and index as they stand: no genl/genlCx closure, and belief-filtered queries answer nothing"}
   sync-option])

;; ---- discovery -----------------------------------------------------------

(defn- file-at ^File [dir & parts] (apply io/file dir parts))

(defn- readable-edn
  "`f` read as EDN, or nil: a malformed or unreadable file makes a directory *not* a source
  rather than an error.  **The size bound is the one error**: `v/read-manifest` refuses past
  its byte bound, and that refusal travels with the file named, so a gigabyte `meta.edn` is
  not silently skipped as \"not a KB\"."
  [^File f]
  (when (.isFile f)
    (try (v/read-manifest f)
         (catch clojure.lang.ExceptionInfo e
           (if (= :manifest-too-large (:type (ex-data e))) (throw e) nil))
         (catch Exception _ nil))))

(defn classify
  "The kind of KB in directory `d`, or nil.  Reads the marker each writer leaves: a corpus's
  `meta.edn` carries the context order, a dump's carries a `:format-version`, and a vaelii
  store is a `records/` directory with its own `format.edn`.  **The records half is the
  whole marker**: only `:disk-log` keeps a durable `index/`, and `:disk-columnar`,
  `:disk-dense` and `:disk-memory` write none.  A KB whose records are on a server
  (`:pg-disk-log`, `:pg-snapshot`) has no `records/` here; its marker is
  `index/records.edn`, which `open-kb` reopens it from."
  [^File d]
  (when (.isDirectory d)
    (let [m (readable-edn (file-at d "meta.edn"))]
      (cond
        (and (map? m) (:context-order m))                                :corpus
        (and (map? m) (or (:format-version m) (:variant m)))             :dump
        (some? (readable-edn (file-at (file-at d "records") "format.edn"))) :store
        (some? (readable-edn (file-at (file-at d "index") "records.edn")))  :store))))

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
  size on disk is what the catalog shows instead."
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
  (`vaelii.impl.foreign`), and a KB this build cannot read produces a load that
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
                          :options (into corpus-options (target-options))})
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
                          :options (into dump-options (target-options))})
               :store  {:blurb "An on-disk vaelii KB, opened in place — no import, no copy."
                        :scale (human-bytes (du d))
                        :options store-options})))))

(defn- set-to
  "A switch's value, or nil when it is unset.  **Blank is unset**, as for every other switch
  (`vaelii.impl.config`'s `raw`, `guard/api-token`): an empty `VAELII_KB_PATH` would split
  to nothing and leave discovery with no directory.  A fn over the value, not the switch's
  *name*, because the configuration-surface scan reads `System/getenv \"VAELII_…\"`
  literals."
  [v]
  (not-empty (str/trim (str v))))

(defn search-path
  "The directories discovery walks: `VAELII_KB_PATH` when set, else the
  `vaelii.kb.path` system property, else `./kbs` and `~/.vaelii/kbs`.  The list is
  separated as the platform's `PATH` is — `:`, and `;` on Windows, where `:` is part of
  every absolute path.  A path entry that
  *is* a KB directory counts as one source; otherwise its children are probed, one level
  down.  (The property mirrors `vaelii.disk.dir`, and is what a test sets — a JVM cannot
  change its own environment.)  Either spelling **blank** is unset — `set-to` for why."
  []
  (if-let [p (or (set-to (System/getenv "VAELII_KB_PATH"))
                 (set-to (System/getProperty "vaelii.kb.path")))]
    (remove str/blank? (str/split p (re-pattern (java.util.regex.Pattern/quote File/pathSeparator))))
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
  "How many directories one search-path entry is probed for, at most.  Every candidate costs
  a `classify` (a `meta.edn` read) and, for a `:store`, a size estimate on **every** `/kbs`
  request, since `sources` is recomputed per call.  Nothing else in the browser renders an
  uncapped list (docs/web.md, \"Long lists continue\").  The cap bounds the cost and does
  not curate."
  200)

(defn sources
  "Every KB this process can load, built-ins first: the shipped ontologies and the
  generator, then the catalog file's entries, then the search path's.  Recomputed per call,
  so a corpus dropped into a search-path directory appears on the next page load.  A
  search-path entry holding more than `max-discovered` candidates is probed for the first
  `max-discovered` by name, and what was passed over is **named** on the vector's metadata
  as `:truncated` and in the log.  The built-ins and the catalog file's entries are never
  capped."
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

;; ---- where the server writes --------------------------------------------

(defn write-root
  "The directory a store or a dump the request did not name goes under: the first
  search-path entry that is not itself a KB, so a dump written there is a `:dump` source
  the moment it lands.  Nil when every entry is a KB."
  ^File []
  (first (remove classify (map io/file (search-path)))))

(defn- server-dir
  "A directory under `write-root` that does not exist yet: `stem` with every character
  outside `[A-Za-z0-9_-]` turned to `-`, then the local time to the second, then `-2`,
  `-3`… past a name already taken.  Throws `:no-destination` when `write-root` is nil."
  ^File [stem]
  (let [root (or (write-root)
                 (throw (ex-info (str "nowhere to write: every KB search-path entry ("
                                      (str/join ", " (search-path)) ") is itself a KB."
                                      "  Name a directory in VAELII_KB_PATH to write under")
                                 {:type :no-destination})))
        base (str (str/replace (str stem) #"[^A-Za-z0-9_-]" "-") "-"
                  (.format (java.time.format.DateTimeFormatter/ofPattern "yyyyMMdd-HHmmss")
                           (java.time.LocalDateTime/now)))]
    (first (remove #(.exists ^File %)
                   (cons (io/file root base)
                         (map #(io/file root (str base "-" %)) (iterate inc 2)))))))

;; ---- the registry --------------------------------------------------------
;; One atom holds every loaded (and loading) KB, which is active, and the next free memory
;; space.  A memory-backed KB is keyed by space number for the life of the JVM
;; (`vaelii.impl.memory`), so two resident KBs need different numbers, which start well
;; clear of the block the test suite owns.

(def ^:private first-space 100)

(defonce ^:private state (atom {:active nil :entries {} :order [] :next-space first-space}))

;; `load-source`'s claim is a read-test-write across two touches of `state`, which one
;; `swap!` cannot express.  This makes the key pick, the already-loaded test and the
;; registration one step.  `export-entry!`'s one-export-at-a-time check (`exporting?`, then
;; `jobs/submit`) takes the same monitor, so two export requests cannot both pass it.
;; `unload!`'s export test takes it too, since its check and `export-entry!`'s read
;; *different* registries.  The claim that only one job writes at a time is the registry's,
;; under its own monitor, and nothing here takes the two in the other order.
(defonce ^:private start-monitor (Object.))

;; The KBs `unload!` has released, so a write that resolved one before the release can be
;; refused after it (`released?`).  Weak keys: an entry lasts while something still holds
;; the KB value, which is exactly while a late write could still reach it.  A KB is a
;; record whose atoms compare by identity, so two KB values are equal only when they are
;; the same KB.
(defonce ^:private released-kbs
  (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn- now [] (System/currentTimeMillis))

(defn claim-space!
  "The next free `:space` number."
  []
  (dec (:next-space (swap! state update :next-space inc))))

(defn- put-entry!
  "Apply `f` to entry `key` — **and only while the registry still holds it**.  Nothing here
  creates an entry (`load-source` and `register!` both do that with their own `assoc-in`),
  so an update reaching a dropped key would not fail: it would *recreate* the entry as a
  fragment with no `:key` and no `:started`, which `public-entry` subtracts from.  Reachable
  because a load's own thread writes here as it unwinds, and `unload!` may have dropped
  the entry in between."
  [key f]
  (swap! state (fn [s] (cond-> s (contains? (:entries s) key) (update-in [:entries key] f))))
  key)

(defn- with-job
  "An entry's own fields, plus the four its **job** owns: where the load has got to, what
  became of it, and when.  A load reports through the registry like every other long
  operation, so the panel and the loader read one answer.  An entry `register!` filed, or
  one whose job has aged out, carries its own settled status (`load-source` files the
  terminal status onto the entry as it finishes)."
  [e]
  (if-let [j (jobs/job (:job e))]
    (merge e (select-keys j [:status :progress :error :finished]))
    e))

(defn entry
  "One entry, whole (`:kb` included) — for a caller that wants the KB itself."
  [key]
  (with-job (get-in @state [:entries key])))

(defn- public-entry
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
  "Every entry, in load order, as public entries."
  []
  (let [{:keys [entries order]} @state]
    (into [] (keep #(public-entry (get entries %))) order)))

(defn active
  "The key of the active entry, or nil."
  []
  (:active @state))

(defn active-entry [] (public-entry (entry (active))))

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

(defn live-kbs
  "Every KB open in *this* JVM — the records whose per-KB caches a process-wide sweep
  reaches.  An attached daemon's entry holds a remote handle with no local caches, so
  `:records` tells the two apart, the way `in-process?` does for one key."
  []
  (into [] (keep (fn [e] (let [kb (:kb e)] (when (:records kb) kb))))
        (vals (:entries @state))))

(defn install-memory-guard!
  "Attach the cache memory-pressure guard, feeding it this catalog's live KBs so the trim
  reaches their per-KB caches (`vaelii.core/install-memory-guard!`).  The browser
  calls this at startup; the guard holds no list of open KBs of its own, since the engine
  does not."
  []
  (v/install-memory-guard! {:kbs live-kbs}))

(defn entry-of
  "The entry holding `kb`, or nil for a KB this registry never heard of.  By identity,
  like `exporting-kb?` and `write-blocked?`."
  [kb]
  (when kb
    (let [{:keys [entries order]} @state]
      (some #(let [e (get entries %)] (when (identical? kb (:kb e)) e)) order))))

(defn name-of
  "What to call `kb` — the name of the entry holding it (`entry-of`), or nil.

  A page that has *resolved* a KB and judged it asks this rather than `active-entry`:
  `activate` re-points the holder at any moment and takes no monitor, so the active entry
  a moment later can be a different KB — and a refusal that named it would name the KB it
  did not judge."
  [kb]
  (:name (entry-of kb)))

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
  "Is `kb` the one a running export is still walking?  Asked by identity, as
  `write-blocked?` is, and its reciprocal: `export-entry!` refuses to *start* while a loader
  writes the KB, and this lets the write entry points refuse while the walk runs, since the
  walk fetches record by record with no snapshot.  `unload!` reads it too."
  [kb]
  (boolean (and kb
                (some #(and (= :export (:kind %))
                            (identical? kb (:kb (entry (:entry %)))))
                      (jobs/running)))))

(defn released?
  "Did `unload!` release `kb`'s stores (clear a memory KB, or close a disk one)?  A write
  parked on the browser's write monitor while an unload released its KB asks this once it
  holds the monitor, and is refused.  The question is \"was this KB released\", not \"does
  the catalog hold it\": a KB the catalog never held is never refused.  An unload that
  releases nothing marks nothing, and `register!` clears the mark of a KB it files again."
  [kb]
  (boolean (and kb (.containsKey ^java.util.Map released-kbs kb))))

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
      (let [owed        (v/owed-releases kb)
            unsupported (v/unsupported kb)]
        (cond-> {:contexts (count (v/contexts kb))
                 :sentexes (v/sentex-count kb)
                 :types    (count (v/types kb))
                 :terms    (v/term-count kb)}
          ;; the withheld mints an open or a bulk load left undrawn (`v/release-withheld!`)
          (pos? owed) (assoc :owed-releases owed)
          ;; the records the open found nothing supporting (`v/remove-unsupported!`)
          (pos? (:n unsupported)) (assoc :unsupported unsupported)))
      (catch Exception e
        {:error (.getMessage e)}))))

;; ---- memory --------------------------------------------------------------
;; `heap` is a **measurement** of the whole JVM (every KB, the browser, uncollected
;; garbage); `footprint` is an **estimate** for one KB, since attributing heap to one KB
;; would mean unloading it and diffing.  The two are kept apart.

(def resident-bytes-per-sentex
  "What one stored sentex costs in RAM, per resident component: the coefficients
  `footprint` multiplies out, measured on a real-assert load through `bench-scale` and
  `bench-memory`.  Resident size is linear in the sentex count, so the estimate takes one
  coefficient per component.  The main error term is the sentence's shape: a
  fact of arity 2 with no compound arguments indexes at ~1,549 B and a richer one at
  ~2,158 B; the leaner figure is used, so a corpus of fat sentences reads low.  The `:tms`
  figure is the **dense** network's, the default (the reference map is ~467 B/sentex,
  ~3.8× more): `18 B/node + 166 B/justification`, so ~101 per stored sentex at j/n≈0.5.  A
  justification-heavy KB reads low; the coefficient never counts justifications on the
  render path."
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
  with no in-process KB (an attached daemon holds its corpus in another process).  Nothing
  is measured (`resident-bytes-per-sentex`), and the sentex count is the trie's root count,
  O(1).  The belief check is not free: a `{:tms :dense}` KB answers `-datums` by draining
  its node bitmap into a vector of boxed Longs, an allocation per stored sentex per render.
  Two adjustments: a `:disk-log` KB drops the record term (its bounded hot-record LRU does
  not grow with the corpus), and a KB loaded without belief drops the TMS term."
  [key]
  (let [e  (entry key)
        kb (:kb e)]
    (when-let [n (when (:records kb) (try (v/sentex-count kb) (catch Exception _ nil)))]
      (let [paged?   (= :disk-log (:backend (:where e)))
            belief?  (:network? (v/store-state kb #{:network?}))
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
  when the params name a directory (`start-load` names one for `:durable?`) — a durable
  `:disk-log` one there.  Returns
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
  (let [st (v/store-state kb #{:readable?})]
    (when-not (:readable? st)
      (throw (ex-info (str "the store at " path " holds records this build cannot read"
                           " — they thaw as " (pr-str (:thawed-keys st))
                           ", not as sentexes.  It was written by a build whose record"
                           " classes differ; re-import it from a dump.")
                      {:type :unreadable-store :path path})))))

(defn- chain-asked
  "Forward-chain `kb` when the form asked for it, folding what it derived into `summary`.
  The corpus loader asserts with `:chain? false`, and this is the pass at the end
  (docs/catalog.md, \"A chained load chains once, at the end\").  The phase reports no
  total, since a fixpoint's agenda grows as it derives.  `:max-derivations` bounds it,
  and a truncated run says so in the summary.  The run is called with `:on-stop :keep`,
  so a cancel or the cap leaves what it placed for `unload!` to release."
  [kb params progress! summary]
  (if-not (:chain? params)
    summary
    (let [note (fn [pending] (if pending
                               (format "derived · %,d on the agenda" (long pending))
                               "forward chaining to a fixpoint"))
          _    (progress! {:phase :chaining :done 0 :total nil :note (note nil)})
          r    (v/forward-chain
                kb (cond-> {:on-stop     :keep
                            :on-progress (fn [{:keys [derived pending]}]
                                           (progress! {:phase :chaining :total nil
                                                       :done (or derived 0)
                                                       :note (note pending)}))}
                     (:max-derivations params) (assoc :max-derivations
                                                      (:max-derivations params))))]
      (assoc summary :derived (:derived r 0) :truncated? (boolean (:truncated? r))))))

(defn- option-default
  "The `:default` the option `key` declares in `options` — the value the card's form fills
  in, and so the value a caller that names none is given, which keeps a card's load and
  a `load-dir` or `load-source` with the key absent the same load."
  [options key]
  (:default (first (filter #(= key (:key %)) options))))

(defn- noting-log-fn
  "A Trove `*log-fn*` that files each `:info`-or-louder message's text as the job's
  progress `:note`, then hands the call on to `prior` (nil when nothing was installed).
  A store's open reports nothing through `:on-progress`, but a large one logs each
  recover step and each image install, and those lines are what the card can show.

  Never throws: a log site is not a cancellation point, and `progress!` throwing there
  would unwind an open from inside the engine's own bookkeeping.  A cancel asked during
  the open is honoured at the load's next progress report instead."
  [progress! prior]
  (fn [ns coords level id payload_]
    (when (#{:info :warn :error :fatal :report} level)
      (when-let [msg (:msg (force payload_))]
        (try (progress! {:phase :open :note msg})
             (catch Exception _ nil))))
    (when prior (prior ns coords level id payload_))))

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
                  (progress! {:phase :vocabulary :done 0 :note "the upper ontology"})
                  (core-context/load-into kb)
                  {})
      :starter  (let [kb (open!)]
                  (progress! {:phase :ontology :done 0 :note "the shipped schema"})
                  (starter/load-into kb)
                  {})
      :generated (generate/load-into (open!) params {:on-progress progress!})
      :corpus   (let [kb (open!)]
                  (progress! {:phase :vocabulary :done 0 :note "the upper ontology"})
                  (core-context/load-into kb)
                  ;; the corpus reader ships as a plugin, so it is asked for rather
                  ;; than required (docs/foreign.md).  Its own `:chain?` chains per
                  ;; assertion, which is not what the option offers — `chain-asked` says
                  ;; why the pass belongs at the end
                  (chain-asked
                   kb params progress!
                   (v/load-foreign!
                    kb :cyc-corpus path
                    {:profile     (keyword (or (:profile params)
                                               (option-default corpus-options :profile)))
                     :bulk?       (boolean (:bulk? params))
                     :chain?      false
                     :on-progress progress!})))
      ;; passed through rather than coerced: `:belief?` has three values and a `boolean`
      ;; here would read `:stored` as `true` and run the recover the caller asked to defer
      :dump     (v/import! (open!) path {:belief?     (belief-mode (:belief? params))
                                         :on-progress progress!})
      ;; A store is already a KB: opening it *is* the load.  Opening is not quick at scale
      ;; (the record log is scanned, the index rebuilt) and takes no `:on-progress`, so
      ;; say what is happening first and file each line the engine logs as the card's note
      ;; (`noting-log-fn`).  The backend is read off the store's layout: a `:disk-columnar`
      ;; store opened as `:disk-log` surfaces no records (docs/storage.md).
      ;;
      ;; The open takes `open-kb`'s default `:recover? :trust`: an image an earlier engine
      ;; build wrote is installed and kept, writable at once; `lein cli upgrade` is where a
      ;; store pays a recover on purpose (docs/storage.md, "Trusting an image").  A
      ;; recovered `:snapshot` store opens with an operation log, so a process killed with
      ;; no close reopens by replaying its writes (docs/storage.md, "The operation log").
      :store    (let [backend  (v/store-backend path)
                      recover? (boolean (:recover? params))
                      _  (progress! {:phase :open :done 0
                                     :note (if recover?
                                             "opening the store and recovering belief and the taxonomy"
                                             "opening the store — records only, recover to build belief")})
                      kb (binding [trove/*log-fn* (noting-log-fn progress! trove/*log-fn*)]
                           (v/open-kb (cond-> {:backend backend :dir path :reasoners :stored}
                                        (not recover?) (assoc :recover? false)
                                        (and recover? (#{:disk-snapshot :pg-snapshot} backend))
                                        (assoc :oplog? true))))]
                  (note-kb! kb {:backend backend :dir path :attached? true})
                  (check-readable! kb path)
                  {})
      (throw (ex-info (str "unknown KB source kind " (pr-str kind) " — want :core,"
                           " :starter, :generated, :corpus, :dump or :store")
                      {:type :unknown-source :kind kind})))))

(defn- sync-op-note
  "One change of a step-by-step sync as a job's progress note."
  [{:keys [op context form]}]
  (let [f (pr-str form)]
    (str (name op) " " (if (< 120 (count f)) (str (subs f 0 119) "…") f) " in " context)))

(defn- sync-now!
  "Sync `kb`'s shipped contexts, file the report on entry `key` as `:sync` and log it.
  Returns the report.  Given a job's `progress!`, one change at a time (`sync/sync-each!`):
  the plan's size, then each change, with a cancel landing between two changes.  Without
  one, the one batch (`sync/sync!`).  A sync that throws is filed and logged as
  `{:error message}`, not rethrown, since the KB loaded; a cancel is rethrown.  `ships` is
  `sync/premises`, read once by a caller that syncs more than one KB."
  ([key kb] (sync-now! key kb nil nil))
  ([key kb ships] (sync-now! key kb ships nil))
  ([key kb ships progress!]
   (let [ships  (or ships (sync/premises))
         report (try (if progress!
                       (sync/sync-each! kb ships
                                        (fn [{:keys [done total op]}]
                                          (progress! (cond-> {:phase :sync :done done :total total}
                                                       op (assoc :note (sync-op-note op))))))
                       (sync/sync! kb ships))
                     (catch Exception e
                       (if (jobs/cancelled? e)
                         (throw e)
                         {:error (or (ex-message e) (str (class e)))})))]
     (put-entry! key #(assoc % :sync report))
     (trove/log! {:level (if (or (:error report) (seq (:refused report))) :warn :info)
                  :id    ::shipped-synced
                  :msg   (if-let [err (:error report)]
                           (str "the shipped contexts of " key " were not synced: " err)
                           (str "synced the shipped contexts of " key ": " (:added report)
                                " added, " (:removed report) " retracted, "
                                (count (:refused report)) " refused"))
                  :data  (assoc report :key key)})
     report)))

(defn- sync-after-rebuild!
  "Sync `kb`'s shipped contexts once the belief rebuild behind its image finishes, as a
  writing job of its own.  A daemon thread waits for `v/write-hazards` to empty, and gives
  up when the rebuild fails or the entry stops holding `kb` (it was unloaded).  A writer
  held by another job is waited out, since the sync is owed to this KB whenever it runs."
  [key kb]
  (doto (Thread.
         ^Runnable
         (fn []
           (loop []
             (cond
               (not (identical? kb (:kb (entry key)))) nil

               (:failed (v/rebuild-progress kb))
               (trove/log! {:level :warn :id ::shipped-synced
                            :msg (str "the shipped contexts of " key " were not synced: the"
                                      " belief rebuild failed, and writes stay refused")
                            :data {:key key}})

               (seq (v/write-hazards kb))
               (do (Thread/sleep 2000) (recur))

               :else
               (when (= ::busy
                        (try (jobs/submit {:label  (str "Sync the shipped contexts of " key)
                                           :kind   :sync
                                           :writes kb
                                           :entry  key}
                                          (fn [progress!] (sync-now! key kb nil progress!)))
                             (catch clojure.lang.ExceptionInfo e
                               (if (= :job-busy (:type (ex-data e))) ::busy (throw e)))))
                 (Thread/sleep 2000)
                 (recur)))))
         (str "vaelii-shipped-sync " key))
    (.setDaemon true)
    (.start)))

(defn- follows-shipped?
  "Does entry `e` follow the shipped files?  A KB built from this engine's own files
  does.  A loaded store or dump does only when its load asked for it (`:sync?`): a sync
  is an `edit!` and a settle over the whole KB, which on a corpus of millions of
  sentexes outlasts the session, and every record it writes before it is stopped stays
  in the store and leaves its images stale."
  [e]
  (or (not (#{:store :dump} (get-in e [:source :kind])))
      (true? (get-in e [:params :sync?]))))

(defn- sync-shipped
  "Bring a loaded store's or dump's shipped contexts up to this engine's
  (`vaelii.host.sync`) when its load asked for it (`:sync?`, `follows-shipped?`): inline
  when `kb` accepts writes, which a served browser's recover leaves it doing, and after
  the rebuild when belief is being rebuilt behind an image.  A store opened without a
  recover accepts no writes and is left as it is.  The other source kinds are built from
  this engine's own files and are already in sync.  Returns the report,
  `{:deferred true}`, or nil."
  [key {:keys [kind]} params progress!]
  (when-let [kb (and (#{:store :dump} kind) (:sync? params) (:kb (entry key)))]
    (let [hz (v/write-hazards kb)]
      (cond
        (empty? hz)
        (do (progress! {:phase :sync :done 0 :note "planning the sync of the shipped contexts"})
            (sync-now! key kb nil progress!))

        (:stale-belief hz)
        (do (sync-after-rebuild! key kb)
            {:deferred true})))))

(defn sync-loaded!
  "Sync the shipped contexts of every entry that holds a KB in this process and accepts
  writes, as one `:sync` job: the shipped files are read once (`sync/premises`), and
  each entry's report is filed on it as `:sync` (`sync-now!`).  What the development
  browser runs when a shipped KB file changes on disk (`vaelii.browser.web`).  A store or
  dump loaded without `:sync?` is not one of them (`follows-shipped?`).  Returns the job
  id, or nil when no entry qualifies.  Throws `{:type :job-busy}` while another job holds
  this process's writer."
  []
  (let [ks (filterv #(and (in-process? %) (follows-shipped? (entry %))
                          (empty? (v/write-hazards (:kb (entry %)))))
                    (:order @state))]
    (when (seq ks)
      (jobs/submit {:label  "Sync the shipped contexts of every loaded KB"
                    :kind   :sync
                    :writes true}
                   (fn [_]
                     (let [ships (sync/premises)]
                       {:synced (into {} (for [k ks :let [kb (:kb (entry k))] :when kb]
                                           [k (sync-now! k kb ships)]))}))))))

(defn sync-entry!
  "Sync the shipped contexts of entry `key` as a `:sync` job, whatever its load asked,
  one change at a time with each reported, filing the report on it as `:sync`
  (`sync-now!`), and return the job id.  How a store
  or dump loaded without `:sync?` is brought current on purpose.  Throws
  `:unknown-source` when no entry `key` holds a KB in this process, `:unrecovered-kb` when
  that KB accepts no writes (`v/write-hazards`), and `{:type :job-busy}` while another job
  holds this process's writer."
  [key]
  (let [kb (and (in-process? key) (:kb (entry key)))]
    (when-not kb
      (throw (ex-info (str "no KB in this process is filed as " (pr-str key))
                      {:type :unknown-source :key key})))
    (when-let [hz (not-empty (v/write-hazards kb))]
      (let [msg (str "sync-entry! into " key ", which accepts no writes: "
                     (pr-str (sort (keys hz))) " (v/write-hazards)")]
        (throw (ex-info msg {:type      :unrecovered-kb
                             :hazards   (vec (sort (keys hz)))
                             :operation 'sync-entry!
                             :repair    (if (:no-index hz) 'reindex 'recover)
                             :message   msg}))))
    (jobs/submit {:label  (str "Sync the shipped contexts of " key)
                  :kind   :sync
                  :writes kb
                  :entry  key}
                 (fn [progress!] (sync-now! key kb nil progress!)))))

(defn held-premises
  "`sync/held` of entry `key`'s KB, or nil unless that KB is in this process and
  accepts writes."
  [key]
  (when-let [kb (and (in-process? key) (:kb (entry key)))]
    (when (empty? (v/write-hazards kb))
      (sync/held kb))))

(defn write-back!
  "Write to the shipped files what entry `key`'s KB holds in its exact contexts and `base`
  does not, and remove what `base` holds and the KB does not (`sync/write-back!`).
  `base` is an earlier `held-premises` of the same entry.  Returns `[held report]`, the
  report nil when nothing changed, or nil when `held-premises` is."
  [key base]
  (when-let [now (held-premises key)]
    (let [changes {:add    (vals (apply dissoc now (keys base)))
                   :remove (vals (apply dissoc base (keys now)))}]
      [now (when (or (seq (:add changes)) (seq (:remove changes)))
             (sync/write-back! (:kb (entry key)) changes))])))

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

(def ^:private max-entries
  "How many entries the catalog holds at most.  `start-load` refuses a load past it with
  `:too-many-kbs` instead of evicting one: a loaded KB is one a reader chose to open, and
  unloading it unasked loses their work.  `register!` files past it, since only a start
  or an attach calls that."
  16)

(defn- drop-entry!
  "Forget entry `key` — the registry half of `unload!`, and what a load that never started
  leaves behind."
  [key]
  (swap! state (fn [s]
                 (-> s
                     (update :entries dissoc key)
                     (update :order #(vec (remove #{key} %)))
                     (update :active #(when (not= % key) %))))))

(defn- start-load
  "Start loading the source map `src` under `params`, as a job, and return the entry key.
  `activate?` makes the entry active when the load finishes; without it the entry becomes
  active only when no other entry is.  `load-source` and `load-dir` share this."
  [src params activate?]
  ;; Pick the key, check and claim under one monitor.  The already-loaded test and the
  ;; `swap!` that registers the entry are two touches of `@state`, so two requests on
  ;; Jetty's pool could each pass both and spawn two loaders over the same stores.  The key
  ;; is picked inside too: a `:repeat?` source's suffix is one past the highest
  ;; *registered*, so two generated loads keyed outside would both read `generated#1`.  A
  ;; *second load* is refused a layer down, by the writer claim in the registry.
  (locking start-monitor
    (let [key    (entry-key src)
          ;; `:durable?` with no `:dir` names one here, under the monitor, so two loads
          ;; cannot pick one name
          params (cond-> params
                   (and (:durable? params) (str/blank? (str (:dir params))))
                   (assoc :dir (str (server-dir key))))]
      (when (entry key)
        (throw (ex-info (str (:name src) " is already loaded — unload it first")
                        {:type :already-loaded :key key})))
      (let [held (:order @state)]
        (when (>= (count held) max-entries)
          (throw (ex-info (str "the catalog holds " (count held) " KBs, its most ("
                               (str/join ", " held) ") — unload one first")
                          {:type :too-many-kbs :max max-entries :entries held}))))
      ;; The status and progress here are what an entry reads for the moment between being
      ;; registered and its job's id landing on it — `with-job` prefers the job the instant
      ;; there is one.  Not redundant: a caller rendering an entry in that interval would
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
                    ;; The entry outlives its job's report (a settled job ages out of the
                    ;; registry after an hour), so the status the entry keeps of its own has
                    ;; to be the settled one.  A fallback still reading `:running` would make
                    ;; the browser refuse every write to the KB (`write-blocked?`) and
                    ;; `unload!` refuse `:still-stopping`, for ever.
                    (try
                      (let [note-kb! (fn [kb where] (put-entry! key #(assoc % :kb kb :where where)))
                            summary  (run-load src params progress! note-kb!)
                            ;; while the entry still reads `:running`, so the browser's
                            ;; writes wait for it (`write-blocked?`)
                            _        (sync-shipped key src params progress!)]
                        ;; A cancelled or failed load leaves what had landed in its stores;
                        ;; `unload!` takes those down.  `:progress` settles with the status
                        ;; as on the job (the placeholder reads `:starting`).  `stats` is a
                        ;; four-read census, so it runs BEFORE the swap: a swap! fn must be
                        ;; cheap and retryable (`start-monitor`'s own argument).
                        (let [ks (some-> (get-in @state [:entries key]) :kb stats)]
                          (put-entry! key #(assoc % :summary summary :stats ks
                                                  :status :done :finished (now)
                                                  :progress {:phase :done})))
                        (swap! state (fn [s] (cond-> s (or activate? (nil? (:active s))) (assoc :active key))))
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
          (throw t))))))

(defn load-source
  "Start loading the source with id `source-id` under `params`, as a job.  Returns the
  entry key, or throws when the id names no source, the source is already loaded, or
  another job holds this process's writer.

  The entry is registered `:running` before this returns, so the caller can render it
  immediately; `entries` then reports the job's progress until it settles into `:done`
  (the KB is queryable, and activated when nothing else is) or `:failed` / `:cancelled`."
  ([source-id] (load-source source-id {}))
  ([source-id params]
   (start-load (or (source source-id)
                   (throw (ex-info (str "no KB source " (pr-str source-id) " — the built-in"
                                        " ids are \"core\", \"starter\" and \"generated\";"
                                        " anything else is named in the catalog file or"
                                        " found on the search path (docs/catalog.md)")
                                   {:type :unknown-source})))
               params false)))

(defn load-dir
  "Start loading the KB directory at `path` under `params`, as a job, and make it the
  active KB when the load finishes.  Returns the entry key.  The search path and the
  catalog file need not list `path`: the directory is classified as discovery classifies
  one, so `params` are that kind's options (`{:recover? true}` for a store).  Throws
  `:unknown-source` when `path` holds no KB, and otherwise what `load-source` throws."
  [path params]
  (start-load (or (discovered-source (io/file path))
                  (throw (ex-info (str "no KB at " path " — a KB directory holds a store's"
                                       " records/, or a dump's or a corpus's meta.edn")
                                  {:type :unknown-source :path (str path)})))
              params true))

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
  vouch for, and falling to it would put the browser straight back on it.

  The test and the fall are one `swap!`, so an `activate` landing between them is not
  overwritten.  The statuses are read before it, since a status is the load job's."
  []
  (let [done (into #{} (filter #(= :done (:status (entry %)))) (:order @state))]
    (swap! state (fn [s]
                   (cond-> s
                     (nil? (:active s))
                     (assoc :active (last (filter done (:order s)))))))))

(defn- refuse-while-a-job-writes!
  "Throw `:still-writing` when a job other than entry `e`'s loader claims its KB as the
  KB it writes — a chaining run or a shipped-context sync (`jobs/kb-writer`).  A loader claims no
  KB by identity (it opens its own), so the loader arm of `unload!` answers for that one."
  [e key]
  (when-let [w (jobs/kb-writer (:kb (entry key)))]
    (throw (ex-info (str (:name e) " is being written by " (:label w) " (job " (:id w)
                         ") — releasing its stores now would pull them out from under"
                         " that job.  Cancel it on the jobs page, or wait for it to"
                         " finish, then unload.")
                    {:type :still-writing :key key :holder (:id w) :label (:label w)}))))

(defn unload!
  "Take an entry down: cancel it if it is still loading, release what it held, and drop it
  from the registry.  **A memory-backed KB is cleared**; **every other backend is closed,
  not cleared** (`v/close!`), so the file lock is released and the directory is left as it
  was, and an adapter store's connection is closed too.  An entry `register!` filed with no
  `:where` releases nothing.  The `!` is for the memory case.

  Four ways it declines, each about a KB something else still holds:

  - **its loader has not stopped**: `:still-stopping`, retryable, since cancellation is
    cooperative.
  - **another job writes it**: `:still-writing`, naming the job.  A chaining run or a
    shipped-context sync claims the KB as its writer.  Asked **before** `:run-in` is
    entered, so the answer does not wait for a fixpoint, and again inside for a job
    registered meanwhile.  Refused, not cancelled, since a daemon's chain reports no
    progress.
  - **an export is walking it**: `:still-exporting`.  **That test and the release are one
    step under `start-monitor`**, the monitor `export-entry!` checks and submits under;
    otherwise an unload and an export arriving together each pass their own check and the
    walk dumps an emptied KB.  The entry is dropped inside the monitor too.
  - **the release itself failed**: the entry keeps its place with status `:unreleased` and
    the reason on it, is not active, and the throw reaches the caller.  Unloading again
    retries the release.

  `opts` takes `:run-in`, a wrapper the check-and-release step runs inside (as
  `export-entry!`'s): the browser hands its write monitor, so a write already inside
  finishes before the stores go, and a write still waiting enters after the release and is
  refused by `released?`.  `:run-in` is entered **before** `start-monitor` is taken.  The
  write monitor is process-wide, so an unload still waits for a chain running on another
  KB."
  ([key] (unload! key nil))
  ([key {:keys [run-in]}]
   (when-let [e (entry key)]
     ;; A running load owns the stores this is about to clear or close, so nothing is
     ;; released until its thread has stopped.  Cancellation lands at the next progress
     ;; report, and a phase that reports none (opening a large store scans its record log)
     ;; can outlast the wait, so the entry is reported still stopping and left whole.
     ;; `:cancelling` is still that writer (a previous unload's cancel), so it takes the same
     ;; wait.
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
     ;; a job writing this KB holds the browser's write monitor for its whole run, so this
     ;; is asked before `run-in` takes it: asked inside only, the answer waits for the job
     (refuse-while-a-job-writes! e key)
     (let [run-in (or run-in (fn [work] (work)))]
       (run-in
        (fn []
          ;; An export is a reader of exactly this KB, mid-request.  Not cancelled for the
          ;; operator: a dump takes minutes, so the unload gives way.  Checked and acted on
          ;; under `start-monitor` (`export-entry!`'s monitor), since the test and the release
          ;; touch two registries; outside it both requests pass their own check and the walk
          ;; dumps an emptied KB under a clean-looking summary.  `drop-entry!` is inside so
          ;; an export blocked here finds the entry *gone*.  The loader wait above stays
          ;; outside, since it can take thirty seconds.  `start-monitor` is taken inside
          ;; `run-in`, not around it, so an unload waiting for the write monitor holds up no
          ;; load and no export.
          (locking start-monitor
            (when (exporting-kb? (:kb (entry key)))
              (throw (ex-info (str (:name e) " is being exported — the dump walks its records"
                                   " one by one, so releasing them now would leave it a dump"
                                   " of a KB that stopped existing halfway through.  Wait for"
                                   " the export, or cancel it, then unload.")
                              {:type :still-exporting :key key})))
            ;; a job submitted after the ask above and before this monitor was taken
            (refuse-while-a-job-writes! e key)
            (let [{:keys [backend]} (:where (entry key))]
              (try
                ;; every backend but memory is closed, the adapters' `:sqlite` and
                ;; `:pg-disk-log` among them, so a backend `store-backend` answers later
                ;; is released with no edit here.  No `:where` is an entry `register!`
                ;; filed for a KB this process does not own, and nothing is released.
                (when-let [kb (case backend
                                nil     nil
                                :memory (some-> (:kb (entry key)) v/clear!)
                                (some-> (:kb (entry key)) v/close!))]
                  ;; marked inside `run-in`, so a write parked on the browser's monitor
                  ;; reads the mark when it gets the monitor (`released?`)
                  (.put ^java.util.Map released-kbs kb true))
                (catch Exception ex
                  (let [why (or (.getMessage ex) (str (class ex)))]
                    (trove/log! {:level :warn :id ::unload-problem
                                 :msg (str "releasing KB " key ": " why)})
                    ;; the entry's own status, and the load job's dropped with it: that job
                    ;; finished `:done` and `with-job` prefers it while it is there, so
                    ;; leaving it on would report the settled load over the failed release
                    (put-entry! key #(-> (dissoc % :job)
                                         (assoc :status :unreleased :finished (now)
                                                :error (str "did not release cleanly — " why))))
                    (swap! state update :active #(when (not= % key) %))
                    (fall-back-active!)
                    (throw (ex-info (str (:name e) " did not release cleanly — " why
                                         ".  It is still listed, and unloading it again"
                                         " retries the release.")
                                    {:type :unreleased :key key :backend backend} ex))))))
            (drop-entry! key)
            (fall-back-active!)))))
     true)))

(defn activate
  "Make entry `key` the one the browser reads.  Anything **holding a KB** can be activated,
  a load still running included; only an entry with no KB yet is refused.  A half-loaded KB
  answers about a *prefix*, the open-world condition, and reading beside the loader is
  sound for the single-writer reason (docs/storage.md).  A reader is owed being *told*
  (`active-caveat`), not being refused.  The entry is tested inside the `swap!` that
  activates it, so a concurrent `unload!` cannot leave `:active` naming a dropped key."
  [key]
  (let [s (swap! state (fn [s]
                         (cond-> s
                           (get-in s [:entries key :kb]) (assoc :active key))))]
    (when (and (= key (:active s)) (get-in s [:entries key :kb]))
      true)))

(defn write-blocked?
  "Is `kb` one a loader is still **writing**?  Reading beside a loader is sound; writing
  beside one is not, since two interleaved writers are not serializable and this process's
  one writer is the loader (docs/storage.md).  Asked of the **KB itself**, by identity, not
  of the active entry: loading a second KB is no reason to stop writing to the one on
  screen, and a KB the catalog never heard of is nobody's loader's business.  Two halves: a
  job handed a KB (a chaining run) says so at `submit` (`jobs/writes-kb?`), and a **load**
  opens its own, so the identity is on the entry."
  [kb]
  (boolean (and kb
                (or (jobs/writes-kb? kb)
                    (some (fn [e] (and (#{:running :cancelling} (:status (with-job e)))
                                       (identical? kb (:kb e))))
                          (vals (:entries @state)))))))

(defn active-caveat
  "What is provisional about the KB the browser is reading, or nil when nothing is.
  `{:key :name :status :progress :belief? :recoverable? :rebuilding? :rebuild}`, `:rebuild`
  being `v/rebuild-progress` while belief is rebuilt behind an installed image.  Two
  independent reasons an answer can be less than the whole truth:

  - the load is **still running** (or stopped part-way), so what is stored is a prefix;
  - **belief and the taxonomy are not built** (`recover` builds both, `:belief? false`
    skips both): every believed answer is empty and a fully stored KB renders with no
    types or contexts.

  The second outlives the first (a store opened without `:recover?` is `:done` and stays
  so), which is why it is reported beside the status.  The TMS is what is probed.  An empty
  KB is empty, not beliefless; an entry that is not an in-process KB has nothing to
  report."
  []
  (let [key (active)
        e   (entry key)
        kb  (:kb e)]
    (when (:records kb)
      ;; a store that cannot even be counted is the *most* caveated state, not the
      ;; least: folded into 0 it read as "nothing stored, nothing to miss" and the
      ;; page rendered a damaged KB as a healthy, fully settled one
      (let [n        (try (v/sentex-count kb) (catch Exception _ ::unreadable))
            ;; `in-datums`, not `datums`: the question is whether anything is *believed*,
            ;; and a recover over a strength-less store builds every node OUT, the state this
            ;; caveat points at.  The store-state probes read the store like the count does,
            ;; so a throw here makes the KB unreadable rather than failing the page header.
            st       (when-not (= ::unreadable n)
                       (try (v/store-state kb #{:believes? :recoverable?})
                            (catch Exception _ ::unreadable)))
            n        (if (= ::unreadable st) ::unreadable n)
            belief?  (if (= ::unreadable n)
                       false
                       (or (zero? (long n)) (:believes? st)))
            settled? (and (not= ::unreadable n) (= :done (:status e)))
            ;; Which repair a beliefless KB needs, which only the store knows: `recover`
            ;; reads the premise set and justifications from the record store, so a store
            ;; holding either wants a `recover`, and one holding neither has to be loaded
            ;; again.  Telling the first case to reload costs hours for nothing.
            recoverable? (and (not= ::unreadable n) (boolean (:recoverable? st)))
            ;; the third reason: belief is the image an earlier engine build wrote, and a
            ;; rebuild under this build replaces it when it finishes (`:recover? :background`)
            rebuilding?  (boolean (:stale-belief (v/write-hazards kb)))]
        (when-not (and settled? belief? (not rebuilding?))
          {:key key :name (:name e) :status (if (= ::unreadable n) :unreadable (:status e))
           :progress (:progress e) :belief? belief? :recoverable? recoverable?
           :rebuilding? rebuilding?
           ;; nil when the rebuild installed between the two reads
           :rebuild (when rebuilding? (v/rebuild-progress kb))})))))

;; ---- exporting -----------------------------------------------------------
;; A dump this process writes is a *source* it can discover, so export and reload is a round
;; trip inside the browser.  An export is a job (`vaelii.browser.jobs`): minutes on a
;; corpus, progress where the panel looks, cancelled by the progress callback throwing
;; (`export!` calls it at each chunk boundary, the only stop that leaves a directory, not a
;; half-written file).  It is not an entry, since an export produces no KB, and claims no
;; writer, so a load filling another KB may run beside it.  `exporting?` and
;; `exporting-kb?` are registry reads up with `loading?`; `unload!` asks one under
;; `start-monitor`, the monitor the check and the submit below are one step under, so the
;; loser of an unload/export race is the one that has not started.

(defn export-entry!
  "Write the KB in entry `key` out as a dump in `dir`, on its own thread, and return the
  job.  `opts` are `vaelii.core/export!`'s (`:variant`, `:compression`), plus `:run-in`, a
  wrapper the walk runs inside (the browser's write monitor, so a synchronous write already
  past the refusals drains before the walk starts).  Three refusals:

  - **another export is running**: one at a time.  A load does not refuse an export.
  - **the entry is not an in-process KB**: a daemon's export belongs to that daemon.
  - **the KB is still loading**: `export!` walks record by record with no snapshot.

  While the walk runs `exporting-kb?` answers true for this KB, and the browser's write
  entry point refuses with it, since the job claims no writer (a daemon's export is filed
  by `serve` under its own monitor).  A blank `dir` writes under `write-root`, in a
  directory `server-dir` names after the entry key.  `!` for what a cancelled one leaves:
  a directory holding part of a dump, not loadable since `meta.edn` is written last."
  [key dir opts]
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
      (let [dir    (if (str/blank? (str dir)) (server-dir (str key "-export")) dir)
            run-in (:run-in opts (fn [work] (work)))
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
     (.remove ^java.util.Map released-kbs kb)
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
  "Forget every entry, releasing each as `unload!` does, and stop every job.  For tests:
  nothing in the browser calls it, and no shutdown hook does.  Every running job is stopped
  **first** and waited for, since `unload!` refuses a KB under a live export or writer
  (`:still-exporting`, `:still-writing`).  The cancels are issued together and the waits
  overlap, each bounded by 30 s; a job that does not stop keeps its KB.  One entry refusing
  to release does not stop the rest: each refusal is logged and the sweep goes on."
  []
  ;; the running set rather than `jobs/latest` — `cancel-export!`'s docstring says why
  ;; (the newest job of a kind is routinely one that settled this morning)
  (let [ids (mapv :id (jobs/running))]
    (doseq [id ids] (jobs/cancel! id))
    (doseq [id ids] (jobs/wait id 30000)))
  (doseq [k (:order @state)]
    (try (unload! k)
         (catch Exception ex
           (trove/log! {:level :warn :id ::reset-problem
                        :msg (str "resetting the registry, KB " k ": " (.getMessage ex))}))))
  (jobs/reset-registry!)
  (reset! state {:active nil :entries {} :order [] :next-space first-space}))
