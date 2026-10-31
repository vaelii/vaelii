;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.backup
  "A backup of a `:pg-snapshot` store, taken from the browser before a large edit.

  Such a store is in two places: its directory holds the index and reasoning images and
  the operation log, and a Postgres schema holds the records (`index/records.edn` names
  the schema).  A backup is both, as of one state, in a new directory beside the store:

  | file | |
  |---|---|
  | `store/` | a copy of the store directory (`copy-flags`), its lock file left out |
  | `records.dump` | `pg_dump --format=custom` of the schema |
  | `backup.edn` | where it came from, the seal, the time, and how to restore it |

  **One state.**  The job seals the KB first, so the images name the records as they
  stand (`v/seal`), and holds the process's writer claim and the browser's write monitor
  (`:run-in`) from before the seal to after the dump, so nothing writes between the
  three.  `pg_dump` reads its schema in one snapshot transaction.

  **Restore** is by hand and takes the KB offline: unload it, rename the schema out of
  the way, `pg_restore` the dump (which recreates the schema under its own name), put
  `store/` back in the store directory's place, and load the store.  `backup.edn`
  carries the commands.  The images then open against the restored records, since
  `pg_dump` keeps the fingerprint row they were sealed against."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.string :as str]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.core :as v])
  (:import [java.io File]
           [java.nio.file FileAlreadyExistsException Files]
           [java.nio.file.attribute FileAttribute]
           [java.time LocalDateTime]
           [java.time.format DateTimeFormatter]
           [java.util.concurrent TimeUnit]))

(defn store-records
  "The Postgres location a `:pg-snapshot` store directory names, as `{:host :port :db
  :schema}`, read off its `index/records.edn`; nil when it names none."
  [dir]
  (let [f (io/file dir "index" "records.edn")]
    (when (.exists f)
      (let [[host port db schema] (:records (edn/read-string (slurp f)))]
        (when schema {:host host :port port :db db :schema schema})))))

(defn backup-dir
  "Where a backup of store directory `dir` taken at `at` goes: beside it, named after it
  and the time."
  [dir ^LocalDateTime at]
  (str (str/replace (str dir) #"/+$" "") "-backup-"
       (.format at (DateTimeFormatter/ofPattern "yyyyMMdd-HHmmss"))))

(defn pg-dump-command
  "The `pg_dump` argv writing schema `schema` of `{:host :port :db}` to `file`.  It is
  the `pg_dump` on the PATH, which must be at least the server's version, connecting as
  `pg_dump` itself decides (`PGUSER`, else the OS user), as the store's own connection
  does."
  [{:keys [host port db schema]} file]
  ["pg_dump"
   "--host" (str host) "--port" (str port) "--dbname" (str db)
   "--schema" (str schema) "--format=custom" "--compress=zstd:1" "--no-password"
   "--file" (str file)])

(def ^:private copy-flags
  "`cp`'s flags for the store copy: an APFS clone (`-cR`) on macOS, and a recursive copy
  (`-R`) elsewhere, where GNU `cp` refuses `-c`.  Both keep a link as a link."
  (if (str/starts-with? (System/getProperty "os.name") "Mac") "-cR" "-R"))

(defn- run-process!
  "Run `argv` to completion, calling `(tick)` every two seconds while it runs; throw
  with its output when it exits non-zero.  `tick` throwing (a cancel) kills the
  process and rethrows."
  [argv tick]
  (let [log  (File/createTempFile "vaelii-backup" ".log")
        proc (-> (ProcessBuilder. ^java.util.List (vec argv))
                 (.redirectErrorStream true)
                 (.redirectOutput log)
                 (.start))]
    (try
      (loop []
        (when-not (.waitFor proc 2 TimeUnit/SECONDS)
          (tick)
          (recur)))
      (when-not (zero? (.exitValue proc))
        (throw (ex-info (str (first argv) " exited " (.exitValue proc) ": "
                             (str/trim (slurp log)))
                        {:type :backup-failed :argv argv})))
      (catch Throwable t
        (.destroyForcibly proc)
        (throw t))
      (finally (.delete log)))))

(defn- delete-tree!
  "Delete `f` and, when it is a directory and not a link to one, what it holds: the clone
  keeps a link as a link, and the link is deleted without what it names."
  [^File f]
  (when (and (.isDirectory f) (not (Files/isSymbolicLink (.toPath f))))
    (run! delete-tree! (.listFiles f)))
  (.delete f))

(defn- create-dir!
  "Create the directory `out`, or `out-2`, `out-3`, … when a backup taken in the same
  second holds that name, and answer the one created.  The parent must exist."
  ^File [out]
  (loop [n 1]
    (let [f (io/file (cond-> (str out) (> n 1) (str "-" n)))]
      (if (try (Files/createDirectory (.toPath f) (make-array FileAttribute 0)) true
               (catch FileAlreadyExistsException _ false))
        f
        (recur (inc n))))))

(defn- restore-steps
  "The commands that put this backup back, as strings for `backup.edn`."
  [{:keys [host port db schema]} dir out]
  [(str "unload the store in the browser (/kbs)")
   (str "psql -h " host " -p " port " -d " db " -c 'ALTER SCHEMA " schema " RENAME TO "
        schema "_replaced'")
   (str "pg_restore -h " host " -p " port " -d " db " " out "/records.dump")
   (str "mv " dir " " dir ".replaced && cp " copy-flags " " out "/store " dir)
   (str "load the store " dir " in the browser")])

(defn refusal
  "Why entry `key` cannot be backed up, as an ex-info, or nil."
  [key]
  (let [e (catalog/entry key)]
    (cond
      (nil? e)
      (ex-info (str "no loaded KB " (pr-str key)) {:type :unknown-entry :key key})
      (not (catalog/in-process? key))
      (ex-info (str (:name e) " is served by a daemon; back it up on that host")
               {:type :not-in-process :key key})
      (not= :pg-snapshot (get-in e [:where :backend]))
      (ex-info (str (:name e) " keeps its records in "
                    (if-let [b (get-in e [:where :backend])] (str (name b) " storage") "memory")
                    ", not Postgres; this backup is for a :pg-snapshot store")
               {:type :not-pg-snapshot :key key})
      (catalog/write-blocked? (:kb e))
      (ex-info (str (:name e) " is still loading") {:type :still-loading :key key})
      (nil? (store-records (get-in e [:where :dir])))
      (ex-info (str (get-in e [:where :dir]) " names no Postgres schema in index/records.edn")
               {:type :no-records-location :key key}))))

(defn backup!
  "Back up the `:pg-snapshot` KB `kb`, whose store directory is `dir`, into a new
  directory named `out` (see the namespace doc), reporting to `progress!`, and return what
  `backup.edn` says, its `:dir` the directory written.  When `out` exists, the directory is
  `out-2`, `out-3`, … (`create-dir!`).  The caller holds off writes for the whole call.
  A backup that fails or is cancelled deletes the directory it created, and touches
  nothing else."
  [kb dir out progress!]
  (let [loc (store-records dir)]
    (progress! {:phase :seal :note "sealing, so the images name the records as they stand"})
    (let [seal (v/seal kb)
          _    (when-not (:sealed seal)
                 (throw (ex-info (str "the KB did not seal (" (:reason seal) "), so its"
                                      " images may not match its records; no backup taken")
                                 {:type :not-sealed :seal seal})))
          t0   (System/currentTimeMillis)
          out  (create-dir! out)
          dump (io/file out "records.dump")]
      (try
        (progress! {:phase :directory :note (str "cloning " dir " into " out)})
        (run-process! ["cp" copy-flags (str dir) (str (io/file out "store"))] (fn []))
        (.delete (io/file out "store" ".vaelii.lock"))
        (progress! {:phase :records :note (str "pg_dump of schema " (:schema loc))})
        (run-process! (pg-dump-command loc dump)
                      #(progress! {:phase :records :done (.length dump)
                                   :note (str "pg_dump of schema " (:schema loc) ": "
                                              (catalog/human-bytes (.length dump)) " written")}))
        (let [info {:source     {:dir (str dir) :records loc}
                    :taken-at   (str (java.time.Instant/now))
                    :seal       (select-keys seal [:generation :watermark])
                    :dump-bytes (.length dump)
                    :ms         (- (System/currentTimeMillis) t0)
                    :restore    (restore-steps loc dir out)}]
          (spit (io/file out "backup.edn") (with-out-str (pprint/pprint info)))
          (assoc info :dir (str out)))
        (catch Throwable t
          (delete-tree! out)
          (throw t))))))

(defn backup-entry!
  "Back up the `:pg-snapshot` store in entry `key` as a `:backup` job (`backup!`) and
  return the job id.  `:run-in` wraps the work, which is how the browser hands its write
  monitor.  Refuses what `refusal` names, and `{:type :job-busy}` while another job holds
  the writer."
  [key {:keys [run-in] :or {run-in (fn [work] (work))}}]
  (when-let [r (refusal key)] (throw r))
  (let [{:keys [kb name where]} (catalog/entry key)
        dir (:dir where)
        out (backup-dir dir (LocalDateTime/now))]
    (jobs/submit
     {:label      (str "Back up " name)
      :kind       :backup
      :writes     kb
      :entry      key
      :result-url "/kbs"
      :progress   {:phase :starting :done 0 :note (str "backing up " dir)}}
     (fn [progress!]
       (run-in #(assoc (backup! kb dir out progress!) :result-url "/kbs"))))))
