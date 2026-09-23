;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.oplog-crash-fuzz-test
  "A logged `:disk-snapshot` directory (`vaelii.impl.seal`) cut the way a power loss cuts
  it, at every byte a crash can take.

  A power loss keeps what an fsync covered and any prefix of what it did not.  A seal
  fsyncs the record store before it writes `seal.nippy`, and the log fsyncs an
  operation's frame before the operation writes a record older than the log.  So each
  file of the directory holds a **floor**: its length when the seal returned, and for
  the log the length after the last operation that wrote such a record.  The sweep
  copies the directory as the workload left it, cuts one file at an offset between its
  floor and its length, and restores the copy — for every such offset of every file.
  A file written whole through a temp file and a rename (`.nippy`) is never cut, so it
  is not swept.

  **Two outcomes are allowed.**  A restore that restores holds exactly the records and
  the belief of a directory that took the same setup and the first `n` operations and
  never crashed, where `n` is the number of frames the restore replayed.  A restore that
  declines leaves a directory whose next open believes what a rebuild from its records
  believes: the images it keeps are ones the open refuses, or ones that describe the
  records.  An open of the cut directory may refuse with a `:type`, which counts as a
  decline.  A throw from `restore!` once the open succeeded, a throw carrying no `:type`,
  a hang, and a restored KB that differs from its reference are failures.

  **The source identity is held for the sweep.**  A seal stamps its images with the
  identity of the source it was taken under, and a restore refuses an image whose identity
  has moved — so an edit under `src/` while the sweep runs would decline every cut, on a
  reason that says nothing about a crash, and the sweep would measure nothing.  Pinned
  around the build and the probes, the cut is what varies.  What an *uncut* copy does is
  taken first and reported as the sweep's premise: it restores, or no cut could.

  The `^:fuzz` test walks every offset; the unmarked one walks a seeded sample, so the
  harness runs on every commit (`vaelii.truncation-fuzz-test` states the rule)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.seal :as seal]
            [vaelii.impl.source-identity :as si])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files StandardCopyOption]
           [java.nio.file.attribute FileAttribute]
           [java.util Random]))

;; ---- directories -----------------------------------------------------------

(def ^:private scratch-dir
  "`VAELII_TEST_TMPDIR`, or the platform temp directory when it is unset.  A probe's
  cost is the fsyncs of an open, a restore and a close, so a tmpfs shortens the sweep."
  (some-> (System/getenv "VAELII_TEST_TMPDIR") str/trim not-empty))

(defn- tmpdir ^String []
  (let [attrs (into-array FileAttribute [])]
    (str (if scratch-dir
           (Files/createTempDirectory (.toPath (File. ^String scratch-dir)) "vaelii-opfuzz-" attrs)
           (Files/createTempDirectory "vaelii-opfuzz-" attrs)))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- copy-dir!
  "Copy `from` into `to` as the files stand, the single-writer lock file left out."
  [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :when (not= ".vaelii.lock" (.getName f))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        (Files/copy (.toPath f) (.toPath t)
                    ^"[Ljava.nio.file.CopyOption;"
                    (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))))))

(defn- lengths
  "Relative path -> length, for every file under `dir` a crash can cut."
  [^String dir]
  (let [base (.toPath (io/file dir))]
    (into (sorted-map)
          (for [^File f (file-seq (io/file dir))
                :when (and (.isFile f)
                           (not= ".vaelii.lock" (.getName f))
                           (not (str/ends-with? (.getName f) ".nippy")))]
            [(str (.relativize base (.toPath f))) (.length f)]))))

(defn- truncate! [^String dir ^String rel ^long k]
  (with-open [raf (RandomAccessFile. (io/file dir rel) "rw")] (.setLength raf k)))

(defn- open
  ([dir] (open dir {:recover? false}))
  ([dir opts] (v/open-kb (merge {:backend :disk-snapshot :dir dir} opts))))

;; ---- the workload ------------------------------------------------------------

(defn- setup!
  "What the directory holds when the log's first seal is taken: a forward rule and three
  facts it fires on."
  [kb]
  (v/assert kb '(set/forwardRule (implies (and (animal ?x)) (mortal ?x))) 'CxUniverse)
  (doseq [x '[Socrates Plato Aristotle]]
    (v/assert kb (list 'animal x) 'CxUniverse)))

(def ^:private ops
  "The operations after the seal.  The second retracts a fact the seal holds, so the log
  fsyncs its frame before the retraction writes; the fourth retracts a fact this
  generation stored, which needs no fsync."
  [#(v/assert % '(animal Zeno) 'CxUniverse)
   #(v/retract! % (v/handle-of % '(animal Socrates) 'CxUniverse))
   #(v/assert % '(animal Diogenes) 'CxUniverse)
   #(v/retract! % (v/handle-of % '(animal Zeno) 'CxUniverse))
   #(v/assert % '(animal Thales) 'CxUniverse {:strength :monotonic})])

(defn- view
  "Every sentex `kb`'s records hold, as `[sentence context believed?]`."
  [kb]
  (into #{} (keep (fn [h]
                    (when-let [sx (p/get-sentex (:records kb) h)]
                      [(pr-str (:sentence sx)) (pr-str (:context sx)) (boolean (v/in? kb h))])))
        (p/sentex-ids (:records kb))))

(defn- reference
  "The view of a directory that took `setup!` and the first `n` of `ops`, and closed."
  [n]
  (let [dir (tmpdir)]
    (try
      (let [kb (open dir)]
        (try (setup! kb)
             (doseq [op (take n ops)] (op kb))
             (view kb)
             (finally (v/close! kb))))
      (finally (rm-rf! dir)))))

(def ^:private log-rel (str "oplog" File/separator "ops.log"))

(defn- build!
  "Seal a logged KB over `dir`, run `ops` through it, and copy `dir` into `crash` while
  the KB is still open.  Returns `{:floor rel->len :final rel->len}`."
  [^String dir ^String crash]
  (let [kb  (open dir)
        _   (setup! kb)
        lkb (seal/attach! kb)
        log (:oplog lkb)]
    (try
      (let [floor (reduce (fn [floor op]
                            (let [before (:guard-checks @(:state log))]
                              (op lkb)
                              (if (> (long (:guard-checks @(:state log))) (long before))
                                (assoc floor log-rel (.length (io/file dir log-rel)))
                                floor)))
                          (lengths dir)
                          ops)]
        (copy-dir! dir crash)
        {:floor floor :final (lengths crash)})
      (finally (v/close! lkb)))))

;; ---- one probe ---------------------------------------------------------------

(def ^:private open-ms
  "How long one probe is given before it counts as a hang."
  60000)

(defn- rebuilt-view
  "The view of `dir` opened with no images: a copy with `index/` and `reasoning/` removed,
  so the open rebuilds both from the records."
  [^String dir]
  (let [copy (tmpdir)]
    (try
      (copy-dir! dir copy)
      (rm-rf! (str copy "/index"))
      (rm-rf! (str copy "/reasoning"))
      (let [kb (open copy {:recover? :auto})]
        (try (view kb) (finally (v/close! kb))))
      (finally (backend/close-dir! copy) (rm-rf! copy)))))

(defn- restore-outcome
  "What restoring `dir` did: `{:restored n}`, `{:declined reason}`, `{:wrong …}`,
  `{:restore-threw …}`, `{:refused type}`, `{:untyped …}`, `{:threw …}` or
  `{:hang true}`.  `:refused` is a typed throw from the open, before `restore!` runs."
  [^String dir reference]
  (let [f (future
            (try
              (let [kb (open dir)
                    r  (try (seal/restore! kb)
                            (catch Throwable t
                              {::threw (str (.getName (class t)) ": " (ex-message t) " "
                                            (pr-str (ex-data t)))}))]
                (cond
                  (::threw r)
                  (do (v/close! kb) {:restore-threw (::threw r)})

                  (:restored r)
                  (let [n    (:frames r)
                        got  (try (view (:kb r)) (finally (v/close! (:kb r))))
                        want (reference n)]
                    (if (= want got) {:restored n} {:wrong n :missing (remove got want)
                                                    :extra (remove want got)}))

                  :else
                  (do (v/close! kb)
                      (let [got (let [kb2 (open dir {:recover? :auto})]
                                  (try (view kb2) (finally (v/close! kb2))))
                            want (rebuilt-view dir)]
                        (if (= want got)
                          {:declined (:reason r)}
                          {:wrong [:after-decline (:reason r)] :missing (remove got want)
                           :extra (remove want got)})))))
              (catch clojure.lang.ExceptionInfo e
                (if-let [ty (:type (ex-data e))]
                  {:refused ty}
                  {:untyped (str "ExceptionInfo: " (ex-message e))}))
              (catch Throwable t
                {:threw (str (.getName (class t)) ": " (.getMessage t))})))
        r (deref f open-ms ::timeout)]
    (if (= ::timeout r) {:hang true} r)))

(defn- probe
  "Restore a copy of `crash`, cut at offset `k` of `rel` — or uncut, when no file is named."
  ([^String crash reference] (probe crash nil nil reference))
  ([^String crash rel k reference]
   (let [work (tmpdir)]
     (try
       (copy-dir! crash work)
       (when rel (truncate! work rel k))
       (restore-outcome work reference)
       (finally (backend/close-dir! work) (rm-rf! work))))))

;; ---- the sweep ---------------------------------------------------------------

(defn- cuts
  "Every `[rel k]` with k between `rel`'s floor and its length, or `sample` of them drawn
  from a seeded `Random`."
  [{:keys [floor final]} sample]
  (let [all (into [] (mapcat (fn [[rel len]]
                               (map (fn [k] [rel k]) (range (get floor rel 0) len))))
                  final)]
    (if (nil? sample)
      all
      (let [rnd (Random. 20260913)
            n   (count all)]
        (mapv #(nth all %) (repeatedly (min (long sample) n) #(.nextInt rnd (int n))))))))

(defn- call-with-source-identity-held
  "Run `thunk` with `si/source-identity` pinned to the value it answers now — the
  namespace docstring, \"The source identity is held for the sweep\"."
  [thunk]
  (let [held (si/source-identity)]
    (with-redefs [si/source-identity (fn ([] held) ([_] held))] (thunk))))

(defn- decline-reason [r]
  (if (contains? r :declined) (:declined r) [:refused (:refused r)]))

(defn- sweep
  "`{:offsets n :restored n :declined n :reasons {reason n} :premise outcome
  :bad [[rel k outcome] …]}` over `sample` cuts, or every cut when `sample` is nil.
  `:premise` is what an uncut copy of the directory did."
  [sample]
  (call-with-source-identity-held
   (fn []
     (let [dir (tmpdir) crash (tmpdir)
           reference (memoize reference)]
       (try
         (let [shape   (build! dir crash)
               premise (probe crash reference)]
           (reduce (fn [acc [rel k]]
                     (let [r (probe crash rel k reference)]
                       (cond-> (update acc :offsets inc)
                         (:restored r) (update :restored inc)
                         (or (contains? r :declined) (:refused r))
                         (-> (update :declined inc)
                             (update-in [:reasons (decline-reason r)] (fnil inc 0)))
                         (some r [:wrong :restore-threw :untyped :threw :hang])
                         (update :bad conj [rel k r]))))
                   {:offsets 0 :restored 0 :declined 0 :reasons {} :premise premise :bad []}
                   (cuts shape sample)))
         (finally (backend/close-dir! dir) (rm-rf! dir) (rm-rf! crash)))))))

(defn- check! [{:keys [offsets restored declined bad premise]}]
  (is (:restored premise)
      (str "an uncut copy of the crash directory did not restore, so no cut could: "
           (pr-str premise)))
  (is (empty? bad) (str "cuts that restored wrong, threw untyped or hung: "
                        (pr-str (take 5 bad))))
  (is (pos? offsets) "the sweep walked no offset")
  (is (= offsets (+ restored declined (count bad)))
      "every cut restored, declined, or is listed as bad"))

(def ^:private sample-cuts
  "How many cuts the unmarked sweep draws."
  3)

(deftest a-sampled-crash-cut-of-a-logged-directory-restores-or-declines
  (check! (sweep sample-cuts)))

(deftest ^:fuzz every-crash-cut-of-a-logged-directory-restores-or-declines
  (let [r (sweep nil)]
    (check! r)
    (is (pos? (:restored r))
        (str "a cut of a record file restores by replaying its writes; every cut declined: "
             (pr-str (:reasons r))))))
