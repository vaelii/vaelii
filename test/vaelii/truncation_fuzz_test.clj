;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.truncation-fuzz-test
  "A durable file cut at an arbitrary byte, over **every** byte.

  The suite already pins the tears a crash is known to leave: a length prefix promising
  bytes nobody wrote (`vaelii.disk-kv-test`, `vaelii.disk-files-test`,
  `vaelii.disk-record-store-test`), a fixed lop off an index log
  (`vaelii.disk-backend-test`), half an entry stream (`vaelii.index-dump-test`), a chunk
  length no framing writes (`vaelii.export-test`).  Each is one offset somebody chose.
  This is the same question asked at every offset there is: for each file a KB writes,
  a copy truncated at k, opened and read, for every k in `[0, len)`.

  **Three outcomes are allowed and everything else is a bug.**  A store that opens and
  holds a subset of what was written; a refusal carrying a `:type`; nothing else — not a
  bare `RuntimeException`, not an untyped throw, not a hang, and above all not content
  nobody wrote.  A truncated file is a **prefix** of a good one, so what survives it can
  only be a prefix of what was written: a read that answers with something else is a
  posting resolved against the wrong bytes, which is the failure that looks like an
  answer.

  Two tests over one sweep.  `^:fuzz` walks every offset of every file for all four
  durable backends, the disk-log store a second time with tokenized bodies (so its
  `tokens.log` is swept too), and an export dump — the coverage.  The `:default` one walks a fixed,
  seeded sample of the same space, so the harness itself cannot rot unnoticed between
  runs of the exhaustive one.  Both assert on the **aggregate** rather than per offset,
  so the count is a property of the subjects and not of how many bytes a build happens
  to write.

  **`^:fuzz` runs only when named**, by `lein test-fuzz` and by `deep.yml` — no
  selector reaches it, `:all` included.  Not because it is slow the way `^:slow` is
  slow, but because it asks a question no configuration varies: `subjects` names its own
  backends and pins the one switch a subject sets, so every row of the matrix would run
  the identical sweep.  What `^:slow` means is *deferred until something eventually runs it*; what
  this means is *once, not once per configuration* — see `CONTRIBUTING.md` §5.  The one
  build that varies `vaelii.disk.tokens` pins it for itself rather than reading it, so no
  matrix row moves the sweep.

  Cost lives in `scratch-dir`, and it is worth reading before concluding the sweep is
  expensive: on a tmpfs it is a couple of minutes rather than ten."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.protocols :as p])
  (:import (java.io File RandomAccessFile)
           (java.nio.file CopyOption Files StandardCopyOption)
           (java.nio.file.attribute FileAttribute)
           (java.util Random)))

;; ---- the corpus every subject is built from ------------------------------

(defn- build!
  "A KB small enough that every byte of it can be walked, and varied enough that the
  walk crosses each stream: a taxonomy edge, a fact, a rule, and the conclusion the rule
  mints — so the sentex log, the justification log and the provenance log all hold
  something, and the index holds a rule posting as well as a fact one."
  [kb]
  (v/assert kb '(genl dog animal) 'CxUniverse)
  (v/assert kb '(dog Fido) 'CxUniverse)
  (v/assert-rule kb '[(dog ?x)] '(likes ?x Water) 'CxUniverse)
  kb)

(defn- contents
  "Every stored sentex as `[sentence context]` strings — read off the **records**, not
  through belief, since a truncated store may open with nothing recovered and still be
  perfectly readable."
  [kb]
  (into #{} (keep (fn [h]
                    (when-let [sx (p/get-sentex (:records kb) h)]
                      [(pr-str (v/sentence-of sx)) (pr-str (:context sx))])))
        (p/sentex-ids (:records kb))))

;; ---- files -------------------------------------------------------------

(def ^:private scratch-dir
  "Where a probe's directory is built — `VAELII_TEST_TMPDIR`, or the platform temp
  directory when it is unset.

  **The sweep's cost is one device cache flush per offset, and nothing else.**  A probe
  opens a store over a copied directory and closes it again; the close fsyncs, and the
  directory is deleted a moment later.  Measured on this tree: 92% of a probe is that
  open-and-close pair, an *empty* directory with nothing to truncate and nothing to
  recover costs the same 60 ms as a real probe, and the same probe against a RAM-backed
  filesystem costs 9.  So the number of bytes is not what makes this expensive and
  neither is the recovery — a `fsync` against a physical device is.

  Cheap scratch space is also, for now, the only lever.  Running the sweep wider does
  not work twice over: on macOS `F_FULLFSYNC` flushes the whole device cache, so
  concurrent flushes queue at the device rather than overlapping and four workers
  against APFS measured 0.96× one — and where scratch space *is* inexpensive enough for
  concurrency to pay (2.7× measured on a RAM disk), it makes a green run print at
  `:error`.  `sweep` says what that line is and what it would take to collect the rest.

  Point this at a tmpfs and the exhaustive sweep goes from ten minutes to under two:
  `/dev/shm` on Linux, which is what `deep.yml` uses and adds no work to arrange; on
  macOS a RAM disk is a two-line `hdiutil`/`diskutil` incantation, so a local run
  without it simply pays the ten minutes."
  (some-> (System/getenv "VAELII_TEST_TMPDIR") str/trim not-empty))

(defn- temp-root ^File []
  (let [attrs (into-array FileAttribute [])]
    (.toFile (if scratch-dir
               (Files/createTempDirectory (.toPath (File. ^String scratch-dir))
                                          "vaelii-truncfuzz-" attrs)
               (Files/createTempDirectory "vaelii-truncfuzz-" attrs)))))

(defn- rm-rf! [^File d] (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- data-files
  "Every file under `d` a truncation could damage, in a stable order.  The single-writer
  lock file is not one: it holds no content, it is recreated on open, and its bytes are
  the operating system's business."
  [^File d]
  (->> (file-seq d)
       (filter #(.isFile ^File %))
       (remove #(= ".vaelii.lock" (.getName ^File %)))
       (sort-by #(.getPath ^File %))
       vec))

(defn- copy-tree!
  "`from` copied file for file into a fresh `to`."
  [^File from ^File to]
  (.mkdirs to)
  (let [prefix (count (.getPath from))]
    (doseq [^File f (file-seq from) :when (.isFile f)]
      (let [dst (File. (str (.getPath to) (subs (.getPath f) prefix)))]
        (.mkdirs (.getParentFile dst))
        (Files/copy (.toPath f) (.toPath dst)
                    ^"[Ljava.nio.file.CopyOption;"
                    (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))))))

(defn- truncate! [^File f ^long k]
  (with-open [raf (RandomAccessFile. f "rw")] (.setLength raf k)))

;; ---- the subjects ------------------------------------------------------

(def ^:private open-ms
  "How long one open of a damaged directory is given before it counts as a hang.  A good
  open of this corpus is milliseconds; anything near this is a read that found a length
  it believed."
  20000)

(defn- with-property
  "Run `thunk` with the JVM system property `k` set to `v`, restoring the prior value
  (or clearing it) after.  `vaelii.disk.tokens` is read at each store open
  (`config/disk-tokens?`), so setting it around a build is what selects tokenized frames
  for that build alone."
  [^String k ^String v thunk]
  (let [prev (System/getProperty k)]
    (System/setProperty k v)
    (try (thunk)
         (finally (if prev (System/setProperty k prev) (System/clearProperty k))))))

(defn- store-subject
  "A durable KB on `backend`: built, closed, and reopened with recovery — which is the
  read a restart makes, and the one that walks every file."
  [backend space]
  {:label (name backend)
   :build (fn [dir]
            (.mkdirs (File. ^String dir))
            (let [kb (v/open-kb {:backend backend :dir dir :space space :recover? false})]
              (try (build! kb) (contents kb) (finally (v/close! kb)))))
   :open  (fn [dir]
            (let [kb (v/open-kb {:backend backend :dir dir :space space :recover? :auto})]
              (try (contents kb)
                   (finally
                     ;; a RAM-side index is registered per **space** for the life of the
                     ;; JVM, and every probe of a subject opens on one space over a fresh
                     ;; copy of the directory — so the index goes out empty, or the next
                     ;; probe reads this one's postings and the sweep answers about a
                     ;; directory nobody wrote
                     (p/clear-index! (:index kb))
                     (v/close! kb)))))})

(defn- tokenized-store-subject
  "The `:disk-log` store built with tokenized sentex bodies (`vaelii.disk.tokens` on for
  the build), so its durable `tokens.log` and its tokenized `sentexes.log` frames join
  the sweep — the shapes the four plain subjects never write, since tokenization is off
  by default.  Only the build sets the switch: a reopen reads a tokenized frame off its
  own tag with the dictionary opened whenever `tokens.log` is present, so a truncated
  `tokens.log` retires the ids past its torn tail and `open-record-store` tombstones the
  records that cite them, exactly as it would after a crash."
  [space]
  (let [s (store-subject :disk-log space)]
    (assoc s
           :label "disk-log-tok"
           :build (fn [dir] (with-property "vaelii.disk.tokens" "true" #((:build s) dir))))))

(defn- dump-subject
  "An export dump, read back with `import!` — the other durable shape, and the one that
  arrives from another machine."
  [space]
  {:label "dump"
   :build (fn [dir]
            (let [src (str dir "-src")]
              (.mkdirs (File. ^String src))
              (let [kb (v/open-kb {:backend :disk-log :dir src :space space
                                   :recover? false})]
                (try (build! kb)
                     (v/export! kb dir {:compression :none})
                     (contents kb)
                     (finally (v/close! kb)
                              (rm-rf! (File. ^String src)))))))
   :open  (fn [dir]
            (let [kb (v/open-kb {:backend :memory :space [::fuzz :dump-into]
                                 :recover? false})]
              ;; one space, emptied per probe rather than a fresh number each time: a
              ;; space is a JVM-lifetime registry entry, and `import!` refuses a
              ;; destination that is not empty, so clearing is both halves of the job
              (p/clear-records! (:records kb))
              (p/clear-index! (:index kb))
              (v/import! kb dir)
              (contents kb)))})

(defn- subjects
  "One per durable shape, with the disk-log store appearing a second time built with
  tokenized bodies.  Each takes a space of its own — a RAM-side index is shared
  per space number for the life of the JVM, so two subjects on one number would read
  each other's postings."
  []
  [(store-subject :disk-memory        [::fuzz :disk-memory])
   (store-subject :disk-dense         [::fuzz :disk-dense])
   (store-subject :disk-columnar      [::fuzz :disk-columnar])
   (store-subject :disk-log           [::fuzz :disk-log])
   (tokenized-store-subject           [::fuzz :disk-log-tok])
   (dump-subject                      [::fuzz :dump])])

;; ---- one offset --------------------------------------------------------

(defn- outcome
  "What opening `dir` did, as one of: `{:read <set>}`, `{:refused <type>}`,
  `{:untyped …}`, `{:threw …}`, `{:hang true}`.

  On a future, so a read that believed a length prefix is a bounded failure rather than
  a suite that never finishes.  `Throwable`, not `Exception`: a length read out of torn
  bytes is exactly how an `OutOfMemoryError` arrives, and it is an outcome like any
  other."
  [open! dir]
  (let [f (future (try {:read (open! dir)}
                       (catch clojure.lang.ExceptionInfo e
                         (if-let [ty (:type (ex-data e))]
                           {:refused ty}
                           {:untyped (str "ExceptionInfo: " (ex-message e))}))
                       (catch Throwable t
                         {:threw (str (.getName (class t)) ": " (.getMessage t))})))
        r (deref f open-ms ::timeout)]
    (if (= ::timeout r) {:hang true} r)))

(defn- probe
  "`base` copied, its `rel` file truncated at `k`, opened, and the copy cleaned up."
  [{:keys [open]} written ^File base rel k]
  (let [work (File. (str (.getPath base) "-work"))]
    (try
      (rm-rf! work)
      (copy-tree! base work)
      (truncate! (File. (str (.getPath work) rel)) k)
      (let [r (outcome open (.getPath work))]
        (if-let [read (:read r)]
          (let [extra (set/difference read written)]
            (if (seq extra) {:invented (vec extra)} {:ok (count read)}))
          r))
      (finally
        (backend/close-dir! (.getPath work))
        (rm-rf! work)))))

;; ---- the sweep ---------------------------------------------------------

(defn- cuts
  "Every `[rel k]` a truncation of this directory can be — one per byte of every file —
  or, when `sample` is a number, that many of them drawn from a **seeded** `Random`.

  Drawn across the subject's whole byte space rather than per file, so a handful of
  probes still lands in more than one stream: a per-file draw at this size would spend
  most of them on the four-byte sentinels and none on the log."
  [^File base sample]
  (let [prefix (count (.getPath base))
        all    (into [] (mapcat (fn [^File f]
                                  (let [rel (subs (.getPath f) prefix)]
                                    (map (fn [k] [rel k]) (range (.length f))))))
                     (data-files base))]
    (if (nil? sample)
      all
      (let [rnd (Random. 20260825)
            n   (count all)]
        (mapv #(nth all %) (repeatedly (min (long sample) n) #(.nextInt rnd (int n))))))))

(defn- sweep
  "Truncate `subject`'s directory at each cut and collect what happened:
  `{:offsets n :bad [[rel k outcome] …] :recovered n :refused n}`.

  **Serial on purpose**, and not because sharding would be hard: probes are independent,
  each subject already has its own space, and four workers over one subject measured
  2.7× on a RAM disk.  It is that a sharded sweep makes a green run print at `:error`.

  What it provokes is **benign and already handled**.  A close landing under a queued
  auto-compaction is a window `vaelii.impl.disk.durability` documents and closes: its
  registry check is the early skip, and the record store's compaction throws on its
  closed idx before a temp or a marker is written.  So the `auto-compact of
  disk-records … failed: Stream Closed` that four workers produce — and one worker over
  the same offsets does not — is the designed guard firing, nothing written and nothing
  lost.  The defect is only that `durability.clj`'s catch-all reports it at `:error`
  alongside real failures.

  Which is why this is a wait rather than a refusal: reclassify that one outcome and
  sharding is available, for the last 30% after `scratch-dir` has taken the rest.  Until
  then a sweep is not worth teaching to make a clean run look dirty."
  [subject sample]
  (let [root (temp-root)
        base (File. (str (.getPath root) "/base"))]
    (try
      (let [written ((:build subject) (.getPath base))]
        (reduce
         (fn [acc [rel k]]
           (let [r (probe subject written base rel k)]
             (cond-> (update acc :offsets inc)
               (:ok r)       (update :recovered inc)
               (:refused r)  (update :refused inc)
               (or (:threw r) (:hang r) (:invented r) (:untyped r))
               (update :bad conj [rel k r]))))
         {:offsets 0 :bad [] :recovered 0 :refused 0}
         (cuts base sample)))
      (finally (rm-rf! root)))))

(defn- check!
  "The claims, one `is` each, over the aggregate — so the count is the number of
  subjects and never the number of bytes a build happened to write."
  [label {:keys [offsets bad recovered refused]}]
  (let [by-kind (fn [k] (filterv #(k (nth % 2)) bad))]
    (is (empty? (by-kind :threw))
        (str label ": an offset failed with an untyped exception — "
             (pr-str (take 5 (by-kind :threw)))))
    (is (empty? (by-kind :untyped))
        (str label ": an offset threw an ex-info carrying no :type — "
             (pr-str (take 5 (by-kind :untyped)))))
    (is (empty? (by-kind :hang))
        (str label ": an offset did not finish inside " open-ms " ms — "
             (pr-str (take 5 (by-kind :hang)))))
    (is (empty? (by-kind :invented))
        (str label ": an offset read back content nobody wrote — "
             (pr-str (take 5 (by-kind :invented)))))
    (is (and (pos? offsets) (pos? (+ recovered refused)))
        (str label ": the sweep walked " offsets " offsets, of which " recovered
             " opened and " refused " were refused — one of those has to be non-zero or
             the harness measured nothing"))))

(def ^:private sample-cuts
  "How many cuts the `:default` sweep draws per subject.  A probe is a directory copied,
  a store opened under recovery and closed again, so this is a wall-clock decision as
  much as a coverage one — the exhaustive sweep below is where coverage comes from, and
  this is the check that it still runs at all.  The seeded draw makes the number of
  probes fixed rather than a property of the box."
  2)

(deftest a-sampled-truncation-of-a-durable-file-is-refused-or-recovered
  (doseq [s (subjects)]
    (testing (:label s)
      (check! (:label s) (sweep s sample-cuts)))))

(deftest every-fuzz-marked-sweep-keeps-a-sampled-twin
  ;; The rule that makes `^:fuzz` safe to hand out, checked rather than written down.
  ;; No selector reaches the mark, so a namespace whose tests all carry it runs in one
  ;; weekly job and nowhere else — and a harness that quietly stopped working reads
  ;; exactly like one that passes.  The twin is the answer: the exhaustive half proves
  ;; the property, the sampled half proves the harness still runs, and only the sampled
  ;; half runs on an ordinary commit.  Written as a scan rather than a roster so it
  ;; covers the sweep somebody adds next, which is the one nobody will remember.
  (doseq [^File f (->> (file-seq (File. "test"))
                       (filter #(.isFile ^File %))
                       (filter #(str/ends-with? (.getName ^File %) "_test.clj"))
                       (sort-by #(.getPath ^File %)))
          :let [src (slurp f)]
          :when (re-find #"\((?:deftest|tu/deftest-kb|defspec)\s+\^:fuzz" src)]
    (is (re-find #"\((?:deftest|tu/deftest-kb|defspec)\s+[a-z]" src)
        (str (.getPath f) " carries a ^:fuzz test and no unmarked one — nothing in it"
             " runs outside `lein test-fuzz`, so a harness that broke would keep"
             " passing until somebody named the mark"))))

(deftest ^:fuzz every-truncation-of-every-durable-file-is-refused-or-recovered
  ;; The whole space: every byte of every file, for every durable shape — 9,717 offsets
  ;; over this corpus.  A probe is a directory copied and a store opened under recovery,
  ;; so the cost tracks the number of *opens* and not the number of bytes — and, since
  ;; an open costs a device cache flush and almost nothing else, `scratch-dir` is what
  ;; decides whether that is ten minutes or under two.  The sampled sweep above is what
  ;; keeps this harness honest between the runs that name it.
  (doseq [s (subjects)]
    (testing (:label s)
      (check! (:label s) (sweep s nil)))))
