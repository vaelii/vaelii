;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.index-snapshot-test
  "The mapped index snapshot (`vaelii.impl.disk.index-snapshot`) against real records.

  `columnar_index_oracle_test` owns the question *does a mapped index answer what the
  store it was written from answered* — it round-trips the whole differential oracle
  through a snapshot.  This file owns the other one: **is this image still about this
  KB**, and what happens when it is not.  Every mismatch class gets its own test, because
  a validity rule with one test is a validity rule with one case.

  The rule under test is that a snapshot is a *cache of derived state*: any doubt at all
  discards it and reindexes, and a reindex is always correct.  So each test asserts two
  things — that the fallback was taken, and that the KB answers correctly afterwards.  One
  that checked only the first would pass on a build that rebuilt every time, and one that
  checked only the second would pass on a build that never wrote an image at all.

  The path is asserted on, never wall-clock: `opening` counts the `reindex` calls, because
  a fast rebuild is still a rebuild."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.index-snapshot :as snap]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.snapshot :as snapshot-types])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files Paths StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-snapshot-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (File. dir)))] (.delete ^File f)))

(defn- copy-tree!
  "Copy every regular file of `from` into a fresh `to` — how a test takes an image aside
  and puts it back, which is the only defensible way to produce a *stale* one."
  [^String from ^String to]
  (rm-rf! to)
  (.mkdirs (File. to))
  ;; hoisted and hinted: the options array is the same on every file, and unhinted it
  ;; reads as Object at the call, which is a reflective `Files/copy` per file
  (let [^"[Ljava.nio.file.CopyOption;" opts
        (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING])]
    (doseq [^File src (.listFiles (File. from)) :when (.isFile src)]
      (Files/copy (.toPath src)
                  (Paths/get (str to "/" (.getName src)) (into-array String []))
                  opts))))

(defn- with-snapshot-dir
  "Run `(f dir)` in a fresh temporary directory, closing its stores and deleting it
  afterwards.

  The mode is not set here: `{:index :snapshot}` rides each caller's own opts map, because
  the image is an index *representation* and the KB records that it was asked for
  (`kb/backend-axes`).  So this hands out a directory and takes it away again, and a test
  that wants the pairing that names no image opens `{:index :columnar}` over the same
  helper."
  [f]
  (let [dir (tmpdir)]
    (try (f dir)
         (finally
           (backend/close-dir! dir)
           (rm-rf! dir)))))

(defn- with-properties
  "Run `f` with each system property set, restoring every one afterwards."
  [m f]
  (let [prev (into {} (map (fn [[k _]] [k (System/getProperty k)])) m)]
    (doseq [[k v] m] (System/setProperty k v))
    (try (f)
         (finally
           (doseq [[k v] prev]
             (if v (System/setProperty k v) (System/clearProperty k)))))))

;; ---- the content, and what it must answer -------------------------------

(defn- build!
  "A KB with something of every indexed shape in it: plain binary facts, a unary type, a
  **number** argument (a trie token that is not a handle), and a rule (which lands in the
  rule index rather than the roots)."
  [kb]
  (v/clear! kb)
  (doseq [i (range 60)]
    (v/assert kb (list 'parentOf (symbol (str "Snap" i)) (symbol (str "Snap" (inc i))))
              'CxUniverse {:strength :monotonic}))
  (v/assert kb '(dog SnapMuffet) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(likes SnapMuffet SnapBall) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(bornIn SnapMuffet 1970) 'CxUniverse {:strength :monotonic})
  (v/assert-rule kb '[(parentOf ?x ?y)] '(ancestorOf ?x ?y) 'CxUniverse)
  kb)

(defn- answers
  "Everything the index is asked for, through the public surface plus the index reads no
  query would notice going wrong: `term-count`, the root count, and **both** argument
  paths.

  The two argument reads are here because they descend differently and an image can carry
  one without the other.  A named functor takes the predicate-scoped key, which the
  packed long carries through its scope id; a variable functor takes the agnostic read,
  which descends the slot roster in the fallback blob and then reads the scoped postings
  it names.  `SnapMuffet` occupies position 1 under three predicates, so the agnostic read
  is a genuine union rather than a single set handed back."
  [kb]
  {:parents  (count (v/sentexes-matching kb '(parentOf ?x ?y) 'CxUniverse))
   :dog      (v/ask? kb '(dog SnapMuffet) 'CxUniverse)
   :ball     (count (v/sentexes-matching kb '(likes ?x SnapBall) 'CxUniverse))
   :number   (count (v/sentexes-matching kb '(bornIn ?x 1970) 'CxUniverse))
   :ancestor (v/ask? kb '(ancestorOf Snap0 Snap1) 'CxUniverse)
   :scoped   (p/sentexes-with-args (:index kb) 'likes {2 'SnapBall})
   :agnostic (p/sentexes-with-arg  (:index kb) 1 'SnapMuffet)
   :agn-n    (p/count-with-arg     (:index kb) 1 'SnapMuffet)
   :terms    (p/term-count (:index kb))
   :nodes    (p/count-at (:index kb) [])})

(defn- opening
  "Open a KB over `dir` in recovery mode, counting the reindexes that ran.  Returns
  `[kb reindexes]`."
  [dir]
  (let [n    (atom 0)
        real reindex/reindex]
    (with-redefs [reindex/reindex (fn [kb] (swap! n inc) (real kb))]
      (let [kb (v/open-kb {:records :disk :index :snapshot :dir dir :recover? :auto})]
        [kb @n]))))

(defn- opening-columnar
  "`opening` for the pairing that names no image — the same count, over `:index
  :columnar`, which rebuilds on every open by definition."
  [dir]
  (let [n    (atom 0)
        real reindex/reindex]
    (with-redefs [reindex/reindex (fn [kb] (swap! n inc) (real kb))]
      (let [kb (v/open-kb {:records :disk :index :columnar :dir dir :recover? :auto})]
        [kb @n]))))

(defn- meta-path  ^String [dir] (str (snap/snapshot-root dir) "/snapshot.meta"))
(defn- meta-file  ^File   [dir] (File. (meta-path dir)))

(defn- scratch-index
  "A columnar index store on its own space — somewhere to load an image into when the
  question is what `load!` *decides*, not what a KB then answers."
  [tag]
  (doto (columnar/columnar-index-store {:space [::scratch tag]}) (p/clear-index!)))

;; ---- which records an image can be about --------------------------------

(deftest the-image-pairs-with-disk-records-alone
  ;; An image is stamped with `record-store/slot-fingerprint` — the disk record store's own
  ;; sequential read of its slot file, which lives on that namespace rather than on the
  ;; `RecordStore` protocol.  No other record axis can compute one, so an image over one
  ;; could be neither stamped when it was written nor checked when it was read, and validity
  ;; is this representation's whole design.  Durability is not the test, which is what makes
  ;; this a second gate rather than a stricter reading of the first: `:pg` records are
  ;; durable and are refused all the same.
  (testing ":pg records, durable and still unable to answer the stamp"
    (let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo
                                  #"the :snapshot index pairs with :disk records"
                                  (kb/backend-axes {:records :pg :index :snapshot})))]
      (is (= :unknown-backend (:type (ex-data e))))
      (is (= :pg-disk-log (:instead (ex-data e))) "naming the pairing to take instead")
      (is (re-find #"fingerprint" (ex-message e)) "and saying which of the two gates it is")))
  (testing "and no backend name spells that pair"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown KB backend"
                          (kb/backend-axes {:backend :pg-snapshot}))))
  (testing "while RAM records get the durability argument, which is the other one"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"the :snapshot index needs durable records — :disk —"
                          (kb/backend-axes {:records :memory :index :snapshot}))))
  (testing "and the one pairing that opens"
    (is (= {:records :disk :index :snapshot} (kb/backend-axes {:backend :disk-snapshot})))
    (is (= {:records :disk :index :snapshot} (kb/backend-axes {:records :disk :index :snapshot})))))

;; ---- the round trip ------------------------------------------------------

(deftest snapshot-round-trip-skips-the-rebuild
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
            want (answers kb)]
        (backend/close-dir! dir)
        (is (.exists (meta-file dir)) "closing the directory wrote the image")
        (let [[kb2 rebuilds] (opening dir)]
          (is (zero? rebuilds) "no reindex ran")
          (is (= want (answers kb2))))))))

(deftest a-write-after-a-mapped-open-thaws-and-answers
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 rebuilds] (opening dir)]
        (is (zero? rebuilds))
        (v/assert kb2 '(cat SnapTom) 'CxUniverse {:strength :monotonic})
        (v/assert kb2 '(likes SnapTom SnapBall) 'CxUniverse {:strength :monotonic})
        (is (v/ask? kb2 '(cat SnapTom) 'CxUniverse) "the trie thawed out of its mapping")
        (is (= 2 (count (v/sentexes-matching kb2 '(likes ?x SnapBall) 'CxUniverse)))
            "the thawed roots hold the mapped posting and the new member alike")
        (let [want (answers kb2)]
          (backend/close-dir! dir)
          (testing "and the next image round-trips the thawed state"
            (let [[kb3 rebuilds] (opening dir)]
              (is (zero? rebuilds))
              (is (= want (answers kb3))))))))))

(deftest a-mapped-index-that-was-never-written-is-not-rewritten
  (testing "closing a read-only session must not pull the cold tail back into heap"
    (with-snapshot-dir
      (fn [dir]
        (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
        (backend/close-dir! dir)
        (let [[kb2 _] (opening dir)
              stamp   #(drs/slot-fingerprint (:records kb2))]
          (is (= {:index :skipped :reason :unchanged}
                 (select-keys (snap/save! dir (:index kb2) stamp) [:index :reason]))
              "the image already *is* this index — writing it would thaw the roots to read them")
          ;; and a write puts it back in play
          (v/assert kb2 '(cat SnapTom) 'CxUniverse {:strength :monotonic})
          (is (= :saved (:index (snap/save! dir (:index kb2) stamp)))))))))

(deftest a-save-that-fails-part-way-takes-its-temp-sections-with-it
  ;; Each section is written beside its target and swapped in only at the commit point,
  ;; so a throw part-way costs the new image and never the one on disk.  What it must not
  ;; also cost is the directory: a `.tmp` section is the size of the index, nothing else
  ;; ever deletes one, and a KB nobody reopens carries it for good.
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 _] (opening dir)
            stamp   #(drs/slot-fingerprint (:records kb2))
            ^String root (snap/snapshot-root dir)
            temps   (fn [] (->> (.listFiles (File. root))
                                (filter #(.endsWith (.getName ^File %) ".tmp"))
                                (mapv #(.getName ^File %))
                                sort
                                vec))]
        ;; a write, so the image is no longer the index being read and `save!` is not
        ;; skipped as `:unchanged`
        (v/assert kb2 '(cat SnapTom) 'CxUniverse {:strength :monotonic})
        (is (= [] (temps)) "nothing is left over before the failed save")
        (is (thrown? java.io.IOException
                     (with-redefs-fn
                       {#'snap/write-roots! (fn [& _] (throw (java.io.IOException. "the disk filled")))}
                       (fn [] (snap/save! dir (:index kb2) stamp))))
            "the failure travels rather than being reported as a written image")
        (is (= [] (temps))
            (str "a failed save left its sections behind: " (pr-str (temps))))
        (testing "and the image already on disk is the one that is still there"
          (let [want (answers kb2)]
            (backend/close-dir! dir)
            (let [[kb3 rebuilds] (opening dir)]
              (is (zero? rebuilds) "the previous image still reads, so nothing rebuilt")
              (is (= want (answers kb3))))))))))

(deftest a-half-thawed-index-writes-its-sections-out-of-the-mapping
  ;; `index-rule` writes the rule index and touches no trie path (the rule *sentex* does
  ;; that separately — this is the half `reindex/index-rule-entry` posts on its own).  So
  ;; it thaws the roots and leaves the trie mapped, and the next image is written with its
  ;; leaf sections read **straight out of the live mapping** — the one write path with no
  ;; heap array to copy from, and one the `:unchanged` skip above keeps an ordinary close
  ;; from reaching.
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 _] (opening dir)
            idx     (:index kb2)]
        (is (snapshot-types/snapshot-mapped? (:trie idx)) "the trie opened mapped")
        (p/index-rule idx 987654 '[snapAnte] 'snapConsq)
        (is (snapshot-types/snapshot-mapped? (:trie idx)) "and the rule index left it so — only the roots thawed")
        (is (= :saved (:index (snap/save! dir idx #(drs/slot-fingerprint (:records kb2))))))
        (let [want (answers kb2)]
          (backend/close-dir! dir)
          (let [[kb3 rebuilds] (opening dir)]
            (is (zero? rebuilds))
            (is (= want (answers kb3)) "the mapped-through sections read back unchanged")
            ;; the rule entry is not derivable from the records (no such sentex), so its
            ;; survival is proof the image carried it rather than a rebuild recreating it
            (is (= #{987654} (p/rules-by-consequent (:index kb3) 'snapConsq)))))))))

;; ---- staleness: an image about a KB that has moved ----------------------

(deftest a-stale-image-is-discarded-and-rebuilt
  (testing "an image that is internally perfect and describes an older record set"
    (with-snapshot-dir
      (fn [dir]
        (let [aside (str dir "-aside")]
          (try
            (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
            (backend/close-dir! dir)
            (copy-tree! (snap/snapshot-root dir) aside)     ; the image as of now

            ;; move the records on, and let the close write a *newer* image
            (let [[kb2 _] (opening dir)]
              (v/assert kb2 '(fish SnapNemo) 'CxUniverse {:strength :monotonic}))
            (let [want (do (backend/close-dir! dir)
                           (let [[kb3 _] (opening dir)
                                 a (answers kb3)]
                             (backend/close-dir! dir)
                             a))]
              ;; put the older image back: self-consistent, and about a KB that is gone
              (copy-tree! aside (snap/snapshot-root dir))
              (let [[kb4 rebuilds] (opening dir)]
                (is (= 1 rebuilds) "the stamp caught it")
                (is (= want (answers kb4)) "and the records answered instead")
                (is (v/ask? kb4 '(fish SnapNemo) 'CxUniverse)
                    "including the fact the stale image had never heard of")))
            (finally (rm-rf! aside))))))))

(deftest a-cleared-store-declines-an-image-of-the-records-it-held
  ;; `clear!` truncates the logs, so a record of the same byte length refills an old slot
  ;; exactly, and the store below differs from the one the older image describes in
  ;; content alone.  The epoch the wipe mints is the part of the stamp that separates the
  ;; two.
  (with-snapshot-dir
    (fn [dir]
      (let [aside (str dir "-aside")]
        (try
          (v/assert (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})
                    '(dog SnapMuffet) 'CxUniverse {:strength :monotonic})
          (backend/close-dir! dir)
          (copy-tree! (snap/snapshot-root dir) aside)       ; the image of the dog record
          (let [[kb2 _] (opening dir)]
            (v/clear! kb2)
            (v/assert kb2 '(cat SnapTiddle) 'CxUniverse {:strength :monotonic}))
          (backend/close-dir! dir)
          (copy-tree! aside (snap/snapshot-root dir))
          (let [[kb3 rebuilds] (opening dir)]
            (is (= 1 rebuilds) "the stamp caught it")
            (is (v/ask? kb3 '(cat SnapTiddle) 'CxUniverse))
            (is (empty? (v/sentexes-matching kb3 '(dog ?x) 'CxUniverse))))
          (finally (rm-rf! aside)))))))

;; ---- every other mismatch class, one at a time --------------------------

(def ^:private mismatches
  [["a bumped snapshot format"      (fn [_ m] (update m :format inc))                :layout-changed]
   ["a bumped index layout"         (fn [_ m] (update m :index-layout inc))          :layout-changed]
   ["the other endianness"          (fn [_ m] (assoc m :byte-order "BIG_ENDIAN"))    :byte-order]
   ["records that moved"            (fn [_ m] (update-in m [:records :digest] inc))  :records-differ]
   ["a section short of its header"
    (fn [dir m]
      (with-open [raf (RandomAccessFile. (str (snap/snapshot-root dir) "/trie.csr") "rw")]
        (.setLength raf (max 0 (- (.length raf) 64))))
      m)
    :entries-truncated]
   ;; the fallback blob holds the slot roster, which the predicate-agnostic argument
   ;; reads descend through — so losing it must discard the image, never open with
   ;; every `sentexes-with-arg` empty
   ["a missing roots fallback blob"
    (fn [dir m]
      (.delete (File. (str (snap/snapshot-root dir) "/roots-fallback.nippy")))
      m)
    :entries-truncated]
   ["a truncated roots fallback blob"
    (fn [dir m]
      (with-open [raf (RandomAccessFile. (str (snap/snapshot-root dir) "/roots-fallback.nippy") "rw")]
        (.setLength raf (max 0 (dec (.length raf)))))
      m)
    :entries-truncated]
   ;; same length, garbage content: past the length check, so it is the strict thaw
   ;; (`read-fallback`) that has to catch it
   ["a corrupt roots fallback blob of the recorded length"
    (fn [dir m]
      (with-open [raf (RandomAccessFile. (str (snap/snapshot-root dir) "/roots-fallback.nippy") "rw")]
        (dotimes [i (min 16 (.length raf))]
          (.seek raf i)
          (.writeByte raf 0xFF)))
      m)
    :unreadable]])

(deftest ^:slow each-mismatch-class-names-itself-and-falls-back
  (doseq [[label mutate expected] mismatches]
    (testing label
      (with-snapshot-dir
        (fn [dir]
          (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
                want (answers kb)]
            (backend/close-dir! dir)
            (let [m (f/read-nippy-file (meta-path dir) nil)]
              (f/write-nippy-atomic! (meta-path dir) (mutate dir m))
              ;; the decision names what changed …
              (is (= {:index :rebuild :reason expected}
                     (select-keys (snap/load! dir (scratch-index label) (constantly (:records m)))
                                  [:index :reason])))
              ;; … and an ordinary open takes the fallback and is right anyway
              (let [[kb2 rebuilds] (opening dir)]
                (is (= 1 rebuilds) "the records were the fallback")
                (is (= want (answers kb2)))))))))))

(deftest an-uncommitted-image-is-not-read
  (testing "a crash before the meta lands leaves sections nothing points at"
    (with-snapshot-dir
      (fn [dir]
        (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
              want (answers kb)]
          (backend/close-dir! dir)
          (is (.delete (meta-file dir)) "the commit marker goes; the sections stay")
          (is (.exists (File. (str (snap/snapshot-root dir) "/trie.csr"))))
          (let [[kb2 rebuilds] (opening dir)]
            (is (= 1 rebuilds) "no meta means no image, whatever else is on disk")
            (is (= want (answers kb2)))))))))

(deftest an-absent-image-is-a-plain-rebuild
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
            want (answers kb)]
        (is (not (.exists (meta-file dir))) "nothing was written — the directory never closed")
        (let [[kb2 rebuilds] (opening dir)]
          (is (= 1 rebuilds))
          (is (= want (answers kb2))))))))

;; ---- order independence: the ids differ, the answers do not -------------

(deftest a-rebuild-and-a-mapped-load-answer-alike
  (testing "token ids depend on first-encounter order and nothing above them reads one"
    (with-snapshot-dir
      (fn [dir]
        (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
              want (answers kb)]
          ;; the two argument reads are only a check on the image if the corpus makes
          ;; them answer something: an equality between two empty sets holds however
          ;; badly the scope ids round-tripped
          (is (= 3 (count (:agnostic want)) (:agn-n want))
              "SnapMuffet sits at position 1 under dog, likes and bornIn")
          (is (= 1 (count (:scoped want))) "and SnapBall at position 2 under likes")
          (backend/close-dir! dir)
          ;; a mapped load cites the ids the image was written with …
          (let [[kb2 mapped-rebuilds] (opening dir)]
            (is (zero? mapped-rebuilds))
            (is (= want (answers kb2))))
          (backend/close-dir! dir)
          ;; … and a rebuild re-interns the vocabulary in the records' arrival order,
          ;; which is a different numbering of the same index
          (.delete (meta-file dir))
          (let [[kb3 rebuilds] (opening dir)]
            (is (= 1 rebuilds))
            (is (= want (answers kb3)) "equal answers, whatever the ids were")))))))

;; ---- the cadence --------------------------------------------------------

(deftest the-writer-refreshes-a-drifted-image-without-a-close
  ;; The image is written when the directory closes, which a process killed outright
  ;; never reaches: a writer that ran for weeks would reopen onto no image and pay the
  ;; whole reindex the backend is named to skip.  So the writer rewrites it mid-life,
  ;; once the live index has drifted far enough from the one on disk.
  ;;
  ;; The interval floor is dropped to zero rather than waited out, and the threshold left
  ;; at its default: what this checks is that the drift trigger fires from the write entry point
  ;; on the writer's thread, not how long the floor is.
  (with-properties {"vaelii.disk.compact-min-interval-ms" "0"}
    (fn []
      (with-snapshot-dir
        (fn [dir]
          (let [kb (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})]
            (v/clear! kb)
            (is (not (.exists (meta-file dir)))
                "a fresh directory holds no image, and nothing has closed")
            (build! kb)
            (is (.exists (meta-file dir))
                "the write entry point wrote one: drift from an absent image is total")
            ;; and it describes the records, which is the only thing that makes it worth
            ;; having — a mid-life image stamped against a store that has moved on is one
            ;; the next open discards
            (let [want (answers kb)]
              (backend/close-dir! dir)
              (let [[kb2 rebuilds] (opening dir)]
                (is (zero? rebuilds) "so the next open maps rather than reindexes")
                (is (= want (answers kb2)))))))))))

(deftest a-fresh-image-is-not-rewritten-on-every-write
  ;; The refresh is a full CSR write on the writer's thread, so the trigger has to be a
  ;; threshold and not a counter.  With the floor at its default no second image is due,
  ;; whatever the drift.
  (with-snapshot-dir
    (fn [dir]
      (let [kb (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})]
        (v/clear! kb)
        (build! kb)
        (is (not (.exists (meta-file dir)))
            "the interval floor has not elapsed, so the drift never gets asked about")))))

(deftest auto-compact-off-declines-the-mid-life-refresh-outright
  ;; A batch that fills a KB in one run and closes cleanly wants exactly one image, at the
  ;; end, and neither of the cadence's two numbers can say so: the floor only rate-limits
  ;; (and moves the record store's compaction with it), and the drift ratio's `0` is the
  ;; *most* eager setting rather than the off one — as a threshold it means "any drift at
  ;; all".  A refresh is an opportunistic compaction of a derived structure, so the knob
  ;; that already governs those is the one that says it.
  (with-properties {"vaelii.disk.compact-min-interval-ms" "0"
                    "vaelii.index.snapshot-drift" "0"
                    "vaelii.disk.auto-compact" "false"}
    (fn []
      (with-snapshot-dir
        (fn [dir]
          (let [kb (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})]
            (v/clear! kb)
            (build! kb)
            (is (not (.exists (meta-file dir)))
                "the floor is zero and the drift threshold the most eager there is — and still nothing was written")
            (testing "and the close writes the one image the caller asked for"
              (backend/close-dir! dir)
              (is (.exists (meta-file dir)))
              (let [[_ rebuilds] (opening dir)]
                (is (zero? rebuilds) "which the next open maps")))))))))

(deftest a-drift-threshold-of-zero-is-the-most-eager-setting-and-not-the-off-one
  ;; The trap worth pinning: an operator reaching for 0 to mean "never" gets a whole CSR
  ;; rewrite on every write past the floor.  The switch is `vaelii.disk.auto-compact`
  ;; above; this is what the low end of the ratio actually does.
  (with-properties {"vaelii.disk.compact-min-interval-ms" "0"
                    "vaelii.index.snapshot-drift" "0"}
    (fn []
      (with-snapshot-dir
        (fn [dir]
          (let [kb    (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})
                saves (atom 0)
                real  snap/save!]
            (v/clear! kb)
            (with-redefs [snap/save! (fn [& args] (swap! saves inc) (apply real args))]
              (dotimes [i 5]
                (v/assert kb (list 'cat (symbol (str "SnapEager" i))) 'CxUniverse
                          {:strength :monotonic})))
            (is (= 5 @saves) "one whole image per write, which is the pathology and not the switch")))))))

(deftest a-refresh-attempt-restarts-the-floor-without-moving-the-baseline
  ;; A save that throws — a full disk, a directory gone read-only — writes no image, so the
  ;; drift it was called on is still there when it returns.  A cadence stamped only by a
  ;; completed save would therefore read due again on the very next write, and a broken
  ;; directory would be re-attempted per assert forever.  The attempt restarts the floor;
  ;; only a completed save moves the baseline.
  ;;
  ;; The clock is aged by hand rather than slept through: what is under test is which event
  ;; moves it, and a sleep would be testing how long a floor is.
  (with-snapshot-dir
    (fn [dir]
      (snap/note-no-image! dir)
      (swap! @#'snap/image-state update (#'snap/state-key dir) assoc :at 0)
      (with-properties {"vaelii.disk.compact-min-interval-ms" "100000"
                        "vaelii.index.snapshot-drift" "0.5"}
        (fn []
          (is (snap/due? dir 40) "an aged clock over total drift: a refresh is due")
          (snap/note-attempt! dir)
          (is (not (snap/due? dir 40))
              "and the attempt restarted the floor, whether or not it wrote an image")
          (is (== 1.0 (snap/drift dir 40))
              "while the baseline still describes what is on disk, which is nothing")))
      (testing "and a directory with no cadence state gets none from an attempt"
        (snap/forget-image! dir)
        (snap/note-attempt! dir)
        (is (not (snap/due? dir 40)) "there is no image to be drifted from")))))

(deftest a-refresh-that-throws-costs-the-image-and-not-the-write
  ;; By the time the refresh runs the sentex is durably stored and indexed, and the image
  ;; is a cache of derived state — so a failure to write one must not fail the assert, and
  ;; must not skip the observation call sites that run after it (`observe/notify-add`, the
  ;; incremental matcher's alpha-memory entry point, which would otherwise be permanently behind
  ;; the store).  The image on disk is left exactly as it was.
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 _] (opening dir)
            before  (.lastModified (meta-file dir))]
        (with-properties {"vaelii.disk.compact-min-interval-ms" "0"
                          "vaelii.index.snapshot-drift" "0.001"}
          (fn []
            (with-redefs [snap/save! (fn [& _] (throw (java.io.IOException. "the disk filled")))]
              (v/assert kb2 '(cat SnapTom) 'CxUniverse {:strength :monotonic})
              (v/assert kb2 '(likes SnapTom SnapBall) 'CxUniverse {:strength :monotonic}))))
        (is (v/ask? kb2 '(cat SnapTom) 'CxUniverse)
            "the write went through: a failed cache write is not a failed data write")
        (is (= 2 (count (v/sentexes-matching kb2 '(likes ?x SnapBall) 'CxUniverse)))
            "and so did the one after it, so nothing stopped at the throw")
        (is (= before (.lastModified (meta-file dir)))
            "and the image on disk is the one that was already there")
        (testing "which still reads, because a refusal to refresh left it whole"
          (let [want (answers kb2)]
            (backend/close-dir! dir)
            (let [[kb3 rebuilds] (opening dir)]
              (is (zero? rebuilds))
              (is (= want (answers kb3))
                  "and the close's image carries the writes the failed refresh did not"))))))))

(deftest a-second-open-over-a-current-image-does-not-force-a-rewrite
  ;; `open-kb` starts the cadence clock for every KB constructed over a directory, and they
  ;; all share one index — so a start that clobbered would reset the baseline to "no image"
  ;; on the second open, `drift` would read 1.0 against an image that is exactly right, and
  ;; the first write past the floor would rewrite a whole CSR for nothing.
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 rebuilds] (opening dir)]
        (is (zero? rebuilds) "the image maps, so the baseline is the live count")
        ;; a second KB over the same directory: same stores, same index, one more
        ;; registration
        (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false})
        (let [saves (atom 0)
              real  snap/save!]
          (with-properties {"vaelii.disk.compact-min-interval-ms" "0"}
            (fn []
              (with-redefs [snap/save! (fn [& args] (swap! saves inc) (apply real args))]
                (doseq [i (range 5)]
                  (v/assert kb2 (list 'cat (symbol (str "SnapCat" i))) 'CxUniverse
                            {:strength :monotonic})))))
          (is (zero? @saves)
              (str "five writes over a current image rewrote it " @saves " time(s)"))
          (is (< (snap/drift dir (p/count-at (:index kb2) [])) 0.5)
              "the baseline is the image's own count, not zero"))))))

;; ---- a lazy read walked across a refresh --------------------------------

(defn- walked
  "What a *realized* read answers — the `[context sentence]` pairs — which is the oracle a
  lazy walk of the same pattern has to reproduce."
  [kb pattern context]
  (into #{} (map (juxt :context :sentence)) (v/sentexes-matching kb pattern context)))

(defn- walk-writing!
  "Walk a lazy `sentexes-matching` seq to its end, asserting a fresh fact per element, and
  return the `[context sentence]` pairs it yielded.

  Every step of the walk therefore crosses the whole write entry point, the image refresh
  included — which is the point: `save!` freezes the live trie into CSR in place, and this
  is what does it under an unconsumed tail.  The asserted facts are a unary type, so they
  land in the trie and the roots without joining the pattern being walked."
  [kb pattern context tag]
  (let [seen (atom #{})
        n    (atom 0)]
    (doseq [sx (v/sentexes-matching kb pattern context)]
      (swap! seen conj [(:context sx) (:sentence sx)])
      (v/assert kb (list 'cat (symbol (str tag (swap! n inc)))) 'CxUniverse
                {:strength :monotonic}))
    @seen))

(deftest a-lazy-match-seq-is-walked-across-a-mid-life-refresh
  ;; `core/sentexes-matching` promises a seq that is lazy over live state — "a seq held
  ;; across a write yields what is stored when it is walked" — and asserting while walking
  ;; one is the pattern `forward-chain` is built on.  The mid-life refresh puts a
  ;; `columnar/compact!` on that write path, so the supported pattern now freezes the trie
  ;; under an unconsumed tail, and once mapped it thaws the leaf columns out from under one
  ;; too.  Both are safe, and the reason is in `save!`: an index read is eager per read, so
  ;; a freeze lands between reads and never inside one.  Here to stay safe.
  (with-properties {"vaelii.disk.compact-min-interval-ms" "0"
                    "vaelii.index.snapshot-drift" "0.2"}
    (fn []
      (with-snapshot-dir
        (fn [dir]
          (let [saves (atom 0)
                real  snap/save!]
            (with-redefs [snap/save! (fn [& args] (swap! saves inc) (apply real args))]
              (testing "over an index this process built"
                (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir
                                               :recover? false}))
                      want (walked kb '(parentOf ?x ?y) 'CxUniverse)]
                  (reset! saves 0)
                  (is (= want (walk-writing! kb '(parentOf ?x ?y) 'CxUniverse "SnapBuilt"))
                      "the walk yielded the set a realized read yields")
                  (is (pos? @saves) "and a refresh actually fired inside it")
                  (backend/close-dir! dir)))
              (testing "and over one mapped back from its image, which the walk thaws"
                (let [[kb2 rebuilds] (opening dir)]
                  (is (zero? rebuilds))
                  (is (snapshot-types/snapshot-mapped? (:trie (:index kb2))) "the trie opened mapped")
                  (reset! saves 0)
                  (let [want (walked kb2 '(parentOf ?x ?y) 'CxUniverse)]
                    (is (= want (walk-writing! kb2 '(parentOf ?x ?y) 'CxUniverse "SnapMapped"))))
                  (is (pos? @saves))
                  (is (not (snapshot-types/snapshot-mapped? (:trie (:index kb2))))
                      "and the walk's own writes thawed it, so the freeze ran over heap arrays")
                  (testing "and at a variable context, where the fan reads the index per reader"
                    (reset! saves 0)
                    (let [want (walked kb2 '(parentOf ?x ?y) '?ctx)]
                      (is (= want (walk-writing! kb2 '(parentOf ?x ?y) '?ctx "SnapFanned"))))
                    (is (pos? @saves))))))))))))

;; ---- the platform the image publishes on --------------------------------
;;
;; The commit is `Files/move` with `REPLACE_EXISTING` over a file this process has
;; mapped, and Windows does not permit that.  CI runs neither Windows nor an honest way
;; to fake one, so the platform *read* is injected: string-matching `os.name` inside the
;; test would assert the expression under test.

(defn- on-windows
  "Run `f` with the snapshot's platform read answering Windows."
  [f]
  (with-redefs [snap/os-name (constantly "Windows 11")] (f)))

(deftest the-image-refuses-the-platform-it-corrupts-on
  (testing "the backend named on a platform that cannot publish is an error, not a default"
    (on-windows
     (fn []
       (with-snapshot-dir
         (fn [_dir]
           (let [e (is (thrown? clojure.lang.ExceptionInfo (snap/enabled?)))]
             (is (= :unsupported-platform (:type (ex-data e))))
             (is (= :snapshot (:index (ex-data e))))
             (is (= {:index :columnar} (:remedy (ex-data e))) "naming the pairing to take")
             (is (= "Windows 11" (:os (ex-data e))))
             (is (re-find #"Windows" (ex-message e)) "the message names the platform")
             (is (re-find #"rebuild" (ex-message e)) "and what the remedy costs")))))))
  (testing "and it reaches the open, which is where an operator meets it"
    (on-windows
     (fn []
       (with-snapshot-dir
         (fn [dir]
           (let [e (is (thrown? clojure.lang.ExceptionInfo
                                (v/open-kb {:records :disk :index :snapshot :dir dir
                                            :recover? false})))]
             (is (= :unsupported-platform (:type (ex-data e)))))))))))

(deftest the-refused-platform-still-runs-the-disk-backend
  ;; Only the image's publish is implicated.  A guard that reached the records or the
  ;; lock would turn a working platform into a refused one on the strength of one index
  ;; representation, so the pairing the refusal names as the remedy has to work there.
  (let [dir (tmpdir)]
    (try
      (on-windows
       (fn []
         (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir
                                        :recover? false}))
               want (answers kb)]
           (backend/close-dir! dir)
           (is (not (.exists (meta-file dir))) "no image is written for a backend that named none")
           (let [[kb2 rebuilds] (opening-columnar dir)]
             (is (= 1 rebuilds) "the index rebuilds from the records, which is what :columnar is")
             (is (= want (answers kb2)))))))
      (finally (backend/close-dir! dir) (rm-rf! dir)))))

(deftest an-image-on-a-platform-that-cannot-refresh-it-is-discarded
  ;; The remaining case: a directory carrying an image, opened where it can be mapped and
  ;; never rewritten.  A mapped index that cannot be refreshed is a cache going stale
  ;; against its own records, so it joins the mismatch classes beside byte order rather
  ;; than being read and hoped for.
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir
                                     :recover? false}))
            want (answers kb)]
        (backend/close-dir! dir)
        (is (.exists (meta-file dir)) "this platform wrote one")
        (let [m (f/read-nippy-file (meta-path dir) nil)]
          (is (= {:index :rebuild :reason :unsupported-platform}
                 (on-windows
                  (fn []
                    (select-keys (snap/load! dir (scratch-index "platform")
                                             (constantly (:records m)))
                                 [:index :reason]))))))
        (testing "and this platform still maps it"
          (let [[kb2 rebuilds] (opening dir)]
            (is (zero? rebuilds))
            (is (= want (answers kb2)))))))))

;; ---- the refusals the section readers raise ------------------------------
;;
;; `load!` answers every one of these with `{:index :rebuild}`, which is the whole design:
;; an image in doubt is discarded and the records are always enough.  The refusals
;; themselves are raised one layer down, at the readers, which is where a caller reading
;; a `:type` out of an `ex-data` meets them — so they are provoked there.

(defn- zero-magic!
  "Overwrite a section's four-byte magic number with zero, leaving its length alone — the
  shape a file of the right size in the right place has when something else wrote it."
  [^String path]
  (with-open [raf (RandomAccessFile. path "rw")]
    (.seek raf 0)
    (.writeInt raf 0)))

(deftest a-section-that-is-not-a-vaelii-snapshot-is-refused-on-its-magic-number
  ;; The magic number is the one check that reads the section's own bytes rather than the
  ;; meta beside it.  Everything else agrees on a file of the right length in the right
  ;; place, so without this a trie's worth of somebody else's bytes is mapped and walked.
  ;; Each section names itself, because the refusal is spliced into the WARN an operator
  ;; reads and "did not read" says nothing about whether the data is gone.
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
            want (answers kb)]
        (backend/close-dir! dir)
        (let [^String root (snap/snapshot-root dir)
              m     (f/read-nippy-file (meta-path dir) nil)
              store (scratch-index :magic)]
          (doseq [[part file load! section] [[:trie  "trie.csr"  #'snap/load-trie!  (:trie m)]
                                             [:roots "roots.csr" #'snap/load-roots! (:roots m)]]]
            (testing (name part)
              (let [path (str root "/" file)
                    _    (zero-magic! path)
                    e    (is (thrown? clojure.lang.ExceptionInfo (load! store path section)))
                    d    (ex-data e)]
                (is (= :bad-snapshot (:type d)))
                (is (= part (:part d)) "the refusal names which section")
                (is (= 0 (:magic d)) "and the number it read")
                (is (not= 0 (:expected d)) "against the one it wanted"))))
          (p/clear-index! store))
        (testing "and an ordinary open rebuilds from the records, which are untouched"
          (let [[kb2 rebuilds] (opening dir)]
            (is (= 1 rebuilds))
            (is (= want (answers kb2)))))))))

(deftest a-fallback-blob-that-does-not-thaw-whole-is-refused-rather-than-defaulted
  ;; The fallback blob carries the slot roster — the predicates present at a
  ;; `(pos, term)`, which the agnostic argument reads descend through — so a thaw that
  ;; comes back torn has to condemn the image.  A default of the empty value would open an
  ;; index answering `#{}` to every `sentexes-with-arg`, which is indistinguishable from a KB that holds
  ;; nothing at any position.
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
            want (answers kb)]
        (backend/close-dir! dir)
        (let [^String root (snap/snapshot-root dir)
              m     (f/read-nippy-file (meta-path dir) nil)]
          ;; garbage of the recorded length: past the length check in `decision`, so it is
          ;; the strict thaw that has to catch it
          (with-open [raf (RandomAccessFile. (str root "/roots-fallback.nippy") "rw")]
            (dotimes [i (min 16 (.length raf))]
              (.seek raf i)
              (.writeByte raf 0xFF)))
          (let [e (is (thrown? clojure.lang.ExceptionInfo (#'snap/read-fallback root m)))
                d (ex-data e)]
            (is (= :torn-snapshot (:type d)))
            (is (= (get-in m [:fallback :entries]) (:expected d))
                "naming the entry count the meta vouches for")
            (is (nil? (:entries d)) "and nothing read, since the blob did not thaw")))
        (testing "and an ordinary open rebuilds from the records"
          (let [[kb2 rebuilds] (opening dir)]
            (is (= 1 rebuilds))
            (is (= want (answers kb2)))))))))

(deftest a-dictionary-that-reloads-short-of-its-log-condemns-the-image
  ;; The mapped edges cite durable token ids, and an id is the log position it was written
  ;; at — so a dictionary that comes back holding fewer entries than the log has shifted
  ;; every id past the gap, and each edge still is indistinguishable from a perfectly legal int.  The count
  ;; is the only witness there is, which is why it is compared rather than assumed.
  ;;
  ;; The disagreement is staged at the dictionary, because the thing that shifts a
  ;; numbering in practice is a Clojure-equal pair of frames, and that one is named and
  ;; repaired a layer earlier (below) before this check can see it.  A `reify` delegating
  ;; to a real dictionary is what a protocol change takes: a redef of `token-count` is a
  ;; var no protocol call reads.
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [real  (tok/token-dict)
            short (reify tok/ITokens
                    (intern-token! [_ t] (tok/intern-token! real t))
                    (token-id      [_ t] (tok/token-id real t))
                    (id-token      [_ i] (tok/id-token real i))
                    (token-count   [_]   (dec (tok/token-count real)))
                    (clear-tokens! [_]   (tok/clear-tokens! real)))
            root  (snap/snapshot-root dir)
            e     (is (thrown? clojure.lang.ExceptionInfo (#'snap/load-dictionary! short root)))
            d     (ex-data e)]
        (is (= :torn-snapshot (:type d)))
        (is (= (dec (long (:durable d))) (:loaded d))
            "the refusal carries both counts, so a reader sees the size of the shift")
        (is (pos? (long (:durable d))) "and the log it was read against is a real one")))))

;; ---- a dictionary an older build wrote twice ----------------------------

(deftest a-token-log-holding-a-clojure-equal-pair-is-refused-by-name-and-rewritten
  ;; `1970` and `(int 1970)` are one token under `hasheq`/`equiv` and two frames in a log
  ;; written before the forward map keyed that way.  The dictionary then reloads one entry
  ;; short and every id past the pair moves, which is the shift above — but this one the
  ;; load can do something about, so it says which cause it is and rewrites the log rather
  ;; than condemning the image again on every open.
  (let [dir (tmpdir)]
    (try
      (let [log (f/open-log (str dir "/tokens.log"))]
        (try (doseq [t ['aToken 1970 (int 1970)]] (f/append-record! log t))
             (finally (f/close! log))))
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (#'snap/load-dictionary! (tok/token-dict) dir)))
            d (ex-data e)]
        (is (= :duplicate-tokens (:type d)))
        (is (= 1 (:duplicates d)) "the one pair the log holds twice")
        (is (= 2 (:entries d)) "and what the rewritten log holds"))
      (testing "and the rewritten log reloads whole, so the next open maps again"
        (is (= 2 (#'snap/load-dictionary! (tok/token-dict) dir))))
      (finally (rm-rf! dir)))))

(deftest a-token-log-holding-a-duplicate-is-repaired-rather-than-rediagnosed
  ;; The forward map keys on `tokens/Key`, so `2` and `(int 2)` are one entry — but a log
  ;; written before it did can hold both as separate frames.  It then reloads one entry
  ;; short of the log, every id past the pair shifts, and the image is condemned; the
  ;; rebuilt index is snapshotted against the same log, so the *next* open is condemned
  ;; too, and the one after that.  One open repairs it and the next maps again.
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :snapshot :dir dir :recover? false}))
            want (answers kb)]
        (backend/close-dir! dir)
        ;; `(bornIn SnapMuffet 1970)` put a Long in the dictionary; append the Integer an
        ;; older build would have minted beside it.  Nothing else on disk moves.
        (let [log (f/open-log (str (snap/snapshot-root dir) "/tokens.log"))]
          (try (f/append-record! log (int 1970)) (finally (f/close! log))))
        (testing "the decision names the duplicate, not a torn image"
          (let [m (f/read-nippy-file (meta-path dir) nil)]
            (is (= {:index :rebuild :reason :duplicate-tokens}
                   (select-keys (snap/load! dir (scratch-index :dups)
                                            (constantly (:records m)))
                                [:index :reason])))))
        (testing "the KB opens, rebuilds once, and answers"
          (let [[kb2 rebuilds] (opening dir)]
            (is (= 1 rebuilds) "the records were the fallback")
            (is (= want (answers kb2)))))
        (backend/close-dir! dir)
        (testing "and the repaired log lets the next open map its image again"
          (let [[kb3 rebuilds] (opening dir)]
            (is (zero? rebuilds) "the duplicate is gone for good, not diagnosed forever")
            (is (= want (answers kb3)))))))))
