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
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files Paths StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-snapshot-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (File. dir)))] (.delete ^File f)))

(defn- copy-tree!
  "Copy every regular file of `from` into a fresh `to` — how a test takes an image aside
  and puts it back, which is the only honest way to produce a *stale* one."
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
  "Run `(f dir)` in a fresh directory with the snapshot switched on, restoring the property
  and closing the stores afterwards.  The property is what `open-kb` reads to decide the
  mode; the *validity* check is never gated on it, which is why it is read here and
  nowhere else."
  [f]
  (let [dir  (tmpdir)
        prev (System/getProperty "vaelii.index.snapshot")]
    (System/setProperty "vaelii.index.snapshot" "true")
    (try (f dir)
         (finally
           (backend/close-dir! dir)
           (if prev
             (System/setProperty "vaelii.index.snapshot" prev)
             (System/clearProperty "vaelii.index.snapshot"))
           (rm-rf! dir)))))

;; ---- the content, and what it must answer -------------------------------

(defn- build!
  "A KB with something of every indexed shape in it: plain binary facts, a unary type, a
  **number** argument (a trie token that is not a handle), and a rule (which lands in the
  rule index rather than the roots)."
  [kb]
  (v/clear! kb)
  (doseq [i (range 60)]
    (v/assert kb (list 'parentOf (symbol (str "Snap" i)) (symbol (str "Snap" (inc i))))
              'UniverseContext {:strength :monotonic}))
  (v/assert kb '(dog SnapMuffet) 'UniverseContext {:strength :monotonic})
  (v/assert kb '(likes SnapMuffet SnapBall) 'UniverseContext {:strength :monotonic})
  (v/assert kb '(bornIn SnapMuffet 1970) 'UniverseContext {:strength :monotonic})
  (v/assert-rule kb '[(parentOf ?x ?y)] '(ancestorOf ?x ?y) 'UniverseContext)
  kb)

(defn- answers
  "Everything the index is asked for, through the public surface plus the two index reads
  (`term-count`, the root count) no query would notice going wrong."
  [kb]
  {:parents  (count (v/sentexes-matching kb '(parentOf ?x ?y) 'UniverseContext))
   :dog      (v/ask? kb '(dog SnapMuffet) 'UniverseContext)
   :ball     (count (v/sentexes-matching kb '(likes ?x SnapBall) 'UniverseContext))
   :number   (count (v/sentexes-matching kb '(bornIn ?x 1970) 'UniverseContext))
   :ancestor (v/ask? kb '(ancestorOf Snap0 Snap1) 'UniverseContext)
   :terms    (p/term-count (:index kb))
   :nodes    (p/count-at (:index kb) [])})

(defn- opening
  "Open a KB over `dir` in recovery mode, counting the reindexes that ran.  Returns
  `[kb reindexes]`."
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

;; ---- the round trip ------------------------------------------------------

(deftest snapshot-round-trip-skips-the-rebuild
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
            want (answers kb)]
        (backend/close-dir! dir)
        (is (.exists (meta-file dir)) "closing the directory wrote the image")
        (let [[kb2 rebuilds] (opening dir)]
          (is (zero? rebuilds) "no reindex ran")
          (is (= want (answers kb2))))))))

(deftest a-write-after-a-mapped-open-thaws-and-answers
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 rebuilds] (opening dir)]
        (is (zero? rebuilds))
        (v/assert kb2 '(cat SnapTom) 'UniverseContext {:strength :monotonic})
        (v/assert kb2 '(likes SnapTom SnapBall) 'UniverseContext {:strength :monotonic})
        (is (v/ask? kb2 '(cat SnapTom) 'UniverseContext) "the trie thawed out of its mapping")
        (is (= 2 (count (v/sentexes-matching kb2 '(likes ?x SnapBall) 'UniverseContext)))
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
        (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
        (backend/close-dir! dir)
        (let [[kb2 _] (opening dir)
              stamp   #(drs/slot-fingerprint (:records kb2))]
          (is (= {:index :skipped :reason :unchanged}
                 (select-keys (snap/save! dir (:index kb2) stamp) [:index :reason]))
              "the image already *is* this index — writing it would thaw the roots to read them")
          ;; and a write puts it back in play
          (v/assert kb2 '(cat SnapTom) 'UniverseContext {:strength :monotonic})
          (is (= :saved (:index (snap/save! dir (:index kb2) stamp)))))))))

(deftest a-half-thawed-index-writes-its-sections-out-of-the-mapping
  ;; `index-rule` writes the rule index and touches no trie path (the rule *sentex* does
  ;; that separately — this is the half `reindex/index-rule-entry` posts on its own).  So
  ;; it thaws the roots and leaves the trie mapped, and the next image is written with its
  ;; leaf sections read **straight out of the live mapping** — the one write path with no
  ;; heap array to copy from, and one the `:unchanged` skip above keeps an ordinary close
  ;; from reaching.
  (with-snapshot-dir
    (fn [dir]
      (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
      (backend/close-dir! dir)
      (let [[kb2 _] (opening dir)
            idx     (:index kb2)]
        (is (columnar/mapped? idx) "the trie opened mapped")
        (p/index-rule idx 987654 '[snapAnte] 'snapConsq)
        (is (columnar/mapped? idx) "and the rule index left it so — only the roots thawed")
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
            (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
            (backend/close-dir! dir)
            (copy-tree! (snap/snapshot-root dir) aside)     ; the image as of now

            ;; move the records on, and let the close write a *newer* image
            (let [[kb2 _] (opening dir)]
              (v/assert kb2 '(fish SnapNemo) 'UniverseContext {:strength :monotonic}))
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
                (is (v/ask? kb4 '(fish SnapNemo) 'UniverseContext)
                    "including the fact the stale image had never heard of")))
            (finally (rm-rf! aside))))))))

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
   ;; the fallback blob holds the argument roots — primary index truth — so losing
   ;; it must discard the image, never open with every argument-root read empty
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

(deftest each-mismatch-class-names-itself-and-falls-back
  (doseq [[label mutate expected] mismatches]
    (testing label
      (with-snapshot-dir
        (fn [dir]
          (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
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
        (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
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
      (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
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
        (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir :recover? false}))
              want (answers kb)]
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
  (testing "the property set on a platform that cannot publish is an error, not a default"
    (on-windows
     (fn []
       (with-snapshot-dir
         (fn [_dir]
           (let [e (is (thrown? clojure.lang.ExceptionInfo (snap/enabled?)))]
             (is (= :unsupported-platform (:type (ex-data e))))
             (is (= "vaelii.index.snapshot" (:property (ex-data e))))
             (is (= "Windows 11" (:os (ex-data e))))
             (is (re-find #"Windows" (ex-message e)) "the message names the platform")
             (is (re-find #"rebuild" (ex-message e)) "and what unsetting it costs")))))))
  (testing "and it reaches the open, which is where an operator meets it"
    (on-windows
     (fn []
       (with-snapshot-dir
         (fn [dir]
           (let [e (is (thrown? clojure.lang.ExceptionInfo
                                (v/open-kb {:records :disk :index :columnar :dir dir
                                            :recover? false})))]
             (is (= :unsupported-platform (:type (ex-data e)))))))))))

(deftest the-refused-platform-still-runs-the-disk-backend
  ;; Only the image's publish is implicated.  A guard that reached the records or the
  ;; lock would turn a working platform into a refused one on the strength of an
  ;; off-by-default feature.
  (let [dir (tmpdir)]
    (try
      (on-windows
       (fn []
         (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir
                                        :recover? false}))
               want (answers kb)]
           (is (false? (snap/enabled?)) "with the property unset there is nothing to refuse")
           (backend/close-dir! dir)
           (is (not (.exists (meta-file dir))) "and no image was written")
           (let [[kb2 rebuilds] (opening dir)]
             (is (= 1 rebuilds) "the index rebuilds from the records, as it always did")
             (is (= want (answers kb2)))))))
      (finally (backend/close-dir! dir) (rm-rf! dir)))))

(deftest an-image-on-a-platform-that-cannot-refresh-it-is-discarded
  ;; The remaining case: a directory carrying an image, opened where it can be mapped and
  ;; never rewritten.  A mapped index that cannot be refreshed is a cache going stale
  ;; against its own records, so it joins the mismatch classes beside byte order rather
  ;; than being read and hoped for.
  (with-snapshot-dir
    (fn [dir]
      (let [kb   (build! (v/open-kb {:records :disk :index :columnar :dir dir
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
