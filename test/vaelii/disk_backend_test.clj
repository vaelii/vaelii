;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-backend-test
  "The `:disk` backend wiring: the single-writer lock fails a second opener fast, and
  two KBs over one directory in a process share the durable stores (the restart
  contract the recovery tests rely on)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.lock :as lock]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.test-util :as tu])
  (:import [java.io RandomAccessFile]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-disk-be-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- with-tmp
  "Run `(f dir)` in a fresh temp directory, closing any disk stores opened on it (so
  the durability daemon doesn't outlive the dir) and deleting it afterwards."
  [f]
  (let [dir (tmpdir)]
    (try (f dir)
         (finally (backend/close-dir! dir) (rm-rf! dir)))))

(deftest a-second-jvm-holding-the-lock-fails-fast
  (with-tmp
    (fn [dir]
      ;; stand in for another process: hold an exclusive OS FileLock on the lock file
      ;; directly.  The store's own tryLock on the same file (a different channel) then
      ;; conflicts, exactly as a second JVM would.
      (let [lockfile (io/file dir ".vaelii.lock")
            _        (io/make-parents lockfile)
            raf      (RandomAccessFile. lockfile "rw")
            ch       (.getChannel raf)
            other    (.tryLock ch)]
        (try
          (is (some? other) "the test itself took the lock")
          (testing "opening the disk KB fails fast rather than corrupting the logs"
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"locked by another JVM"
                                  (v/open-kb {:backend :disk :dir dir :recover? false}))))
          (finally
            (.release other)
            (.close ch)))))))

(deftest lock-releases-when-the-holder-goes-away
  (with-tmp
    (fn [dir]
      ;; after the stand-in lock is released, the KB opens cleanly
      (let [lockfile (io/file dir ".vaelii.lock")
            _        (io/make-parents lockfile)
            raf      (RandomAccessFile. lockfile "rw")
            ch       (.getChannel raf)
            other    (.tryLock ch)]
        (.release other)
        (.close ch))
      (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
        (is (lock/held? dir) "the KB now holds the lock")
        (v/assert kb '(genl dog animal) 'UniverseContext {:strength :monotonic})
        (is (v/genl? kb 'dog 'animal))))))

(deftest two-kbs-over-one-directory-share-the-durable-store
  (with-tmp
    (fn [dir]
      (let [kb1 (v/open-kb {:backend :disk :dir dir :recover? false})]
        (v/assert kb1 '(genl dog animal) 'UniverseContext {:strength :monotonic})
        (v/assert kb1 '(dog Muffet) 'UniverseContext {:strength :monotonic})
        (testing "a KB reopened over the same directory (a restart) starts with an empty
                 in-memory graph but the same durable records, and recover rebuilds it"
          (let [kb2 (v/open-kb {:backend :disk :dir dir :recover? false})]
            (is (not (v/isa? kb2 'Muffet 'animal)) "taxonomy not rebuilt yet")
            ;; the durable record is in the shared store — handle-of answers about
            ;; storage, not belief, so it is visible before recover (query is
            ;; belief-filtered by kb2's still-empty TMS, so it is not)
            (is (some? (v/handle-of kb2 '(dog Muffet) 'UniverseContext))
                "the durable record is visible at the storage layer")
            (is (empty? (v/sentexes-matching kb2 '(dog ?x) 'UniverseContext))
                "but not believed until recover rebuilds the TMS")
            (v/recover kb2)
            (is (v/isa? kb2 'Muffet 'animal) "recover rebuilt the taxonomy from the store")
            (is (seq (v/sentexes-matching kb2 '(dog ?x) 'UniverseContext)) "and belief with it")))))))

(deftest close-then-reopen-from-disk-survives
  (with-tmp
    (fn [dir]
      (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
        (v/assert kb '(genl dog animal) 'UniverseContext {:strength :monotonic})
        (v/assert kb '(dog Muffet) 'UniverseContext {:strength :monotonic}))
      ;; a genuine restart: fsync + close + release the lock + forget the stores, so the
      ;; reopen reads the durable logs from disk with fresh RAM state (not the shared
      ;; in-process registry the test above relies on)
      (backend/close-dir! dir)
      (is (not (lock/held? dir)) "the lock is released on close")
      (testing "a brand-new KB reads the durable store back from disk"
        (let [kb2 (v/open-kb {:backend :disk :dir dir :recover? false})]
          (is (some? (v/handle-of kb2 '(dog Muffet) 'UniverseContext)) "the record survived")
          (v/recover kb2)
          (is (v/isa? kb2 'Muffet 'animal) "and its taxonomy edge"))))))

(deftest public-close-releases-the-directory-and-a-reopen-recovers-by-default
  ;; the public pair end-to-end: `open-kb` threads the directory onto the KB's `:dir`,
  ;; and `close!` releases it through that slot.  Were the threading broken, close!
  ;; would silently no-op — so the pin is that the lock is genuinely gone and a fresh
  ;; open over the same directory reads the data back.
  (with-tmp
    (fn [dir]
      (tu/with-terms [dog animal Muffet]
        (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
          (v/assert kb (list 'genl dog animal) 'UniverseContext {:strength :monotonic})
          (v/assert kb (list dog Muffet) 'UniverseContext {:strength :monotonic})
          (is (identical? kb (v/close! kb)) "close! returns the KB"))
        (is (not (lock/held? dir)) "close! released the single-writer lock")
        (is (empty? (backend/opened dir)) "and forgot the directory's stores")
        (testing "the same JVM reopens the directory; :recover? defaults to :auto"
          (let [kb2 (v/open-kb {:backend :disk :dir dir})]
            (is (seq (v/sentexes-matching kb2 (list dog Muffet) 'UniverseContext))
                "the data is back and believed with no explicit recover call")
            (is (v/isa? kb2 Muffet animal))))))))

(deftest public-close-on-a-memory-kb-is-a-no-op
  ;; an in-memory KB has no `:dir`, so close! releases nothing and the KB stays
  ;; usable — the guarantee that makes an unconditional (close! kb) in a `finally`
  ;; safe.  Explicitly `:memory` rather than the suite backend: under a disk run the
  ;; scratch KB has a directory, and closing it would pull the store out from under
  ;; every later test.
  (let [kb (v/open-kb {:backend :memory :space ::noop-space :recover? false})]
    (tu/with-terms [dog Muffet Rex]
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (identical? kb (v/close! kb)) "close! returns the KB")
      (is (some? (v/handle-of kb (list dog Muffet) 'UniverseContext))
          "the store is untouched")
      (v/assert kb (list dog Rex) 'UniverseContext)
      (is (some? (v/handle-of kb (list dog Rex) 'UniverseContext))
          "and still writable")
      (tu/clear-kb! kb))))

(deftest close-dir-releases-the-lock-even-when-a-component-close-throws
  ;; a component close fsyncs and can compact, so it can throw (a full disk).  The
  ;; lock and the registry entry must go regardless: close! exists to hand the
  ;; directory to another process, and a throw that kept the lock would defeat exactly
  ;; that.  The first component failure resurfaces after the cleanup.
  (with-tmp
    (fn [dir]
      (tu/with-terms [dog Muffet]
        (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
          (v/assert kb (list dog Muffet) 'UniverseContext {:strength :monotonic}))
        ;; drs/close! is a plain fn called through its var, so with-redefs intercepts
        ;; (a protocol-method var would not)
        (with-redefs [drs/close! (fn [_] (throw (java.io.IOException. "disk full (simulated)")))]
          (is (thrown? java.io.IOException (backend/close-dir! dir))
              "the component failure reaches the caller"))
        (is (not (lock/held? dir)) "the lock is released despite the failed close")
        (is (empty? (backend/opened dir)) "and the registry entry is dropped")
        (testing "so a subsequent open of the same directory succeeds"
          (let [kb2 (v/open-kb {:backend :disk :dir dir :recover? false})]
            (is (some? (v/handle-of kb2 (list dog Muffet) 'UniverseContext))
                "the durable record reads back in the reopened store")))))))

(deftest distinct-directories-are-isolated
  (with-tmp
    (fn [dir1]
      (with-tmp
        (fn [dir2]
          (let [kb1 (v/open-kb {:backend :disk :dir dir1 :recover? false})
                kb2 (v/open-kb {:backend :disk :dir dir2 :recover? false})]
            (v/assert kb1 '(dog Muffet) 'UniverseContext {:strength :monotonic})
            (is (some? (v/handle-of kb1 '(dog Muffet) 'UniverseContext)))
            (is (nil? (v/handle-of kb2 '(dog Muffet) 'UniverseContext))
                "a second directory shares nothing with the first")))))))

(deftest reindex-rebuilds-index-from-records-on-disk
  (with-tmp
    (fn [dir]
      (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
        (v/assert kb '(genl dog animal) 'UniverseContext {:strength :monotonic})
        (v/assert kb '(dog Muffet) 'UniverseContext {:strength :monotonic})
        (v/assert-rule kb ['(dog ?x)] '(barks ?x) 'UniverseContext)
        (let [before {:dogs (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'UniverseContext)))
                      :isa  (v/isa? kb 'Muffet 'animal)
                      :term (count (v/find-sentexes kb 'Muffet))}]
          (v/reindex kb)                          ; wipe the index, rebuild from the records, recover
          (testing "every index read answers as it did before the rebuild"
            (is (= (:dogs before) (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'UniverseContext)))))
            (is (= (:isa before) (v/isa? kb 'Muffet 'animal)))
            (is (= (:term before) (count (v/find-sentexes kb 'Muffet))))))))))

(deftest disk-dir-derivation
  (is (= "/some/where" (backend/disk-dir {:dir "/some/where"}))
      ":dir names the directory outright")
  (testing "otherwise it derives a distinct directory from the space"
    (let [d (backend/disk-dir {:space 15})]
      (is (str/includes? d "space-15")))
    (is (not= (backend/disk-dir {:space 15})
              (backend/disk-dir {:space 13}))
        "different spaces derive different directories")))

(deftest a-short-index-log-is-detected-and-rebuilt
  ;; The two instruments beside the layout gate, each driven through the loss that
  ;; defeats the other.  A tail lost *with the clean marker in place* is a file that
  ;; is not the one that was closed — arbitrary keys of a compacted log, where the
  ;; root count and even the batch seal may survive — and the length disagreement is
  ;; what says so.  A tail lost *with no marker* (the crash shape) keeps each torn
  ;; batch's prefix, the root count included; the batch-seal counter is the last op
  ;; of every batch, so it is what the tear loses first.
  (letfn [(build! [dir]
            (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
              (dotimes [i 20]
                (v/assert kb (list 'tmpShortP (symbol (str "TmpShort" i))) 'UniverseContext))
              (v/close! kb)))
          (lop! [dir n]
            (let [f (RandomAccessFile. (str dir "/index/kv.log") "rw")]
              (.setLength f (- (.length f) (long n)))
              (.close f)))
          (reopened-finds-all? [dir]
            (let [kb2 (v/open-kb {:backend :disk :dir dir :recover? :auto})]
              (try
                (and (= 20 (count (v/sentexes-matching kb2 '(tmpShortP ?x) 'UniverseContext)))
                     (every? #(v/handle-of kb2 (list 'tmpShortP (symbol (str "TmpShort" %)))
                                           'UniverseContext)
                             (range 20)))
                (finally (v/close! kb2)))))]
    (testing "a log shorter than its clean marker recorded is rebuilt, whatever survives"
      (with-tmp (fn [dir]
                  (build! dir)
                  (lop! dir 64)
                  (is (reopened-finds-all? dir)))))
    (testing "a torn tail with no marker loses a batch seal, and the gate sees it"
      (with-tmp (fn [dir]
                  ;; the crash shape is an *append-mode* log — compaction runs on
                  ;; close, and a crashed process never closed — so build one:
                  ;; compaction off for the write, marker deleted for the crash
                  (System/setProperty "vaelii.disk.auto-compact" "off")
                  (try (build! dir)
                       (finally (System/clearProperty "vaelii.disk.auto-compact")))
                  (.delete (java.io.File. (str dir "/index/clean.nippy")))
                  (lop! dir 64)
                  (is (reopened-finds-all? dir)))))))
