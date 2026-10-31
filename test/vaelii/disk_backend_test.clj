;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-backend-test
  "The durable backend wiring: the single-writer lock fails a second opener fast, and
  two KBs over one directory in a process share the durable stores (the restart
  contract the recovery tests rely on)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.lock :as lock]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu])
  (:import [java.io RandomAccessFile]
           [java.lang.ref WeakReference]
           [java.util.concurrent CountDownLatch Executors ScheduledExecutorService
            TimeUnit]))

(defn- with-tmp
  "Run `(f dir)` in a fresh temp directory, closing any disk stores opened on it (so
  the durability daemon doesn't outlive the dir) and deleting it afterwards."
  [f]
  (let [dir (tu/tmpdir "vaelii-disk-be-")]
    (try (f dir)
         (finally (backend/close-dir! dir) (tu/rm-rf! dir)))))

(deftest an-overlapping-lock-in-this-process-is-diagnosed-as-ours
  ;; `tryLock` **throws** `OverlappingFileLockException` rather than returning nil when
  ;; the lock is already held by the calling JVM, so this branch says nothing at all about
  ;; another process — and the holder tag written in the file is then ours.  Reported as
  ;; "locked by another JVM" it sent an operator looking for a process that does not
  ;; exist, and the holder read off the file named this JVM's own pid as the intruder.
  (with-tmp
    (fn [dir]
      (let [lockfile (io/file dir ".vaelii.lock")
            _        (io/make-parents lockfile)
            raf      (RandomAccessFile. lockfile "rw")
            ch       (.getChannel raf)
            other    (.tryLock ch)]
        (try
          (is (some? other) "the test itself took the lock, through another channel")
          (testing "opening the disk KB fails fast rather than corrupting the logs"
            (let [e (try (v/open-kb {:backend :disk-log :dir dir :recover? false})
                         nil
                         (catch clojure.lang.ExceptionInfo t t))]
              (is (some? e) "the open is refused")
              (is (re-find #"already locked by this JVM" (ex-message e))
                  (str "the diagnosis names this process: " (ex-message e)))
              (is (= :disk-locked (:type (ex-data e))))
              (is (true? (:same-jvm? (ex-data e))))
              (is (re-find (re-pattern (str (.pid (java.lang.ProcessHandle/current))))
                           (str (:holder (ex-data e))))
                  "and the holder it reports is us, not whatever the file happens to say")))
          (finally
            (.release other)
            (.close ch)))))))

(deftest the-other-process-branch-still-names-another-jvm
  ;; The branch a `tryLock` that *returns nil* takes — a lock a different process holds,
  ;; which no single-JVM test can stage.  Its message is asserted here so splitting the two
  ;; diagnoses did not leave the real cross-process one saying nothing useful.
  (let [msg (#'lock/conflict-message "/some/kb" "4321@host since 2026-01-01T00:00:00Z")]
    (is (re-find #"locked by another JVM" msg))
    (is (re-find #"4321@host" msg) "with the holder tag read off the lock file")))

(defn- canon
  "`f`'s canonical path — the spelling the open keys a directory by, and so the one its
  refusals name (`/tmp` reads `/private/tmp` on macOS)."
  [f] (.getCanonicalPath (io/file f)))

(defn- open-refusal
  "The `ex-info` opening a `:disk-log` KB over `dir` throws, or nil."
  [dir]
  (try (v/close! (v/open-kb {:backend :disk-log :dir dir :recover? false})) nil
       (catch clojure.lang.ExceptionInfo e e)))

(deftest a-directory-that-cannot-hold-the-lock-is-named-rather-than-its-lock-file
  ;; The lock file is the first thing an open writes, and java.io's refusal names it:
  ;; `/tmp/kb/.vaelii.lock (Permission denied)`, `(Not a directory)` — a file the caller
  ;; never heard of, where the directory they named is what needs changing.
  (with-tmp
    (fn [root]
      (let [file (io/file root "kb-is-a-file")]
        (spit file "not a directory")
        (testing "a --dir that is a regular file"
          (let [e (open-refusal (str file))]
            (is (= :not-a-directory (:type (ex-data e))))
            (is (= (canon file) (:dir (ex-data e))) "naming the directory, not the lock file")
            (is (str/includes? (ex-message e) (str (canon file) " is a file, not a directory"))
                (ex-message e))
            (is (not (str/includes? (ex-message e) ".vaelii.lock (")))))
        (testing "a --dir under a regular file"
          (let [e (open-refusal (str (io/file file "kb")))]
            (is (= :not-a-directory (:type (ex-data e))))
            (is (= (canon file) (:file (ex-data e))) "naming the file in the way"))))
      (let [ro (io/file root "kb-readonly")]
        (.mkdirs ro)
        (.setWritable ro false)
        (try
          ;; a process that writes regardless of the mode (root) has nothing to refuse
          (when-not (.canWrite ro)
            (testing "a directory this process cannot write"
              (let [e (open-refusal (str ro))]
                (is (= :not-writable (:type (ex-data e))))
                (is (= (canon ro) (:dir (ex-data e))))
                (is (str/includes? (ex-message e) (str "Disk KB at " (canon ro) " cannot be opened"))
                    (ex-message e))
                (is (str/includes? (ex-message e) "reads included")
                    "saying why a read needs write access too"))))
          (finally (.setWritable ro true)))))))

(deftest a-lock-toggled-off-after-the-acquire-is-still-released
  ;; `vaelii.disk.lock` can be flipped at runtime, and it is read at acquire time only.
  ;; A `release!` that consulted it instead would return without releasing while the map
  ;; said the directory was free — an OS lock held for the life of the JVM, which is
  ;; precisely the state the single-writer contract exists to keep out of.
  (with-tmp
    (fn [dir]
      (is (= :acquired (lock/acquire! dir)))
      (is (lock/held? dir))
      (let [prior (System/getProperty "vaelii.disk.lock")]
        (System/setProperty "vaelii.disk.lock" "false")
        (try (lock/release! dir)
             (finally (if prior (System/setProperty "vaelii.disk.lock" prior)
                          (System/clearProperty "vaelii.disk.lock")))))
      (is (not (lock/held? dir)) "the entry went with the release")
      (is (= :acquired (lock/acquire! dir)) "and the OS lock was really given back")
      (lock/release! dir))))

(deftest a-release-that-fails-keeps-the-directory-marked-held
  ;; Dropping the entry anyway said the directory was free while this JVM still held its
  ;; descriptor and its OS lock: the next `acquire!` here would take neither, hand the
  ;; directory to a second writer, and report whatever holder tag the *file* carried.
  ;; The entry stays, and re-acquisition is refused by name.
  (with-tmp
    (fn [dir]
      (let [path (lock/canonical-dir dir)]
        (is (= :acquired (lock/acquire! dir)))
        ;; close the channel out from under the entry, so `.release` throws
        (.close ^java.nio.channels.FileChannel (:channel (get @@#'lock/held path)))
        (lock/release! dir)
        (is (lock/held? dir) "a failed release keeps the entry")
        (let [e (try (lock/acquire! dir) nil (catch clojure.lang.ExceptionInfo t t))]
          (is (some? e) "and re-acquisition is refused")
          (is (= :unreleased (:type (ex-data e))))
          (is (re-find #"cannot be locked" (ex-message e)))
          (is (re-find (re-pattern (str (.pid (java.lang.ProcessHandle/current))))
                       (ex-message e))
              "naming this JVM as the holder rather than the file's tag"))
        ;; the directory is this test's, and nothing else may inherit its stuck entry
        (swap! @#'lock/held dissoc path)))))

(deftest a-holder-tag-write-that-throws-releases-the-lock-it-took-or-says-why-not
  ;; The holder tag is written after the OS lock is taken.  Unwinding that lock inside two
  ;; empty catches dropped a failed release on the floor: the map said the directory was
  ;; free while this JVM could still hold its OS lock, and the next open's refusal blamed a
  ;; channel "this namespace does not hold".  The staged failure closes the channel, so
  ;; the release throws, as in the test above.
  (with-tmp
    (fn [dir]
      (let [path   (lock/canonical-dir dir)
            logged (atom [])
            thrown (with-redefs [lock/write-holder!
                                 (fn [^java.nio.channels.FileChannel ch _]
                                   (.close ch)
                                   (throw (java.io.IOException. "injected: disk full")))]
                     (binding [trove/*log-fn* (fn [_ns _coords level id _payload]
                                                (when (= :error level) (swap! logged conj id)))]
                       (try (lock/acquire! dir) nil
                            (catch java.io.IOException e (ex-message e)))))
            again  (try (lock/acquire! dir) (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= "injected: disk full" thrown) "the write's own failure reaches the caller")
        (is (some #{::lock/unreleased} @logged) "the failed release is logged")
        (is (= :unreleased (:type again))
            "and the directory is refused by name, not handed out or blamed on another channel")
        (swap! @#'lock/held dissoc path)))))

(deftest a-lock-request-the-filesystem-answers-with-an-io-error-is-refused-as-unsupported
  (doseq [[reason override?] [["Function not implemented" true] ["Input/output error" false]]]
    (with-tmp
      (fn [dir]
        (let [e (with-redefs [lock/try-lock (fn [_] (throw (java.io.IOException. ^String reason)))]
                  (try (lock/acquire! dir) nil (catch clojure.lang.ExceptionInfo t t)))]
          (is (= {:type :lock-unsupported :dir (lock/canonical-dir dir) :reason reason}
                 (ex-data e)))
          (is (= override? (str/includes? (ex-message e) "vaelii.disk.lock=false"))
              (str "the override is offered for a filesystem with no advisory locks alone: " reason))
          (is (not (lock/held? dir)))
          (is (= :acquired (lock/acquire! dir)) "the refused request leaves the lock file free")
          (lock/release! dir))))))

(deftest the-holder-tag-names-the-host-hostname-sets
  (is (= "seat-a" (#'lock/host-name {"HOSTNAME" " seat-a\n"})))
  (is (seq (#'lock/host-name {})) "an unset HOSTNAME takes the resolver's name"))

;; ---- the durability daemon's process-wide lifecycle ---------------------

(deftest the-durability-singletons-are-installed-under-one-monitor
  ;; Two `register!`s racing the first one each built a ticker over the one registry:
  ;; every registrant fsynced twice a tick, and only one of the two reachable by `stop!`
  ;; (the loser tickes on for the life of the process).  Holding the lifecycle monitor is
  ;; the direct test that the create is inside it — a registration that has to build the
  ;; scheduler waits rather than building a second one.
  (let [prior @@#'dur/scheduler]
    (dur/stop!)
    (when prior
      (.awaitTermination ^ScheduledExecutorService prior 5 TimeUnit/SECONDS))
    (let [started (CountDownLatch. 1)
          done    (CountDownLatch. 1)
          id      (atom nil)
          body    (fn []
                    (.countDown started)
                    (reset! id (dur/register! {:fsync (fn [_] nil)
                                               :close (fn [] nil)
                                               :label "lifecycle-test"}))
                    (.countDown done))
          t       (Thread. ^Runnable body "lifecycle-test-registrant")]
      (try
        (locking @#'dur/lifecycle
          (.start t)
          (.await started)
          (is (not (.await done 500 TimeUnit/MILLISECONDS))
              "a registration that must install the scheduler waits on the monitor"))
        (is (.await done 5000 TimeUnit/MILLISECONDS) "and finishes once it is released")
        (is (some? @@#'dur/scheduler) "with a scheduler installed")
        (finally
          (dur/deregister! @id)
          (.join t 5000))))))

(deftest a-registrant-the-daemon-could-not-act-on-is-refused-at-the-register
  ;; The registry is read at fsync tick and at shutdown, and nothing there can ask a
  ;; registrant for a piece it never carried: a missing `:close` would be a backend the
  ;; shutdown hook silently skips, which is the whole of what this namespace does for it.
  ;; The `:phase` arm is the same argument about ordering — a phase nothing sorts by would
  ;; close in a position nobody chose.  Refused at the register, where the caller who wrote
  ;; the map is still on the stack, and refused as data rather than as an `assert`, which
  ;; `*assert*` may elide.
  (let [whole {:fsync (fn [_] nil) :close (fn [] nil) :label "registrant-test"}
        refused (fn [entry] (try (dur/register! entry)
                                 nil
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (doseq [[k entry] [[:fsync (dissoc whole :fsync)]
                       [:close (assoc whole :close "not a fn")]
                       [:label (assoc whole :label :registrant-test)]
                       [:phase (assoc whole :phase :whenever)]]]
      (testing (str "a registrant whose " k " the daemon cannot use")
        (let [d (refused entry)]
          (is (= :bad-registrant (:type d)))
          (is (= k (:key d)) "naming the key that was wrong")
          (is (= (get entry k) (:value d)) "and what it held"))))))

(deftest a-refused-auto-compaction-submit-clears-the-in-flight-mark
  ;; The id goes in flight **before** the submit, so a tick three seconds later cannot
  ;; queue a second rewrite of a backend whose first has not started.  That makes the
  ;; refused submit the case to handle: the task never runs, its `finally` never clears
  ;; the id, and `maybe-compact!` skips a backend that is in flight — so one rejected
  ;; submit barred that backend from auto-compaction for the life of the process.
  (let [prior @@#'dur/compaction-executor
        dead  (doto (Executors/newSingleThreadExecutor) (.shutdown))]
    (try
      (reset! @#'dur/compaction-executor dead)
      (#'dur/submit-compaction! ::probe "a-refused-submit" (fn [] nil) 0.9 0.5)
      (is (not (contains? @@#'dur/compaction-in-flight ::probe))
          "a rejected submit leaves nothing behind to bar the next tick")
      (finally (reset! @#'dur/compaction-executor prior)))))

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
      (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
        (is (lock/held? dir) "the KB now holds the lock")
        (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
        (is (v/genl? kb 'dog 'animal))))))

(deftest two-kbs-over-one-directory-share-the-durable-store
  (with-tmp
    (fn [dir]
      (let [kb1 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
        (v/assert kb1 '(genl dog animal) 'CxUniverse {:strength :monotonic})
        (v/assert kb1 '(dog Muffet) 'CxUniverse {:strength :monotonic})
        (testing "a KB reopened over the same directory (a restart) starts with an empty
                 in-memory graph but the same durable records, and recover rebuilds it"
          (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
            (is (not (v/isa? kb2 'Muffet 'animal)) "taxonomy not rebuilt yet")
            ;; the durable record is in the shared store — handle-of answers about
            ;; storage, not belief, so it is visible before recover (query is
            ;; belief-filtered by kb2's still-empty TMS, so it is not)
            (is (some? (v/handle-of kb2 '(dog Muffet) 'CxUniverse))
                "the durable record is visible at the storage layer")
            (is (empty? (v/sentexes-matching kb2 '(dog ?x) 'CxUniverse))
                "but not believed until recover rebuilds the TMS")
            (v/recover kb2)
            (is (v/isa? kb2 'Muffet 'animal) "recover rebuilt the taxonomy from the store")
            (is (seq (v/sentexes-matching kb2 '(dog ?x) 'CxUniverse)) "and belief with it")))))))

(deftest close-then-reopen-from-disk-survives
  (with-tmp
    (fn [dir]
      (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
        (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
        (v/assert kb '(dog Muffet) 'CxUniverse {:strength :monotonic}))
      ;; a genuine restart: fsync + close + release the lock + forget the stores, so the
      ;; reopen reads the durable logs from disk with fresh RAM state (not the shared
      ;; in-process registry the test above relies on)
      (backend/close-dir! dir)
      (is (not (lock/held? dir)) "the lock is released on close")
      (testing "a brand-new KB reads the durable store back from disk"
        (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          (is (some? (v/handle-of kb2 '(dog Muffet) 'CxUniverse)) "the record survived")
          (v/recover kb2)
          (is (v/isa? kb2 'Muffet 'animal) "and its taxonomy edge"))))))

(defn- derived-index-held?
  "Does one of the three RAM index backends hold a derived index under `space`?"
  [space]
  (boolean (some #(contains? @@% space)
                 [#'mem/index-spaces #'dense/index-spaces #'columnar/state-spaces])))

(deftest close-releases-the-derived-index-a-directory-held
  ;; A disk-backed KB with a RAM index keeps that index in a process-wide registry keyed
  ;; by its directory, so a process opening KBs in a loop keeps one per directory that
  ;; `close!` does not drop.
  (doseq [backend [:disk-memory :disk-dense :disk-columnar]]
    (with-tmp
      (fn [dir]
        (let [kb (v/open-kb {:backend backend :dir dir :recover? false})]
          (v/assert kb '(tmp_derived_p TmpDerived) 'CxUniverse)
          (let [space (:index-space kb)
                held? (derived-index-held? space)]
            (v/close! kb)
            (is (= [true false] [held? (derived-index-held? space)])
                (str backend ": the open holds a derived index, and close! drops it"))))))))

(deftest public-close-releases-the-directory-and-a-reopen-recovers-by-default
  ;; the public pair end-to-end: `open-kb` threads the directory onto the KB's `:dir`,
  ;; and `close!` releases it through that slot.  Were the threading broken, close!
  ;; would silently no-op — so the assertion is that the lock is genuinely gone and a fresh
  ;; open over the same directory reads the data back.
  (with-tmp
    (fn [dir]
      (tu/with-terms [dog animal Muffet]
        (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          (v/assert kb (list 'genl dog animal) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list dog Muffet) 'CxUniverse {:strength :monotonic})
          (is (identical? kb (v/close! kb)) "close! returns the KB"))
        (is (not (lock/held? dir)) "close! released the single-writer lock")
        (is (empty? (backend/opened dir)) "and forgot the directory's stores")
        (testing "the same JVM reopens the directory; :recover? defaults to :auto"
          (let [kb2 (v/open-kb {:backend :disk-log :dir dir})]
            (is (seq (v/sentexes-matching kb2 (list dog Muffet) 'CxUniverse))
                "the data is back and believed with no explicit recover call")
            (is (v/isa? kb2 Muffet animal))))))))

;; Built in a fn of its own, so no local of the test body holds the KB.
(defn- closed-kb-refs
  "Weak references to a `:disk-snapshot` KB over `dir`, its records, its index and its
  reasoning, taken after two writes and before its close."
  [dir]
  (let [kb (v/open-kb {:backend :disk-snapshot :dir dir})]
    (v/assert kb '(dog Fido) 'CxUniverse {:strength :default})
    (v/assert kb '(genl dog animal) 'CxUniverse {:strength :default})
    (let [refs (mapv #(WeakReference. %) [kb (:records kb) (:index kb) (:reasoning kb)])]
      (v/close! kb)
      refs)))

(deftest a-closed-kb-is-collectable-once-its-caller-drops-it
  (tu/with-snapshot-platform
    ;; A process that opens and closes large KBs in turn needs the heap of the one it closed.
    (with-tmp
      (fn [dir]
        (let [refs (closed-kb-refs dir)
              held #(mapv (fn [^WeakReference r] (some? (.get r))) refs)]
          (is (= [false false false false]
                 (loop [i 0]
                   (System/gc)
                   (let [h (held)]
                     (if (or (not-any? true? h) (= i 20)) h (do (Thread/sleep 50) (recur (inc i)))))))))))))

(deftest public-close-on-a-memory-kb-is-a-no-op
  ;; an in-memory KB has no `:dir`, so close! releases nothing and the KB stays
  ;; usable — the guarantee that makes an unconditional (close! kb) in a `finally`
  ;; safe.  Explicitly `:memory` rather than the suite backend: under a disk run the
  ;; scratch KB has a directory, and closing it would pull the store out from under
  ;; every later test.
  (let [kb (v/open-kb {:backend :memory :space ::noop-space :recover? false})]
    (tu/with-terms [dog Muffet Rex]
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (identical? kb (v/close! kb)) "close! returns the KB")
      (is (some? (v/handle-of kb (list dog Muffet) 'CxUniverse))
          "the store is untouched")
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (some? (v/handle-of kb (list dog Rex) 'CxUniverse))
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
        (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          (v/assert kb (list dog Muffet) 'CxUniverse {:strength :monotonic}))
        ;; drs/close! is a plain fn called through its var, so with-redefs intercepts
        ;; (a protocol-method var would not)
        (with-redefs [drs/close! (fn [_] (throw (java.io.IOException. "disk full (simulated)")))]
          (is (thrown? java.io.IOException (backend/close-dir! dir))
              "the component failure reaches the caller"))
        (is (not (lock/held? dir)) "the lock is released despite the failed close")
        (is (empty? (backend/opened dir)) "and the registry entry is dropped")
        (testing "so a subsequent open of the same directory succeeds"
          (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
            (is (some? (v/handle-of kb2 (list dog Muffet) 'CxUniverse))
                "the durable record reads back in the reopened store")))))))

(deftest distinct-directories-are-isolated
  (with-tmp
    (fn [dir1]
      (with-tmp
        (fn [dir2]
          (let [kb1 (v/open-kb {:backend :disk-log :dir dir1 :recover? false})
                kb2 (v/open-kb {:backend :disk-log :dir dir2 :recover? false})]
            (v/assert kb1 '(dog Muffet) 'CxUniverse {:strength :monotonic})
            (is (some? (v/handle-of kb1 '(dog Muffet) 'CxUniverse)))
            (is (nil? (v/handle-of kb2 '(dog Muffet) 'CxUniverse))
                "a second directory shares nothing with the first")))))))

(deftest reindex-rebuilds-index-from-records-on-disk
  (with-tmp
    (fn [dir]
      (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
        (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
        (v/assert kb '(dog Muffet) 'CxUniverse {:strength :monotonic})
        (v/assert-rule kb ['(dog ?x)] '(barks ?x) 'CxUniverse)
        (let [before {:dogs (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'CxUniverse)))
                      :isa  (v/isa? kb 'Muffet 'animal)
                      :term (count (v/find-sentexes kb 'Muffet))}]
          (v/reindex kb)                          ; wipe the index, rebuild from the records, recover
          (testing "every index read answers as it did before the rebuild"
            (is (= (:dogs before) (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'CxUniverse)))))
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
        "different spaces derive different directories"))
  (testing "a blank vaelii.disk.dir is unset, not a base at the filesystem root"
    (let [prior (System/getProperty "vaelii.disk.dir")]
      (try
        (doseq [blank ["" "  "]]
          (System/setProperty "vaelii.disk.dir" blank)
          (is (= (str (System/getProperty "java.io.tmpdir") "/vaelii-disk/space-15")
                 (backend/disk-dir {:space 15}))))
        (finally (if prior (System/setProperty "vaelii.disk.dir" prior)
                     (System/clearProperty "vaelii.disk.dir")))))))

(deftest store-backend-names-a-store-an-adapter-wrote
  ;; `lein serve <dir>` and `lein cli --dir <dir>` open what `store-backend` names, and a
  ;; `:disk-log` store when it names nothing.  A directory an adapter wrote holds a store,
  ;; so reading it as empty put a second, empty store beside it: the daemon served nothing
  ;; over an `:sqlite` file, and rebuilt a `:pg-disk-log` index from zero records in place.
  (let [root (io/file (System/getProperty "java.io.tmpdir") (str "store-backend-" (System/nanoTime)))
        dir  (fn [nm & files]
               (let [d (io/file root nm)]
                 (doseq [f files] (io/make-parents (io/file d f)) (spit (io/file d f) ""))
                 (str d)))]
    (is (= :sqlite (backend/store-backend (dir "sqlite" "records.sqlite"))))
    (is (= :pg-disk-log (backend/store-backend (dir "pg" "index/kv.log"))))
    (is (= :disk-log (backend/store-backend (dir "log" "records/format.edn" "index/kv.log"))))
    (is (= :disk-columnar (backend/store-backend (dir "col" "records/format.edn"))))
    (is (nil? (backend/store-backend (dir "empty"))))
    (testing "the pg index is refused for want of its server, not opened as a local store"
      (is (= :missing-companion
             (:mismatch (try (v/open-kb {:backend (backend/store-backend (dir "pg2" "index/kv.log"))
                                         :dir (str (io/file root "pg2"))})
                             nil
                             (catch clojure.lang.ExceptionInfo e (ex-data e)))))))))

(deftest a-reopen-under-another-reasoner-set-is-refused
  ;; Two seats over the same records reach different beliefs when one registers `:allen`
  ;; and the other does not: the one without it finds `(before A C)` underivable.
  (with-tmp
    (fn [dir]
      (tu/with-terms [EarlyEvent MidEvent LateEvent]
        (let [opts {:backend :disk-log :dir dir}
              late (list 'before EarlyEvent LateEvent)
              open (fn [o] (try (v/open-kb (merge opts o))
                                (catch clojure.lang.ExceptionInfo e (ex-data e))))]
          (let [kb (v/open-kb opts)]
            (v/add-reasoner kb :allen)
            (v/assert kb (list 'before EarlyEvent MidEvent) 'CxUniverse)
            (v/assert kb (list 'before MidEvent LateEvent) 'CxUniverse)
            (v/close! kb))
          (testing "an open naming no reasoner is refused, naming both sets"
            (let [d (open {})]
              (is (= :reasoner-mismatch (:type d)))
              (is (= [:allen] (:stored d)))
              (is (= [] (:requested d)))
              (is (not (lock/held? dir)) "and the refused open released the lock")))
          (testing "an open naming another set is refused"
            (is (= :reasoner-mismatch (:type (open {:reasoners [:allen :rcc8]})))))
          (testing "an open naming the recorded set registers it"
            (let [kb (open {:reasoners [:allen]})]
              (is (v/ask? kb late 'CxUniverse))
              (v/close! kb)))
          (testing ":reasoners :stored registers the recorded set"
            (let [kb (open {:reasoners :stored})]
              (is (v/ask? kb late 'CxUniverse))
              (v/close! kb))))))))

(deftest a-durable-index-built-against-other-records-is-refused
  ;; A `:disk-log` index over records on a server is a directory and a database joined by
  ;; nothing but one opts map, so the directory records the database it describes
  ;; and a later open naming a different one is refused.  The coverage check beside it
  ;; cannot stand in: that compares record *counts*, and two unrelated stores of the same
  ;; size agree — after which handles resolve to another store's sentences and a re-assert
  ;; mints a second handle for one already stored.
  ;;
  ;; The `:pg` store is the sibling adapter's and is resolved lazily; a RAM store stands
  ;; in at that one call, because the identity check reads the records-identity file and
  ;; the `:pg` opts and never the store.
  (let [records (mem/memory-record-store {:space [::pg-stand-in]})
        opened  (fn [dir url]
                  (with-redefs-fn {#'kb/adapter-ctor (fn [_records] (fn [_spec] records))}
                    (fn []
                      (try (v/open-kb {:records :pg :index :disk-log :dir dir
                                       :pg url :recover? false})
                           :opened
                           (catch clojure.lang.ExceptionInfo e (ex-data e))))))]
    (try
      (with-tmp
        (fn [dir]
          (is (= :opened (opened dir "jdbc:postgresql://localhost/one"))
              "the first open writes the records identity rather than refusing the directory")
          (backend/close-dir! dir)
          (testing "the same database reopens — the records identity names a store and seals nothing"
            (is (= :opened (opened dir "jdbc:postgresql://localhost/one")))
            (backend/close-dir! dir))
          (testing "and another database over that index is refused by name"
            (let [d (opened dir "jdbc:postgresql://localhost/two")]
              (is (= :stale-index-records (:type d)))
              (is (not (lock/held? dir)) "and the refused open released the lock it took")
              (is (= ["localhost" 5432 "one" nil] (:recorded d))
                  "naming the store the index was built against")
              (is (= ["localhost" 5432 "two" nil] (:records d))
                  "and the one this KB brought")
              (is (str/includes? (str (:dir d)) dir) "and the directory to give its own")))))
      (finally (p/clear-records! records)))))

(deftest a-short-index-log-is-detected-and-rebuilt
  ;; The two instruments beside the layout check, each driven through the loss that
  ;; defeats the other.  A tail lost *with the clean marker in place* is a file that
  ;; is not the one that was closed — arbitrary keys of a compacted log, where the
  ;; root count and even the batch seal may survive — and the length disagreement is
  ;; what says so.  A tail lost *with no marker* (the crash shape) keeps each torn
  ;; batch's prefix, the root count included; the batch-seal counter is the last op
  ;; of every batch, so it is what the tear loses first.
  (letfn [(build! [dir]
            (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
              (dotimes [i 20]
                (v/assert kb (list 'tmp_short_p (symbol (str "TmpShort" i))) 'CxUniverse))
              (v/close! kb)))
          (lop! [dir n]
            (let [f (RandomAccessFile. (str dir "/index/kv.log") "rw")]
              (.setLength f (- (.length f) (long n)))
              (.close f)))
          (last-frame-offset [path]
            (with-open [raf (RandomAccessFile. ^String path "r")]
              (let [len (.length raf)]
                (loop [pos 0 last-pos 0]
                  (if (> (+ pos 4) len)
                    last-pos
                    (do (.seek raf pos)
                        (let [n (.readInt raf)]
                          (if (or (<= n 0) (> (+ pos 4 n) len))
                            last-pos
                            (recur (+ pos 4 n) pos)))))))))
          (cut-to! [path new-len]
            (with-open [raf (RandomAccessFile. ^String path "rw")] (.setLength raf (long new-len))))
          (build-uncompacted! [dir]
            ;; the crash shape is an *append-mode* log — compaction runs on close, and a
            ;; crashed process never closed — so build one: compaction off for the write,
            ;; markers deleted for the crash
            (let [prior (System/getProperty "vaelii.disk.auto-compact")]
              (System/setProperty "vaelii.disk.auto-compact" "off")
              (try (build! dir)
                   (finally (if prior (System/setProperty "vaelii.disk.auto-compact" prior)
                                (System/clearProperty "vaelii.disk.auto-compact")))))
            (.delete (java.io.File. (str dir "/index/clean.nippy")))
            (.delete (java.io.File. (str dir "/records/clean.nippy"))))
          (reopened-finds-all? [dir]
            (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? :auto})]
              (try
                (and (= 20 (count (v/sentexes-matching kb2 '(tmp_short_p ?x) 'CxUniverse)))
                     (every? #(v/handle-of kb2 (list 'tmp_short_p (symbol (str "TmpShort" %)))
                                           'CxUniverse)
                             (range 20)))
                (finally (v/close! kb2)))))]
    (testing "a log shorter than its clean marker recorded is rebuilt, whatever survives"
      (with-tmp (fn [dir]
                  (build! dir)
                  (lop! dir 64)
                  (is (reopened-finds-all? dir)))))
    (testing "a torn tail with no marker loses a batch seal, and the open detects it"
      (with-tmp (fn [dir]
                  (build-uncompacted! dir)
                  (lop! dir 64)
                  (is (reopened-finds-all? dir)))))
    (testing "the last record lost with a prefix of its index batch kept: the seal and the record count agree, the root count is one ahead, and the open rebuilds"
      (with-tmp (fn [dir]
                  (build-uncompacted! dir)
                  (let [sl (str dir "/records/sentexes.log")
                        si (str dir "/records/sentexes.idx")
                        kl (str dir "/index/kv.log")]
                    (cut-to! sl (last-frame-offset sl))
                    (cut-to! si (- (.length (java.io.File. si)) 24))
                    (cut-to! kl (last-frame-offset kl)))
                  (let [lost (list 'tmp_short_p 'TmpShort19)
                        kb2  (v/open-kb {:backend :disk-log :dir dir :recover? :auto})]
                    (try
                      (is (nil? (v/handle-of kb2 lost 'CxUniverse)) "no posting names the lost record")
                      (is (= 19 (count (v/sentexes-matching kb2 '(tmp_short_p ?x) 'CxUniverse))))
                      (v/assert kb2 lost 'CxUniverse)
                      (is (v/ask? kb2 lost 'CxUniverse) "the lost fact is stored again and read")
                      (is (= 20 (count (v/sentexes-matching kb2 '(tmp_short_p ?x) 'CxUniverse))))
                      (finally (v/close! kb2)))))))))

;; ---- the close hands the directory over, and waits until it can -------------

(defn- records-dur-id
  "The durability registrant id of `dir`'s record store — the id the compaction executor
  keys an in-flight rewrite of those logs by."
  [dir]
  (get-in @@#'backend/stores [(backend/canonical-dir dir) :dur-ids :records]))

(defn- compact-fn-of
  "The `:compact` thunk the record store registered — the very thunk the daemon's tick
  would call, so the test drives the real rewrite rather than a stand-in."
  [id]
  (:compact (get @@#'dur/registry id)))

(deftest close-dir-waits-for-a-running-compaction-before-releasing-the-lock
  ;; The record store's rewrite phase runs **without** the kind lock, by design: an
  ;; O(bytes) copy that stalled reads and writes would be worse than the dead frames it
  ;; reclaims.  What that costs is that a `close!` blocks on nothing the rewrite holds —
  ;; it read through a private handle and appended to `sentexes.log.compact` by name.
  ;; Releasing the directory's OS lock there hands `D` to a second process while this one
  ;; is still writing `D`'s temp files, and the second process's own compaction opens the
  ;; same paths: two rewrites appending to one temp log, one commit marker, and a replay
  ;; that installs frames from both with each one's slot offsets pointing into the
  ;; other's bytes.  Auto-compaction is on by default, so this is the default
  ;; configuration.
  ;;
  ;; The barrier is what makes it a test rather than a coin flip: a rewrite of a
  ;; test-sized log is over in microseconds, so the race window has to be held open at the
  ;; exact point rather than slept at.
  (with-tmp
    (fn [dir]
      (tu/with-terms [dog Muffet]
        (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          ;; something for the rewrite to copy, and a dead frame or two behind it
          (dotimes [i 40]
            (v/assert kb (list dog (symbol (str Muffet i))) 'CxUniverse
                      {:strength :monotonic}))
          (doseq [i (range 0 40 2)]
            (v/retract! kb (v/handle-of kb (list dog (symbol (str Muffet i))) 'CxUniverse)))
          (let [id      (records-dur-id dir)
                compact (compact-fn-of id)
                entered (promise)
                release (promise)]
            (is (some? compact) "the record store registered a compaction thunk")
            (reset! drs/rewrite-barrier (fn [_] (deliver entered true) @release))
            (try
              (#'dur/submit-compaction! id "close-handshake-probe" compact 0.9 0.5)
              (is (= true (deref entered 10000 nil))
                  "the rewrite is open, past its snapshot and before its reconcile")
              (let [closed (future (backend/close-dir! dir))]
                (is (= :running (deref closed 400 :running))
                    "the close does not return while that rewrite is still in flight")
                (is (lock/held? dir)
                    "and the lock the other process is waiting on is still ours")
                (deliver release true)
                (is (not= :timeout (deref closed 20000 :timeout))
                    "and it returns once the compactor goes quiet")
                (is (not (lock/held? dir)) "having released the lock last"))
              (finally
                (reset! drs/rewrite-barrier nil)
                (deliver release true))))
          (testing "the abandoned rewrite left no temp behind for the next owner to trip on"
            (is (empty? (filter #(str/includes? (.getName ^java.io.File %) ".compact")
                                (file-seq (io/file dir))))
                "no .compact temp or commit marker survives the close"))
          (testing "and the originals still hold every record"
            (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
              (try
                (is (= 20 (count (filter #(v/handle-of kb2 (list dog (symbol (str Muffet %)))
                                                       'CxUniverse)
                                         (range 40))))
                    "the twenty that were not retracted read back")
                (finally (v/close! kb2))))))))))

(deftest a-submit-that-loses-the-race-with-stop-builds-no-second-executor
  ;; `stop!` shuts `@compaction-executor` and nils it under `lifecycle`.  A tick already
  ;; inside `submit-compaction!` then read that nil, took `lifecycle` after `stop!` had
  ;; let it go, and built a **new** single-thread executor — one no var points at, so
  ;; `stop!` returned having stopped nothing, and the replacement lived to JVM exit.
  ;; Daemon threads, so nothing hangs; the contract is what was false.
  (let [prior @@#'dur/scheduler]
    (dur/stop!)
    (when prior (.awaitTermination ^ScheduledExecutorService prior 5 TimeUnit/SECONDS))
    (try
      (is (nil? @@#'dur/compaction-executor) "stop! left no executor")
      (#'dur/submit-compaction! ::post-stop "post-stop-probe"
                                (fn [] (throw (AssertionError. "a stopped compactor ran")))
                                0.9 0.5)
      (is (nil? @@#'dur/compaction-executor)
          "a submit after stop! skips rather than building a replacement")
      (is (not (contains? @@#'dur/compaction-in-flight ::post-stop))
          "and strands no in-flight id, which would bar that backend for the process")
      (finally
        ;; a registration is what un-stops it, which is also what the next open does
        (dur/deregister! (dur/register! {:fsync (fn [_] nil)
                                         :close (fn [] nil)
                                         :label "post-stop-restart"}))))
    (is (false? @@#'dur/compaction-stopped) "and a register! puts the compactor back")))
