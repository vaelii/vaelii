;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-kv-test
  "The on-disk `KvBackend` adapter (`vaelii.impl.disk.kv`): a durable write-ahead log
  over an in-RAM key→value map.  Exercised directly for a close→reopen persistence
  round-trip, WAL compaction, and torn-tail crash recovery.  The full `KvBackend`
  contract is covered by `kv-backend-test`'s suite-backend arm under
  `VAELII_TEST_BACKEND=disk-log`; here the concern is durability."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.kv :as dkv]
            [vaelii.impl.protocols :as p])
  (:import [java.io RandomAccessFile]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.util.concurrent Future]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-dkv-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- with-tmp [f]
  (let [dir (tmpdir)]
    (try (f dir) (finally (rm-rf! dir)))))

(deftest persistence-round-trip
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (p/kv-increment b [:c :n]) (p/kv-increment b [:c :n])   ; counter -> 2
        (p/kv-add-to-set b [:s 1] 1970) (p/kv-add-to-set b [:s 1] :rule) (p/kv-add-to-set b [:s 1] 'foo)
        (p/kv-put b [:v :a] {:x 1})
        (dkv/close! b))
      (testing "a reopen replays the WAL into an identical map"
        (let [b (dkv/open-kv-backend dir)]
          (is (= 2 (p/kv-get b [:c :n])) "the counter replays to its last value")
          (is (= #{1970 :rule 'foo} (p/kv-members b [:s 1])) "set + member types survive")
          (is (= 3 (p/kv-count b [:s 1])))
          (is (= {:x 1} (p/kv-get b [:v :a])))
          (dkv/close! b))))))

(deftest srem-tombstones-replay-as-absent
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (p/kv-add-to-set b [:s 1] 'a) (p/kv-add-to-set b [:s 1] 'b)
        (p/kv-remove-from-set b [:s 1] 'a) (p/kv-remove-from-set b [:s 1] 'b)   ; empties -> key removed
        (p/kv-put b [:s 2] :keep)
        (p/kv-delete b [:s 2])                                 ; explicit delete
        (dkv/close! b))
      (let [b (dkv/open-kv-backend dir)]
        (is (= #{} (p/kv-members b [:s 1])) "an emptied set replays as absent")
        (is (nil? (p/kv-get b [:s 2])) "a deleted key replays as absent")
        (dkv/close! b)))))

(deftest compaction-collapses-overwrites-preserving-state
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (try
          (dotimes [_ 200] (p/kv-increment b [:c :n]))          ; 200 frames, one live key
          (dotimes [i 50] (p/kv-add-to-set b [:s 1] i))          ; 50 frames, one live key
          (is (> (dkv/dead-ratio b) 0.9) "heavy overwrite left a mostly-dead WAL")
          (let [n     (p/kv-get b [:c :n])
                s     (p/kv-members b [:s 1])]
            (dkv/compact! b)
            (is (< (dkv/dead-ratio b) 1.0e-9) "compaction collapsed to one frame per key")
            (testing "the map is untouched by compaction"
              (is (= n (p/kv-get b [:c :n])))
              (is (= s (p/kv-members b [:s 1])))))
          (finally (dkv/close! b))))
      (testing "the compacted WAL still replays to the same state"
        (let [b (dkv/open-kv-backend dir)]
          (is (= 200 (p/kv-get b [:c :n])))
          (is (= (set (range 50)) (p/kv-members b [:s 1])))
          (dkv/close! b))))))

(deftest batch-and-clear-persist-and-replay
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (let [replies (p/kv-batch b [[:increment [:n]] [:increment [:n]] [:add-to-set [:s] 'x]
                                     [:decrement [:n]] [:put [:v] :hi] [:remove-from-set [:s] 'x]])]
          (is (= [1 2 nil 1 nil nil] replies) "incr/decr replies align positionally"))
        (dkv/close! b))
      (testing "the whole batch replays from the WAL"
        (let [b (dkv/open-kv-backend dir)]
          (is (= 1 (p/kv-get b [:n])))
          (is (= :hi (p/kv-get b [:v])))
          (is (zero? (p/kv-count b [:s])) "the sadd/srem cancelled to empty")
          (testing "kv-clear! wipes everything, and the wipe survives a reopen"
            (p/kv-clear! b)
            (dkv/close! b)
            (let [b2 (dkv/open-kv-backend dir)]
              (is (nil? (p/kv-get b2 [:n])))
              (is (nil? (p/kv-get b2 [:v])))
              (dkv/close! b2))))))))

(deftest set-overwrite-and-floored-counter-round-trip
  ;; The floor is the WAL's to reproduce as much as the live map's: a counter is a
  ;; cardinality (`p/KvBackend`), and `apply-op` is both the live fold and the replay, so
  ;; a store reopened over five decrements of an absent key must read what the store that
  ;; wrote them read.  A floor applied on only one side is a reopened index that disagrees
  ;; with the running one.
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (p/kv-add-to-set b [:k] 'a) (p/kv-add-to-set b [:k] 'b)
        (p/kv-put b [:k] #{'x 'y 'z})              ; overwrite the whole set at the key
        (dotimes [_ 5] (is (zero? (long (p/kv-decrement b [:c])))
                           "a decrement below zero answers the floor, not a negative"))
        (dkv/close! b))
      (let [b (dkv/open-kv-backend dir)]
        (is (= #{'x 'y 'z} (p/kv-members b [:k])) "kv-put overwrote, not merged")
        (is (zero? (long (p/kv-get b [:c]))) "and the replay lands on the same floor")
        (dkv/close! b)))))

(deftest compact-then-write-then-reopen-is-consistent
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 30] (p/kv-add-to-set b [:big] i))
        (dotimes [_ 30] (p/kv-increment b [:c]))
        (dkv/compact! b)                            ; collapse the churn
        (p/kv-add-to-set b [:big] 999)                   ; then write more onto the compacted WAL
        (p/kv-increment b [:c])
        (dkv/close! b))
      (testing "writes after a compaction replay correctly on reopen"
        (let [b (dkv/open-kv-backend dir)]
          (is (= (conj (set (range 30)) 999) (p/kv-members b [:big])))
          (is (= 31 (p/kv-get b [:c])))
          (is (= (p/kv-members b [:big]) (p/kv-intersect b [[:big]])) "sinter agrees after reopen")
          (dkv/close! b))))))

(deftest torn-wal-tail-recovers-on-reopen
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (p/kv-put b [:v :a] :one)
        (p/kv-put b [:v :b] :two)
        (dkv/close! b))
      (let [log (str dir "/index/kv.log")]
        (with-open [raf (RandomAccessFile. log "rw")]
          (.seek raf (.length raf))
          (.writeInt raf 999999)                 ; a frame prefix promising bytes never written
          (.write raf (byte-array 8))))
      (testing "reopen truncates the torn tail and keeps the durable entries"
        (let [b (dkv/open-kv-backend dir)]
          (is (= :one (p/kv-get b [:v :a])))
          (is (= :two (p/kv-get b [:v :b])))
          (dkv/close! b))))))

(deftest a-clean-close-compacts-so-the-next-open-replays-live-keys-only
  ;; Opening this store is a replay, so it costs the *frame* count — and a load leaves
  ;; frames far above live keys.  Closing is when to collapse that, once, rather than
  ;; paying it back on every open.  (Measured on a 300k-fact KB: 5.81M frames against
  ;; 2.01M live keys, and the open went 19.3s → 6.5s.)
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 12] (p/kv-put b [:v :k] i))          ; 12 frames, 1 live key
        (p/kv-put b [:v :other] :x)
        (is (> (dkv/dead-ratio b) 0.5) "the fixture did not accumulate deltas")
        (dkv/close! b))
      (let [b (dkv/open-kv-backend dir)]
        (testing "the state is exactly what it was"
          (is (= 11 (p/kv-get b [:v :k])))
          (is (= :x (p/kv-get b [:v :other]))))
        (testing "and the replay is now one frame per live key"
          (is (= (count @(:data b)) @(:frames b)))
          (is (zero? (dkv/dead-ratio b))))
        (dkv/close! b)))))

(deftest a-clean-close-that-has-nothing-to-collapse-leaves-the-log-alone
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 8] (p/kv-put b [:v i] i))            ; 8 frames, 8 live keys
        (is (zero? (dkv/dead-ratio b)))
        (dkv/close! b))
      (let [before (.length (java.io.File. (str dir "/index/kv.log")))
            b      (dkv/open-kv-backend dir)]
        (dkv/close! b)
        (is (= before (.length (java.io.File. (str dir "/index/kv.log"))))
            "a close with a clean log rewrote it for nothing")))))

(deftest the-clean-marker-tracks-the-wal-and-never-outlives-a-session
  (with-tmp
    (fn [dir]
      (let [root (str dir "/index")
            b    (dkv/open-kv-backend dir)]
        (p/kv-put b [:v :a] 1)
        (is (nil? (f/read-clean-marker root)) "the marker must not exist while the store is open")
        (dkv/close! b)
        (is (= (.length (java.io.File. (str root "/kv.log"))) (get (f/read-clean-marker root) "kv"))
            "a clean close records the length it closed at"))
      ;; and a crash after that close invalidates it by length alone.  Asserted on the
      ;; two things the length check decides — the damaged flag the open gate reads, and
      ;; the walk it forces — never on the replayed value, which reads the same whether
      ;; the marker was believed or not (`scan-log` stops at the torn frame either way).
      (let [path   (str dir "/index/kv.log")
            closed (.length (java.io.File. path))]
        (with-open [raf (RandomAccessFile. path "rw")]
          (.seek raf (.length raf))
          (.writeInt raf 999999)
          (.write raf (byte-array 8)))
        (let [b (dkv/open-kv-backend dir)]
          (is (:damaged b) "a log the marker cannot vouch for is flagged, not trusted")
          (is (= closed (.length (java.io.File. path)))
              "and the tail it does not describe is walked off rather than kept")
          (is (= 1 (p/kv-get b [:v :a])) "what the log does hold still replays")
          (dkv/close! b))))))

(defn- log-bytes ^long [dir]
  (with-open [raf (RandomAccessFile. (str dir "/index/kv.log") "r")]
    (.length raf)))

(deftest write-amplification-is-linear-in-members
  ;; The contract for logical (op) logging: adding the i-th member to one set logs the
  ;; member alone, not the size-i set, so a bulk load of N members writes O(N) WAL bytes.
  ;; New-value logging re-serialized the grown set on every add — O(N²), bytes/member
  ;; growing ∝ N — and would fail this gate.
  (letfn [(load-bytes [n]
            (let [dir (tmpdir)]
              (try
                (let [b (dkv/open-kv-backend dir)]
                  (try (dotimes [i n] (p/kv-add-to-set b [:functor-root 'p] i))
                       (log-bytes dir)
                       (finally (dkv/close! b))))
                (finally (rm-rf! dir)))))]
    (let [n     5000
          per-1 (/ (double (load-bytes n)) n)
          per-2 (/ (double (load-bytes (* 2 n))) (* 2 n))]
      (is (< (/ per-2 per-1) 1.3)
          (str "bytes/member should stay ~constant for a linear WAL; O(N²) would roughly "
               "double it. Got " (format "%.1f" per-1) " B/member at " n
               " vs " (format "%.1f" per-2) " at " (* 2 n))))))

(deftest mixed-ops-across-mid-run-compaction-replay-identically
  ;; Replay equivalence under op-logging: a mix of sadd/srem/incr/decr/set/del, with a
  ;; forced compaction in the middle, reconstructs the identical map on reopen.  The
  ;; ops after the compaction fold onto its `[:put k v]` snapshots.
  (with-tmp
    (fn [dir]
      (let [b     (dkv/open-kv-backend dir)
            live  (try
                    (p/kv-add-to-set b [:s 1] 'a) (p/kv-add-to-set b [:s 1] 'b) (p/kv-add-to-set b [:s 1] 'c)
                    (p/kv-increment b [:c]) (p/kv-increment b [:c])
                    (p/kv-put b [:v] {:k 1})
                    (dkv/compact! b)                       ; snapshot mid-run
                    (p/kv-remove-from-set b [:s 1] 'b)               ; then keep mutating
                    (p/kv-add-to-set b [:s 2] 'z)
                    (p/kv-decrement b [:c])
                    (p/kv-put b [:v] {:k 2})              ; overwrite a snapshotted key
                    (p/kv-delete b [:s 2])                   ; delete a post-snapshot key
                    {[:s 1] (p/kv-members b [:s 1])
                     [:s 2] (p/kv-members b [:s 2])
                     [:c]   (p/kv-get b [:c])
                     [:v]   (p/kv-get b [:v])}
                    (finally (dkv/close! b)))]
        (testing "reopen reconstructs the live map across the mid-run compaction"
          (let [b (dkv/open-kv-backend dir)]
            (is (= (get live [:s 1]) (p/kv-members b [:s 1])) "srem folded onto the snapshot")
            (is (= #{} (p/kv-members b [:s 2])) "the post-snapshot add+del cancels")
            (is (= (get live [:c]) (p/kv-get b [:c])) "incr×2 then decr → 1")
            (is (= {:k 2} (p/kv-get b [:v])) "the post-snapshot overwrite wins")
            (is (= (get live [:v]) (p/kv-get b [:v])))
            (dkv/close! b)))))))

(deftest partial-op-frame-at-tail-is-dropped-whole
  ;; A torn op frame at the tail (truthful length prefix, truncated payload) is dropped
  ;; entire on reopen — the op is never half-applied, so no set is left partially built.
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (p/kv-add-to-set b [:s 1] 'a) (p/kv-add-to-set b [:s 1] 'b)
        (dkv/close! b))
      (let [log (str dir "/index/kv.log")]
        (with-open [raf (RandomAccessFile. log "rw")]
          (.seek raf (.length raf))
          (.writeInt raf 64)                     ; promises 64 payload bytes
          (.write raf (byte-array 10))))         ; only 10 present -> a torn op frame
      (testing "reopen recovers to the last complete op; the torn op is not applied"
        (let [b (dkv/open-kv-backend dir)]
          (is (= #{'a 'b} (p/kv-members b [:s 1])) "both complete sadd ops survive, no partial")
          (dkv/close! b))))))

(deftest compact-on-a-closed-store-writes-nothing
  ;; The store-level half of the closed-store guard, for the window the registry check
  ;; cannot cover: that check runs outside the store lock, so a close can land between
  ;; it and `compact!` acquiring the lock.  An unguarded compaction of a closed log
  ;; fails late — temp and commit marker already on disk, the delete that clears them
  ;; never reached — and the next open replays that residue as a crash-interrupted
  ;; compaction.  The closed flag, consulted after the lock is acquired, makes the
  ;; call a no-op instead: no temp, no marker, and the directory reopens to exactly
  ;; the state the close made durable.
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 12] (p/kv-put b [:v :k] i))
        (p/kv-put b [:v :other] :x)
        (dkv/close! b)
        (let [{:keys [temps marker]} (f/compact-temp-paths (:log-path b))
              [[_ tmp]] temps]
          (dkv/compact! b)                        ; must not throw, must not write
          (is (not (.exists (java.io.File. ^String tmp)))
              "no compaction temp for a closed store")
          (is (not (.exists (java.io.File. ^String marker)))
              "and no commit marker for the next open to replay")))
      (let [b (dkv/open-kv-backend dir)]
        (is (= 11 (p/kv-get b [:v :k])) "the reopened state is what the close wrote")
        (is (= :x (p/kv-get b [:v :other])))
        (dkv/close! b)))))

(deftest a-compaction-queued-for-a-closed-store-is-dropped
  ;; Auto-compaction runs on a **single-thread queue**, so a task submitted by one tick
  ;; can reach the front arbitrarily later — after `close-dir!` has closed the store it
  ;; was submitted for.  `close-dir!` deregisters before it closes, so deregistration
  ;; is the signal a queued task reads; this is that it honours it and skips.
  ;;
  ;; The registry check is the early skip, not the airtight guard — it runs outside
  ;; the store lock, and the window between it and `compact!` taking that lock is the
  ;; store's own closed flag's to close (`compact-on-a-closed-store-writes-nothing`
  ;; above).  The remaining ordering — a task already inside `compact!` — needs no
  ;; guard, since it holds the store lock that `close!` blocks on.
  (let [ran     (atom 0)
        compact (fn [] (swap! ran inc))
        submit  @#'dur/submit-compaction!
        id      (dur/register! {:fsync      (fn [_] nil)
                                :close      (fn [] nil)
                                :label      "compaction-guard-test"
                                :compact    compact
                                :dead-ratio (fn [] 1.0)})]
    ;; paused so the daemon's own tick cannot fire this entry underneath the test — the
    ;; two submits below are then the only ones, and pausing gates the tick alone
    (dur/pause-compaction!)
    (try
      (testing "registered, the queued task compacts"
        (.get ^Future (submit id "registered" compact 1.0 0.5))
        (is (= 1 @ran)))
      (testing "deregistered, it is dropped rather than run against a closed store"
        (dur/deregister! id)
        (.get ^Future (submit id "closed" compact 1.0 0.5))
        (is (= 1 @ran) "a compaction ran for a store that had already deregistered"))
      (finally
        (dur/deregister! id)
        (dur/resume-compaction!)))))

;; ---- a compaction failure past the commit marker -------------------------
;; Once the marker is written the fsynced temp is the truth, and installing it over the
;; live log truncates before copying — so a failure there leaves the log half-copied
;; while the session runs on.  The install is retried once; if the retry fails too, the
;; store refuses writes until an open finishes the install off the marker.  Without this,
;; `frames` stayed unreset and the next compaction appended to the stale temp,
;; resurrecting keys deleted in between.

(defn- failing-installs
  "A stand-in for `f/replay-temp-onto-raf!` whose first `n` calls fail; the (n+1)th and
  every later one is the real install."
  [n]
  (let [real  f/replay-temp-onto-raf!
        calls (atom 0)]
    (fn [raf tmp]
      (if (< (long (swap! calls inc)) (inc (long n)))
        (throw (java.io.IOException. "install failed"))
        (real raf tmp)))))

(defn- kv-log-path ^String [dir] (str dir "/index/kv.log"))

(deftest a-post-marker-kv-install-failure-is-retried
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 10] (p/kv-put b [:k i] i))
        (doseq [i (range 2 10 2)] (p/kv-delete b [:k i]))       ; leave a dead ratio to compact
        (let [before (into {} (map (fn [i] [[:k i] (p/kv-get b [:k i])])) (range 10))]
          (with-redefs [f/replay-temp-onto-raf! (failing-installs 1)]
            (dkv/compact! b))
          (testing "the retry installed the compacted log and the session goes on"
            (is (= before (into {} (map (fn [i] [[:k i] (p/kv-get b [:k i])])) (range 10))))
            (let [{:keys [marker temps]} (f/compact-temp-paths (kv-log-path dir))]
              (is (not-any? #(.exists (java.io.File. ^String %))
                            (cons marker (map second temps)))
                  "and the temps are gone")))
          (testing "the store is still writable"
            (p/kv-put b [:k :new] 99)
            (is (= 99 (p/kv-get b [:k :new]))))
          (dkv/close! b))))))

(deftest a-post-marker-kv-install-that-keeps-failing-refuses-writes
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 6] (p/kv-put b [:k i] i))
        (doseq [i (range 1 6 2)] (p/kv-delete b [:k i]))
        (testing "the compaction fails out, and writes refuse rather than tearing the log further"
          (with-redefs [f/replay-temp-onto-raf! (failing-installs 4)]
            (is (thrown? java.io.IOException (dkv/compact! b))))
          (is (= :compaction-failed
                 (:type (try (p/kv-put b [:k :x] 1) (catch clojure.lang.ExceptionInfo e (ex-data e))))))
          (testing "but a read still answers off the valid in-RAM map"
            (is (= 0 (p/kv-get b [:k 0])))))
        (dkv/close! b)
        (testing "the next open finishes the install off the marker, deleted keys stay deleted"
          (let [b2 (dkv/open-kv-backend dir)]
            (is (= 2 (p/kv-get b2 [:k 2])))
            (is (nil? (p/kv-get b2 [:k 1])) "a key deleted before the failed compaction is gone")
            (dkv/close! b2)))))))

(deftest a-kv-clear-supersedes-a-failed-compaction
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 6] (p/kv-put b [:k i] i))
        (doseq [i (range 1 6 2)] (p/kv-delete b [:k i]))
        (with-redefs [f/replay-temp-onto-raf! (failing-installs 4)]
          (is (thrown? java.io.IOException (dkv/compact! b))))
        (testing "a clear wins over the failed compaction: it drops the marker and reopens clean"
          (p/kv-clear! b)
          (p/kv-put b [:k :fresh] 7)                            ; a write after clear is allowed again
          (is (= 7 (p/kv-get b [:k :fresh])))
          (dkv/close! b)
          (let [b2 (dkv/open-kv-backend dir)]
            (is (= 7 (p/kv-get b2 [:k :fresh])))
            (is (nil? (p/kv-get b2 [:k 0])) "the pre-clear snapshot was not replayed back")
            (dkv/close! b2)))))))
