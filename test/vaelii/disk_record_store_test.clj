;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-record-store-test
  "The on-disk `RecordStore` adapter (`vaelii.impl.disk.record-store`), exercised
  directly: put/get/delete across the three kinds, the derived premise set, a
  close→reopen persistence round-trip, compaction of dead frames, and torn-tail crash
  recovery.  Needs no KB — the store is a plain id→blob engine over the
  disk `files` primitives."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.disk.codec :as codec]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx])
  (:import [java.io RandomAccessFile]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-drs-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- with-tmp
  "Run `(f dir)` in a fresh temp directory, deleting it afterwards."
  [f]
  (let [dir (tmpdir)]
    (try (f dir) (finally (rm-rf! dir)))))

(deftest put-get-delete-across-kinds
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (testing "monotonic ids, one space across sentexes and justifications"
            (let [a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})
                  b (p/put-justification s {:informant :rule :antecedents [a]})
                  c (p/put-sentex s {:sentence '(cat Tom) :context 'C})]
              (is (= [1 2 3] [a b c]) "ids allocated 1,2,3 across kinds")
              (is (= '(dog Muffet) (:sentence (p/get-sentex s a))))
              (is (= [a] (:antecedents (p/get-justification s b))))
              (is (= #{a c} (p/sentex-ids s)))
              (is (= #{b} (p/justification-ids s)))))
          (testing "provenance is keyed by the record handle and dies with it"
            (p/put-provenance s 1 {:creator "t" :created 42})
            (is (= {:creator "t" :created 42} (p/get-provenance s 1)))
            (p/delete-sentex! s 1)
            (is (nil? (p/get-sentex s 1)))
            (is (nil? (p/get-provenance s 1)) "provenance torn down with the sentex")
            (is (= #{3} (p/sentex-ids s))))
          (finally (drs/close! s)))))))

(deftest premises-are-derived-from-strength
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (let [a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})
                b (p/put-sentex s {:sentence '(cat Tom) :context 'C})]
            (p/mark-premise s a :monotonic)
            (is (= #{a} (p/premise-ids s)))
            (is (= :monotonic (p/premise-strength s a)))
            (is (= :default (p/premise-strength s b)) "an unmarked sentex is :default")
            (p/mark-premise s b nil)
            (is (= #{a b} (p/premise-ids s)))
            (is (= :default (p/premise-strength s b)) "nil strength stored as :default")
            (p/unmark-premise! s a)
            (is (= #{b} (p/premise-ids s)))
            (is (= :default (p/premise-strength s a))))
          (finally (drs/close! s)))))))

(deftest premise-strength-of-a-bad-id-is-default-on-either-store
  ;; `premise-strength` reads the slot directly (not through `fetch`), so it must keep
  ;; `fetch`'s guard: a non-integer informant or a negative id is a key the store does not
  ;; hold, answered `:default` — never a `read-slot` coercion throw — exactly as the memory
  ;; store answers, or the backend leaks through a read.
  (with-tmp
    (fn [dir]
      (let [d (drs/open-record-store dir)
            m (mem/memory-record-store {:space ::bad-id-premise})]
        (try
          (doseq [s [d m]]
            (is (= :default (p/premise-strength s :some-informant)) "a non-integer id")
            (is (= :default (p/premise-strength s -1)) "a negative id")
            (is (= :default (p/premise-strength s 999)) "an id the store never issued"))
          (finally
            (drs/close! d)
            (p/clear-records! m)))))))

(deftest marking-an-unstored-handle-marks-nothing-on-either-store
  ;; the premise set follows the record set: a handle with no sentex takes no mark, on
  ;; the memory store exactly as on the disk one — the two must answer `premise-ids`
  ;; identically for the same call sequence, or the backend matrix reads a phantom
  (with-tmp
    (fn [dir]
      (let [d (drs/open-record-store dir)
            m (mem/memory-record-store {:space ::phantom-premise})]
        (try
          (doseq [s [d m]]
            (p/mark-premise s 999 :default)
            (is (= #{} (p/premise-ids s)) "no record, no premise")
            (p/unmark-premise! s 999)
            (is (= #{} (p/premise-ids s))))
          (finally
            (drs/close! d)
            (p/clear-records! m)))))))

;; ---- the premise bit ----------------------------------------------------
;; The premise set is read off the idx slots rather than by decoding every record, so
;; these are about the two ways it can be answered agreeing — and about a store whose
;; slots predate the bit staying correct, since that is what makes trusting it safe.

(defn- slot-premises
  "What the sentex idx says about `ids` — `true` / `false` / nil for a slot that does not
  say.  Read straight from the file, so the store must be closed."
  [^String dir ids]
  (let [idx (f/open-idx (str dir "/records/sentexes.idx"))]
    (try
      (into {} (map (fn [id] [id (some-> (f/read-slot idx id) :flags f/slot-premise)])) ids)
      (finally (f/close! idx)))))

(defn- strip-premise-flags!
  "Rewrite `ids`' slots (every live slot when nil) with flags 0 — the shape a store
  written before the premise bit existed has.  A legitimate fixture, not a hack: it is
  the only way to test the fallback path from inside a build that always writes the bit."
  [^String dir ids]
  (let [idx (f/open-idx (str dir "/records/sentexes.idx"))]
    (try
      (doseq [id (or ids (range (f/slot-count idx)))
              :let [slot (f/read-slot idx id)]
              :when (and slot (not (:tombstone? slot)))]
        (f/write-slot! idx id (:offset slot) (:length slot) 0 (:gen slot)))
      (finally (f/close! idx)))))

(defn- strip-strength-flags!
  "Rewrite `ids`' premise slots keeping the premise bit but zeroing the strength rank —
  the shape a store written after the premise bit but before the strength bits has.  That
  is the slot `premise-strength` must fall back to the record for."
  [^String dir ids]
  (let [idx (f/open-idx (str dir "/records/sentexes.idx"))]
    (try
      (doseq [id ids
              :let [slot (f/read-slot idx id)]
              :when (and slot (not (:tombstone? slot)) (f/slot-premise (:flags slot)))]
        (f/write-slot! idx id (:offset slot) (:length slot) (f/premise-flags true 0) (:gen slot)))
      (finally (f/close! idx)))))

;; ---- the flags word after a crash ---------------------------------------
;; The flags word (premise bit + strength rank) is a cache over the durable record and is
;; not crash-atomic: a 24-byte slot straddles a page, so a torn flags page across a crash
;; can persist a handle's new frame while leaving the old flags.  A clean open trusts the
;; slot; a **dirty** open must reconcile it against the records.  These pin that it does,
;; on both a stale rank and a stale bit, tokenized and not — and that a clean open does not.

(defn- corrupt-slot-flags!
  "Overwrite `id`'s sentex slot with `flags`, keeping its offset/length/gen — the shape a
  torn flags page leaves: the frame is current but the flags word reverted.  Store closed."
  [^String dir id flags]
  (let [idx (f/open-idx (str dir "/records/sentexes.idx"))]
    (try
      (let [slot (f/read-slot idx id)]
        (f/write-slot! idx id (:offset slot) (:length slot) flags (:gen slot)))
      (finally (f/close! idx)))))

(defn- simulate-crash!
  "Leave `dir` in the on-disk state a crashed session leaves: the dirty marker present (its
  open never ran a clean close!) and the clean marker gone."
  [^String dir]
  (let [root (str dir "/records")]
    (f/remove-clean-marker! root)
    (f/create-dirty-marker! root)))

(defn- slot-flags [^String dir id]
  (let [idx (f/open-idx (str dir "/records/sentexes.idx"))]
    (try (:flags (f/read-slot idx id)) (finally (f/close! idx)))))

(deftest a-dirty-open-reconciles-a-stale-strength-rank
  ;; `premise-strength` reads the rank off the slot, so a clean open would trust a torn
  ;; one.  A dirty open rewrites the slot to the record's rank.
  (doseq [tok [false true]]
    (with-tmp
      (fn [dir]
        (let [s (drs/open-record-store dir {:tokenize? tok})
              a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})]
          (p/mark-premise s a :monotonic)                       ; rank 2 on disk
          (drs/close! s))
        (corrupt-slot-flags! dir 1 (f/premise-flags true 1))    ; stale: premise, rank 1
        (simulate-crash! dir)
        (let [s2 (drs/open-record-store dir {:tokenize? tok})]
          (try
            (is (= :monotonic (p/premise-strength s2 1))
                (str "tokenize? " tok ": dirty open restored the rank (a clean open reads the stale :default)"))
            (is (= #{1} (p/premise-ids s2)))
            (finally (drs/close! s2))))
        (is (= 2 (f/slot-strength (slot-flags dir 1)))
            (str "tokenize? " tok ": the slot itself is rewritten, so the next clean open is right"))))))

(deftest a-dirty-open-reconciles-a-stale-premise-bit
  ;; A torn page can flip the bit too: a slot claiming premise over a record that is not
  ;; one, and the reverse.  The set follows the records and the slots are rewritten to match.
  (doseq [tok [false true]]
    (with-tmp
      (fn [dir]
        (let [s (drs/open-record-store dir {:tokenize? tok})
              a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})   ; a premise
              _ (p/put-sentex s {:sentence '(cat Tom) :context 'C})]     ; not a premise
          (p/mark-premise s a :default)
          (drs/close! s))
        (corrupt-slot-flags! dir 1 (f/premise-flags false))     ; a: bit lost
        (corrupt-slot-flags! dir 2 (f/premise-flags true 2))    ; b: phantom premise, rank 2
        (simulate-crash! dir)
        (let [s2 (drs/open-record-store dir {:tokenize? tok})]
          (try
            (is (= #{1} (p/premise-ids s2))
                (str "tokenize? " tok ": the set follows the records, not the torn bits"))
            (is (= :default (p/premise-strength s2 1)))
            (is (= :default (p/premise-strength s2 2))
                "b is not a premise, whatever its slot claimed")
            (finally (drs/close! s2))))
        (is (true?  (f/slot-premise (slot-flags dir 1))) "a's premise bit restored")
        (is (false? (f/slot-premise (slot-flags dir 2))) "b's phantom bit cleared")
        (is (zero?  (f/slot-strength (slot-flags dir 2))) "b's phantom rank cleared")))))

(deftest a-clean-open-does-not-reconcile-the-flags
  ;; The reconcile is a dirty-open cost only.  A clean reopen trusts the slots as written,
  ;; so a stale one survives it untouched — which is what keeps the fast path fast.
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)
            a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})]
        (p/mark-premise s a :monotonic)
        (drs/close! s))
      (corrupt-slot-flags! dir 1 (f/premise-flags true 1))      ; stale rank, but no crash
      (let [s2 (drs/open-record-store dir)]                      ; clean reopen
        (try
          (is (= :default (p/premise-strength s2 1))
              "a clean open reads the slot as written — the stale rank survives, so no reconcile fired")
          (finally (drs/close! s2))))
      (is (= 1 (f/slot-strength (slot-flags dir 1))) "the slot was not rewritten on a clean open"))))

(deftest every-write-path-annotates-its-slot
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (p/put-sentex s {:sentence '(dog Muffet) :context 'C})                     ; 1
        (p/put-sentex s {:sentence '(cat Tom) :context 'C :strength :monotonic})  ; 2
        (p/put-sentex s {:sentence '(pig Sam) :context 'C})                      ; 3
        (p/mark-premise s 1 :default)
        (p/unmark-premise! s 2)
        (drs/close! s))
      (testing "a put, a put carrying :strength, mark and unmark all leave the slot saying"
        (is (= {1 true, 2 false, 3 false} (slot-premises dir [1 2 3]))
            "nothing reads as unknown, so the reopen decodes no records at all")))))

(deftest a-bulk-sink-leaves-the-store-the-loop-would-have-left
  ;; The sink writes one log frame and one idx range per batch where `put-sentex` writes
  ;; two syscalls per record, so the risk is entirely in what the *slots* end up saying:
  ;; the premise bit and the strength rank are packed by the batch rather than one at a
  ;; time, and a reopen reads the premise set off them without decoding a record.  So the
  ;; comparison is store-against-store, and then off the slots alone.
  (let [records (fn [n]
                  (into [] (for [i (range n)]
                             (cond-> {:sentence (list 'p i) :context 'C}
                               (zero? (mod i 3)) (assoc :strength :monotonic)
                               (= 1 (mod i 3))   (assoc :strength :default)))))
        state   (fn [s ids]
                  {:records   (into {} (map (fn [id] [id (:sentence (p/get-sentex s id))])) ids)
                   :live      (set (p/sentex-ids s))
                   :premises  (set (p/premise-ids s))
                   :strengths (into {} (map (fn [id] [id (p/premise-strength s id)]))
                                    (sort (p/premise-ids s)))})
        run     (fn [dir sink?]
                  (let [s   (drs/open-record-store dir)
                        rs  (records 25)
                        ids (if sink?
                              ;; a batch smaller than the stream, so a mid-stream flush runs
                              (with-open [^java.io.Closeable snk
                                          (cap/sentex-sink s {:batch 7})]
                                (mapv #(p/write-record! snk %) rs))
                              (mapv #(p/put-sentex s %) rs))]
                    (try [ids (state s ids)] (finally (drs/close! s)))))]
    (with-tmp
      (fn [a]
        (with-tmp
          (fn [b]
            (let [[sink-ids sink-state] (run a true)
                  [loop-ids loop-state] (run b false)]
              (is (= loop-ids sink-ids) "the same handles, minted the same way")
              (is (= loop-state sink-state)
                  "and the same records, live set, premise set and strengths")
              (testing "and the same thing off the slots, with the stores closed"
                (is (= (slot-premises b loop-ids) (slot-premises a sink-ids)))
                (is (every? some? (vals (slot-premises a sink-ids)))
                    "nothing reads as unknown, so a reopen decodes no records"))
              (testing "which survives the reopen the slots exist for"
                (let [s (drs/open-record-store a)]
                  (try (is (= (:premises sink-state) (set (p/premise-ids s))))
                       (is (= (:strengths sink-state)
                              (into {} (map (fn [id] [id (p/premise-strength s id)]))
                                    (sort (p/premise-ids s)))))
                       (finally (drs/close! s))))))))))))

(deftest a-bulk-sink-writes-handles-that-are-not-consecutive
  ;; `write-slots!` coalesces a run of consecutive ids into one positional write, so a
  ;; batch that is *not* one run is the case that exercises the splitting — a dump whose
  ;; handles have gaps, which is any dump written after a retraction.
  (with-tmp
    (fn [dir]
      (let [ids [40 1 41 2 900 42]
            s   (drs/open-record-store dir)]
        (with-open [^java.io.Closeable snk (cap/sentex-sink s {:batch 100})]
          (doseq [id ids]
            (p/write-record! snk {:id id :sentence (list 'p id) :context 'C
                                  :strength (when (even? id) :monotonic)})))
        (is (= (set ids) (set (p/sentex-ids s))))
        (is (= (set (filter even? ids)) (set (p/premise-ids s))))
        (is (= (list 'p 900) (:sentence (p/get-sentex s 900))))
        (drs/close! s))
      (testing "and the gapped slots say the same after a reopen"
        (let [s (drs/open-record-store dir)]
          (try
            (is (= #{40 2 900 42} (set (p/premise-ids s))))
            (is (= '(p 41) (:sentence (p/get-sentex s 41))))
            (is (nil? (p/get-sentex s 43)) "the gap is empty, not garbage")
            (finally (drs/close! s))))))))

(deftest a-bulk-batch-that-is-not-positive-is-refused
  ;; `:batch` is how many records buffer before one pair of writes, so a batch that is not
  ;; a positive count is a sink with no flush unit: zero buffers a corpus into heap and
  ;; never writes it, and a negative one is a size nothing can be partitioned into.  The
  ;; refusal is at the open, where a caller can still name a different number, rather than
  ;; part-way through a load that has already stored millions of frames.
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (doseq [batch [0 -1]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo (cap/sentex-sink s {:batch batch})))]
              (is (= :bad-batch (:type (ex-data e))))
              (is (= batch (:batch (ex-data e))) "naming the number it was handed")))
          (testing "and the justification half opens through the same door"
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (cap/justification-sink s {:batch 0})))]
              (is (= :bad-batch (:type (ex-data e))))))
          (testing "a refused sink stored nothing"
            (is (= #{} (p/sentex-ids s)))
            (is (= #{} (p/justification-ids s))))
          (finally (drs/close! s)))))))

(deftest the-premise-set-agrees-with-the-records-it-is-derived-from
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (dotimes [i 8] (p/put-sentex s {:sentence (list 'p i) :context 'C}))     ; 1..8
        (p/put-sentex s {:sentence '(q 1) :context 'C :strength :monotonic})     ; 9
        (doseq [id [2 4 6]] (p/mark-premise s id :default))
        (p/unmark-premise! s 4)
        (p/delete-sentex! s 6)
        (is (= #{2 9} (p/premise-ids s)))
        (drs/close! s))
      (let [expected #{2 9}
            reopened (fn [] (let [s (drs/open-record-store dir)]
                              (try [(p/premise-ids s) (p/premise-strength s 9)]
                                   (finally (drs/close! s)))))]
        (testing "read off the slots"
          (is (= [expected :monotonic] (reopened))))
        (testing "and identically for a store only half of whose slots say"
          ;; every store that predates the bit passes through this state as it upgrades
          (strip-premise-flags! dir [2])
          (is (= [expected :monotonic] (reopened))))
        (testing "and identically off the records alone, when no slot says"
          (strip-premise-flags! dir nil)
          (is (= [expected :monotonic] (reopened))))))))

(deftest compaction-carries-the-premise-bit-across
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (dotimes [i 20] (p/put-sentex s {:sentence (list 'p i) :context 'C}))
        (doseq [id (range 1 21 2)] (p/mark-premise s id :monotonic))   ; the odds
        (doseq [id (range 2 21 4)] (p/delete-sentex! s id))            ; earn a compaction
        (let [expected (p/premise-ids s)]
          (is (= (set (range 1 21 2)) expected))
          (drs/compact! s)
          (is (= expected (p/premise-ids s)) "the live premise set is untouched")
          (drs/close! s)
          (testing "the rewritten slots still say so — flags dropped here would lose no
                    premise, but would put every later open back to decoding the store"
            (is (= (zipmap (range 1 21 2) (repeat true))
                   (slot-premises dir (range 1 21 2))))
            (is (= {2 nil, 6 nil} (slot-premises dir [2 6])) "deleted, so no slot to say"))
          (testing "and the reopen reads the same set back"
            (let [s2 (drs/open-record-store dir)]
              (is (= expected (p/premise-ids s2)))
              (is (= :monotonic (p/premise-strength s2 1)))
              (drs/close! s2))))))))

(deftest persistence-round-trip
  (with-tmp
    (fn [dir]
      (let [s1 (drs/open-record-store dir)
            a  (p/put-sentex s1 {:sentence '(dog Muffet) :context 'C})
            b  (p/put-justification s1 {:informant :rule})
            _  (p/mark-premise s1 a :monotonic)
            _  (p/put-provenance s1 a {:creator "t"})
            next-before (p/next-id s1)]           ; consumes an id (=3)
        (drs/close! s1)
        (testing "a reopen recovers every record, the premise set, and the counter"
          (let [s2 (drs/open-record-store dir)]
            (try
              (is (= '(dog Muffet) (:sentence (p/get-sentex s2 a))))
              (is (= :monotonic (:strength (p/get-sentex s2 a))))
              (is (= {:informant :rule :id b} (p/get-justification s2 b)))
              (is (= {:creator "t"} (p/get-provenance s2 a)))
              (is (= #{a} (p/premise-ids s2)) "premise set rebuilt from :strength")
              (is (= :monotonic (p/premise-strength s2 a)))
              (is (= #{a} (p/sentex-ids s2)))
              (is (= #{b} (p/justification-ids s2)))
              (is (> (p/next-id s2) next-before) "the id counter never goes backwards")
              (finally (drs/close! s2)))))))))

(deftest clear-records-empties-the-store
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (p/put-sentex s {:sentence '(dog Muffet) :context 'C})
          (p/mark-premise s 1 :monotonic)
          (p/clear-records! s)
          (is (= #{} (p/sentex-ids s)))
          (is (= #{} (p/premise-ids s)))
          (is (nil? (p/get-sentex s 1)))
          (is (= 1 (p/next-id s)) "the counter resets")
          (finally (drs/close! s)))))))

(deftest compaction-reclaims-dead-frames-preserving-live-records
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          ;; churn: write 40 sentexes, delete the even-id ones, re-store premises
          (dotimes [i 40] (p/put-sentex s {:sentence (list 'p i) :context 'C :n i}))
          (doseq [id (range 2 41 2)] (p/delete-sentex! s id))
          (dotimes [i 10] (p/mark-premise s (inc (* 2 i)) :monotonic))   ; re-store odds
          (let [before (drs/dead-ratio s)]
            (is (pos? before) "deletes + re-stores left dead frames")
            (drs/compact! s)
            (is (< (drs/dead-ratio s) 1.0e-9) "compaction reclaimed the dead frames"))
          (testing "every live record and its handle survived compaction"
            (is (= (set (range 1 41 2)) (p/sentex-ids s)))
            (doseq [id (range 1 41 2)]
              (is (= (list 'p (dec id)) (:sentence (p/get-sentex s id))))))
          (finally (drs/close! s)))))))

(deftest next-id-never-reuses-a-handle-across-recovery
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (dotimes [_ 5] (p/put-sentex s {:sentence 'x :context 'C}))   ; ids 1..5
        (doseq [id (range 1 6)] (p/delete-sentex! s id))              ; delete them all
        (drs/close! s))
      (testing "a reopen with the counters blob deleted still climbs past the max slot"
        (let [counters (str dir "/records/counters.nippy")]
          (.delete (java.io.File. counters)))
        (let [s (drs/open-record-store dir)]
          (is (>= (p/next-id s) 6) "next-id recovers as 1 + highest slot id, not 1")
          (drs/close! s)))
      (testing "a stale (too-low) counters blob loses to the max-slot floor"
        (f/write-nippy-atomic! (str dir "/records/counters.nippy") {:seq 2})
        (let [s (drs/open-record-store dir)]
          (is (>= (p/next-id s) 6))
          (drs/close! s))))))

(deftest compaction-of-the-highest-deleted-slot-preserves-next-id
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (dotimes [_ 5] (p/put-sentex s {:sentence 'x :context 'C}))   ; ids 1..5
        (p/delete-sentex! s 5)                                        ; delete the HIGHEST
        (drs/compact! s)                                              ; would drop slot 5
        (drs/close! s))
      (testing "reopen still refuses to reissue handle 5"
        (let [s (drs/open-record-store dir)
              fresh (repeatedly 3 #(p/next-id s))]
          (is (every? #(>= % 6) fresh) "every fresh handle is past the compacted-away max")
          (is (apply distinct? fresh))
          (drs/close! s))))))

(deftest an-orphan-frame-is-harmless-and-reclaimed
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (p/put-sentex s {:sentence '(dog Muffet) :context 'C})          ; id 1, slot 1
        (drs/close! s))
      ;; simulate a crash after the frame append but before the slot write: a frame
      ;; with no idx slot pointing at it.
      (let [log (f/open-log (str dir "/records/sentexes.log"))]
        (f/append-record! log {:orphan true})
        (f/close! log))
      (let [s (drs/open-record-store dir)]
        (testing "the orphan is not a record — no slot references it"
          (is (= #{1} (p/sentex-ids s)))
          (is (= '(dog Muffet) (:sentence (p/get-sentex s 1)))))
        (testing "and compaction reclaims its dead bytes, keeping the live record"
          (is (pos? (drs/dead-ratio s)))
          (drs/compact! s)
          (is (< (drs/dead-ratio s) 1.0e-9))
          (is (= #{1} (p/sentex-ids s)))
          (is (= '(dog Muffet) (:sentence (p/get-sentex s 1)))))
        (drs/close! s)))))

(deftest repeated-compaction-and-reopen-stay-consistent
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (dotimes [round 3]
            (dotimes [i 20] (p/put-sentex s {:sentence (list 'r round i) :context 'C}))
            (doseq [id (take-nth 3 (p/sentex-ids s))] (p/delete-sentex! s id))
            (drs/compact! s))
          (let [survivors (p/sentex-ids s)
                content   (into {} (map (fn [id] [id (:sentence (p/get-sentex s id))])) survivors)]
            (drs/close! s)
            (let [s2 (drs/open-record-store dir)]
              (testing "every surviving record reopens byte-identical"
                (is (= survivors (p/sentex-ids s2)))
                (doseq [[id sen] content]
                  (is (= sen (:sentence (p/get-sentex s2 id)))))
                (drs/close! s2))))
          (finally nil))))))

(deftest compaction-folds-in-concurrent-writes
  ;; The copy-on-write compactor does its O(live) rewrite without the kind lock, so
  ;; stores/kills can land in the middle.  `append-record-sized!` is called (lock-free)
  ;; once per live frame during that rewrite, so a one-shot hook on it fires exactly there
  ;; — modelling a concurrent writer that interleaves mid-compaction — and those writes
  ;; must be folded into the compacted result, not lost or overwritten by stale frames.
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (dotimes [i 20] (p/put-sentex s {:sentence (list 'p (inc i)) :context 'C})) ; 1..20
          (doseq [id (range 2 21 2)] (p/delete-sentex! s id))                         ; evens gone
          (let [real     f/append-record-sized!
                fired    (atom false)
                added    (atom nil)
                before   (drs/dead-ratio s)]
            (with-redefs [f/append-record-sized!
                          (fn [raf v]
                            (when (compare-and-set! fired false true)
                              (reset! added (p/put-sentex s {:sentence '(p 99) :context 'C}))
                              (p/delete-sentex! s 1)               ; kill a snapshotted-live id
                              (p/mark-premise s 3 :monotonic))     ; re-store a snapshotted id
                            (real raf v))]
              (drs/compact! s))
            (testing "compaction reclaimed most dead frames — the concurrent delta's
                     now-stale snapshot copies (id 1's, id 3's) remain as a small
                     residual a follow-up compaction sweeps"
              (is (< (drs/dead-ratio s) before))
              (drs/compact! s)                                     ; no concurrency now
              (is (< (drs/dead-ratio s) 1.0e-9) "a clean follow-up reaches zero"))
            (testing "the mid-rewrite store/kill/re-store all folded into the result"
              (is (= (conj (set (range 3 21 2)) @added) (p/sentex-ids s)))
              (is (nil? (p/get-sentex s 1)) "the concurrent delete took")
              (is (= '(p 99) (:sentence (p/get-sentex s @added))) "the concurrent store survived")
              (is (= :monotonic (:strength (p/get-sentex s 3))) "the concurrent re-store applied")
              (is (= #{3} (p/premise-ids s))))
            (testing "the in-RAM view reopens byte-identical"
              (let [survivors (p/sentex-ids s)
                    content   (into {} (map (fn [id] [id (p/get-sentex s id)])) survivors)]
                (drs/close! s)
                (let [s2 (drs/open-record-store dir)]
                  (is (= survivors (p/sentex-ids s2)))
                  (doseq [[id rec] content] (is (= rec (p/get-sentex s2 id))))
                  (is (>= (p/next-id s2) (inc @added)) "next-id never reissues a handle")
                  (drs/close! s2)))))
          (finally nil))))))

(deftest a-clear-during-compaction-aborts-it-rather-than-resurrecting
  ;; A `clear-records!` that lands in the lock-free rewrite must win: the compactor
  ;; snapshotted the pre-wipe state, so replaying its temps would resurrect it.  The
  ;; abort flag makes the reconcile discard the temps instead.
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (dotimes [i 10] (p/put-sentex s {:sentence (list 'p i) :context 'C}))
          (doseq [id (range 2 11 2)] (p/delete-sentex! s id))
          (let [real  f/append-record-sized!
                fired (atom false)]
            (with-redefs [f/append-record-sized!
                          (fn [raf v]
                            (when (compare-and-set! fired false true) (p/clear-records! s))
                            (real raf v))]
              (drs/compact! s)))
          (testing "the clear won — the store is empty, not resurrected from the snapshot"
            (is (= #{} (p/sentex-ids s)))
            (is (= #{} (p/premise-ids s))))
          (testing "and it stays empty across reopen (no committed temp replayed)"
            (drs/close! s)
            (let [s2 (drs/open-record-store dir)]
              (is (= #{} (p/sentex-ids s2)))
              (drs/close! s2)))
          (finally nil))))))

;; ---- a failure past the commit marker ------------------------------------
;; Once the marker is written the fsynced temps are the truth, and installing them over
;; the live RAFs truncates before copying — so a failure there leaves the live files
;; half-copied while the session keeps running.  The install is retried once; if the
;; retry fails too, the kind refuses every read and write until an open finishes the
;; install off the marker.  The failure is injected under `f/replay-temp-onto-raf!`, the
;; one call that sits past the marker.

(defn- failing-installs
  "A stand-in for `f/replay-temp-onto-raf!` whose first `n` calls fail — the (n+1)th
  and every later one is the real install."
  [n]
  (let [real  f/replay-temp-onto-raf!
        calls (atom 0)]
    (fn [raf tmp]
      (if (< (long (swap! calls inc)) (inc (long n)))
        (throw (java.io.IOException. "install failed"))
        (real raf tmp)))))

(deftest a-post-marker-install-failure-is-retried
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (dotimes [i 10] (p/put-sentex s {:sentence (list 'p i) :context 'C}))
          (doseq [id (range 2 11 2)] (p/delete-sentex! s id))
          (let [before (into {} (map (fn [id] [id (p/get-sentex s id)])) (p/sentex-ids s))]
            (with-redefs [f/replay-temp-onto-raf! (failing-installs 1)]
              (drs/compact! s))
            (testing "the retry installed the compacted files and the session goes on"
              (is (= before (into {} (map (fn [id] [id (p/get-sentex s id)])) (p/sentex-ids s))))
              (is (< (drs/dead-ratio s) 1.0e-9) "the compaction took")
              (let [{:keys [marker temps]}
                    (f/compact-temp-paths (str dir "/records/sentexes.log")
                                          (str dir "/records/sentexes.idx"))]
                (is (not-any? #(.exists (java.io.File. ^String %))
                              (cons marker (map second temps)))
                    "and the temps are gone")))
            (testing "the store is still writable"
              (is (= '(p 99) (:sentence (p/get-sentex s (p/put-sentex s {:sentence '(p 99) :context 'C})))))))
          (finally (drs/close! s)))))))

(deftest a-post-marker-install-that-keeps-failing-makes-the-kind-refuse
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)
            a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})
            b (p/put-sentex s {:sentence '(cat Tom) :context 'C})]
        (p/delete-sentex! s b)
        (testing "the compaction fails out, and the kind refuses rather than answering off torn files"
          (with-redefs [f/replay-temp-onto-raf! (failing-installs 4)]
            (is (thrown? java.io.IOException (drs/compact! s))))
          (is (= :compaction-failed
                 (:type (try (p/get-sentex s a) (catch clojure.lang.ExceptionInfo e (ex-data e))))))
          (is (= :compaction-failed
                 (:type (try (p/put-sentex s {:sentence '(dog Rex) :context 'C})
                             (catch clojure.lang.ExceptionInfo e (ex-data e))))))
          (is (= :compaction-failed
                 (:type (try (p/delete-sentex! s a) (catch clojure.lang.ExceptionInfo e (ex-data e)))))))
        (drs/close! s)
        (testing "the next open finishes the install off the marker, and the records are whole"
          (let [s2 (drs/open-record-store dir)]
            (try
              (is (= '(dog Muffet) (:sentence (p/get-sentex s2 a))))
              (is (= #{a} (p/sentex-ids s2)))
              (is (< (drs/dead-ratio s2) 1.0e-9) "the compacted log is what opened")
              (finally (drs/close! s2)))))))))

(deftest torn-log-tail-recovers-on-reopen
  (with-tmp
    (fn [dir]
      (let [s1 (drs/open-record-store dir)
            a  (p/put-sentex s1 {:sentence '(dog Muffet) :context 'C})
            b  (p/put-sentex s1 {:sentence '(cat Tom) :context 'C})]
        (drs/close! s1)
        ;; simulate a crash mid-append: a length prefix promising bytes that were
        ;; never written — the partial frame the next writer never finished.
        (let [log (str dir "/records/sentexes.log")]
          (with-open [raf (RandomAccessFile. log "rw")]
            (.seek raf (.length raf))
            (.writeInt raf 999999)
            (.write raf (byte-array 8))))
        (testing "reopen truncates the torn tail and keeps the durable records"
          (let [s2 (drs/open-record-store dir)]
            (try
              (is (= '(dog Muffet) (:sentence (p/get-sentex s2 a))))
              (is (= '(cat Tom) (:sentence (p/get-sentex s2 b))))
              (is (= #{a b} (p/sentex-ids s2)))
              (let [log-raf (f/open-log (str dir "/records/sentexes.log"))]
                (is (= (f/log-length log-raf) (f/scan-log log-raf (fn [_ _] nil)))
                    "no torn frame remains at the tail")
                (f/close! log-raf))
              (finally (drs/close! s2)))))))))

(deftest the-clean-marker-records-what-closed-and-is-consumed-by-the-open
  ;; The marker lets an open skip the torn-tail walk.  What makes that safe is that it
  ;; describes a store nobody holds: written at close, deleted at open, and believed only
  ;; while the log is still exactly that long.
  (with-tmp
    (fn [dir]
      (let [root (str dir "/records")
            s1   (drs/open-record-store dir)]
        (p/put-sentex s1 {:sentence '(dog Muffet) :context 'C})
        (is (nil? (f/read-clean-marker root)) "a marker survived into an open session")
        (drs/close! s1)
        (let [m (f/read-clean-marker root)]
          (is (= (.length (java.io.File. (str root "/sentexes.log"))) (get m "sentexes"))
              "the marker must name the length the log closed at")
          (is (contains? m "justifications"))
          (is (contains? m "provenance"))))
      (testing "the next open consumes it, so a crash cannot leave a believable one behind"
        (let [s2 (drs/open-record-store dir)]
          (is (nil? (f/read-clean-marker (str dir "/records"))))
          (drs/close! s2))))))

(deftest a-marker-that-disagrees-with-the-log-is-ignored
  ;; The staleness modes that can actually arise, each asserted to fall back to the walk.
  ;; A marker forged to match a *torn* log is deliberately not among them: the length
  ;; check answers "has anything happened since the close said so", and what makes a
  ;; matching answer trustworthy is the invariant above — the marker is written after the
  ;; fsync and consumed by the next open, so one can never describe a log that grew.
  (doseq [[label forge] [["stale — names a shorter log than exists"
                          (fn [root log] (f/write-clean-marker! root {"sentexes" (- (.length (java.io.File. ^String log)) 40)}))]
                         ["past EOF — names a longer log than exists"
                          (fn [root log] (f/write-clean-marker! root {"sentexes" (+ (.length (java.io.File. ^String log)) 4096)}))]
                         ["absent — no marker at all"
                          (fn [root _] (f/remove-clean-marker! root))]]]
    (testing label
      (with-tmp
        (fn [dir]
          (let [s1 (drs/open-record-store dir)
                a  (p/put-sentex s1 {:sentence '(dog Muffet) :context 'C})]
            (drs/close! s1)
            (let [root (str dir "/records")
                  log  (str root "/sentexes.log")]
              (with-open [raf (RandomAccessFile. log "rw")]
                (.seek raf (.length raf))
                (.writeInt raf 999999)
                (.write raf (byte-array 8)))
              (forge root log)
              (let [s2 (drs/open-record-store dir)]
                (try
                  (is (= '(dog Muffet) (:sentence (p/get-sentex s2 a))) "the record did not survive")
                  (let [log-raf (f/open-log log)]
                    (is (= (f/log-length log-raf) (f/log-tail-offset log-raf))
                        "the torn tail survived — the marker was believed when it should not be")
                    (f/close! log-raf))
                  (finally (drs/close! s2)))))))))))

;; ---- the hot-record cache ------------------------------------------------
;; A record is an immutable value, so caching one is safe exactly as long as every path
;; that changes what lives at an id also changes the cache.  These are those paths.

(defn- cached
  "What the kind's LRU currently holds for `id` (white-box: the cache is what is being
  tested, so the test looks at it rather than inferring it from timings)."
  [store kind id]
  (some-> ^java.util.Map (:cache (kind (:kinds store))) (.get id)))

(deftest hot-cache-stays-consistent-with-the-store
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)]
        (try
          (let [a (p/put-sentex s {:sentence '(dog Muffet) :context 'C})
                b (p/put-justification s {:informant :rule :antecedents [a]})]
            (testing "a written record is cached, and a read returns the same value"
              (is (= '(dog Muffet) (:sentence (cached s :sentexes a))))
              (is (= (p/get-sentex s a) (cached s :sentexes a))))

            (testing "a read populates the cache, and matches a cache-bypassing frame read"
              (.clear ^java.util.Map (:cache (:sentexes (:kinds s))))
              (is (nil? (cached s :sentexes a)) "cleared")
              (let [via-store (p/get-sentex s a)
                    k         (:sentexes (:kinds s))
                    slot      (f/read-slot (:idx k) a)
                    via-file  (codec/decode-sentex (f/read-record (:log k) (:offset slot)))]
                (is (= via-store via-file) "the cached read equals the frame on disk")
                (is (= via-store (cached s :sentexes a)) "and the read populated the cache")))

            (testing "a re-store (mark-premise) replaces the cached record, not just the frame"
              (p/mark-premise s a :monotonic)
              (is (= :monotonic (:strength (cached s :sentexes a))))
              (is (= :monotonic (:strength (p/get-sentex s a))))
              (p/unmark-premise! s a)
              (is (nil? (:strength (p/get-sentex s a))) "and again on unmark"))

            (testing "a delete evicts — the cached record must not outlive its handle"
              (p/get-sentex s a)                              ; warm
              (is (some? (cached s :sentexes a)))
              (p/delete-sentex! s a)
              (is (nil? (cached s :sentexes a)) "evicted from the cache")
              (is (nil? (p/get-sentex s a)) "and gone from the store"))

            (testing "provenance rides the same paths, in its own cache"
              (p/put-provenance s b {:creator "t"})
              (is (= {:creator "t"} (cached s :provenance b)))
              (p/delete-justification! s b)
              (is (nil? (cached s :provenance b)))
              (is (nil? (p/get-provenance s b))))

            (testing "clear-records! empties every kind's cache"
              (let [c (p/put-sentex s {:sentence '(cat Tom) :context 'C})]
                (is (some? (cached s :sentexes c)))
                (p/clear-records! s)
                (is (nil? (cached s :sentexes c)))
                (is (nil? (p/get-sentex s c))))))
          (finally (drs/close! s)))))))

(deftest hot-cache-is-bounded-and-lru
  (with-tmp
    (fn [dir]
      ;; An explicit capacity, well under the load: at the `vaelii.disk.cache` default of
      ;; 65,536 a two-thousand-record load evicts nothing, so the bound and the eviction
      ;; order are both unobservable and every assertion below holds vacuously.
      (let [cap 100
            s   (drs/open-record-store dir {:cache-capacity cap})]
        (try
          ;; the cache is capacity-bounded, so a load larger than it must not grow the
          ;; heap without limit — and the survivors must be the recently used ones.
          (let [size0 (.size ^java.util.Map (:cache (:sentexes (:kinds s))))
                ids   (vec (for [i (range 2000)]
                             (p/put-sentex s {:sentence (list 'p (symbol (str "I" i))) :context 'C})))
                size  (.size ^java.util.Map (:cache (:sentexes (:kinds s))))]
            (is (zero? size0) "starts empty")
            (is (= cap size) "bounded by the configured capacity, whatever the load")
            (testing "and it is the recently used that survive"
              ;; the load left the last `cap` writes in it; the first are long gone
              (is (some? (cached s :sentexes (peek ids))) "the newest write is held")
              (is (nil? (cached s :sentexes (first ids))) "the oldest is not")
              ;; reading an evicted id re-admits it, which is what makes the order LRU
              ;; rather than a fixed window over the writes
              (p/get-sentex s (first ids))
              (is (some? (cached s :sentexes (first ids))) "a read promotes what it paged in")
              (is (= cap (.size ^java.util.Map (:cache (:sentexes (:kinds s)))))
                  "and the promotion evicted one rather than growing the map"))
            (testing "every id still reads correctly whether or not it is cached"
              (doseq [i (range 0 2000 137)]
                (is (= (list 'p (symbol (str "I" i))) (:sentence (p/get-sentex s (nth ids i))))))))
          (finally (drs/close! s)))))))

(deftest premise-strength-reads-the-slot-not-the-record
  ;; The strength rides bits 2..3 of the idx slot, so `premise-strength` — called once per
  ;; premise on every recover — answers off the 24 bytes the open walk already reads,
  ;; without paging the record for one keyword.  Proven white-box: with the hot-record
  ;; cache cold, a strength read must leave it cold, because a record fetch would populate
  ;; it (`hot-cache-stays-consistent-with-the-store` pins that a `get-sentex` caches).
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)
            a (p/put-sentex s {:sentence '(dog Muffet) :context 'C :strength :monotonic})
            b (p/put-sentex s {:sentence '(cat Tom) :context 'C :strength :default})]
        (testing "the strength comes off the slot; no frame is paged"
          (.clear ^java.util.Map (:cache (:sentexes (:kinds s))))
          (is (= :monotonic (p/premise-strength s a)))
          (is (= :default   (p/premise-strength s b)))
          (is (nil? (cached s :sentexes a)) "a's record stayed on disk")
          (is (nil? (cached s :sentexes b)) "and b's"))
        (drs/close! s))
      (testing "but a slot older than the strength bits falls back to the record"
        (strip-strength-flags! dir [1 2])                 ; keep the premise bit, drop the rank
        (let [s2 (drs/open-record-store dir)]
          (try
            (.clear ^java.util.Map (:cache (:sentexes (:kinds s2))))
            (is (= :monotonic (p/premise-strength s2 1)) "recovered from the record instead")
            (is (= :default   (p/premise-strength s2 2)))
            (is (some? (cached s2 :sentexes 1)) "which means it did page the record — the fallback")
            (finally (drs/close! s2))))))))

;; ---- tokenized bodies, end to end ---------------------------------------
;; The store-level half of what `disk_codec_test` checks on the codec: a tokenized frame
;; is only sound if the dictionary that decodes it is durable, so what matters here is a
;; real close → reopen, and a reopen that has *not* asked for tokenized writes.

(deftest tokenized-store-round-trips-across-a-restart
  (with-tmp
    (fn [dir]
      (let [s1 (drs/open-record-store dir {:tokenize? true})
            a  (p/put-sentex s1 {:sentence '(dog Muffet) :context 'C})
            b  (p/put-sentex s1 (sx/->LiteralSentex '(bornIn Tom 1970) 'CxWell nil :true :monotonic))
            r  (p/put-sentex s1 (sx/->RuleSentex '(implies (and (dog ?var0)) (mammal ?var0)) 'C nil
                                                 :true '[(dog ?var0)] '(mammal ?var0) :monotonic
                                                 '{?var0 ?x} :forward true nil nil))
            d  (p/put-justification s1 {:informant :rule :antecedents [a b]})]
        (testing "reads back in the same session"
          (is (= '(bornIn Tom 1970) (:sentence (p/get-sentex s1 b))))
          (is (= '[(dog ?var0)] (:antecedent (p/get-sentex s1 r)))))
        (drs/close! s1)

        (testing "and after a close → reopen, off a dictionary rebuilt from its log"
          (let [s2 (drs/open-record-store dir {:tokenize? true})]
            (try
              (is (= '(dog Muffet) (:sentence (p/get-sentex s2 a))))
              (is (= '(bornIn Tom 1970) (:sentence (p/get-sentex s2 b))))
              (is (= :monotonic (:strength (p/get-sentex s2 b))) "the premise strength too")
              (is (= #{b r} (p/premise-ids s2))
                  "so the derived premise set survives (both were stored with a :strength)")
              (let [rule (p/get-sentex s2 r)]
                (is (= '(mammal ?var0) (:consequent rule)))
                (is (vector? (:antecedent rule)))
                (is (= '{?var0 ?x} (:varmap rule)))
                (is (= :forward (:direction rule))))
              (is (= [a b] (:antecedents (p/get-justification s2 d))))
              (finally (drs/close! s2)))))

        (testing "a store that does NOT ask for tokenized writes still reads them"
          (let [s3 (drs/open-record-store dir {:tokenize? false})]
            (try
              (is (= '(bornIn Tom 1970) (:sentence (p/get-sentex s3 b))))
              ;; and what it writes from here is a plain positional frame, beside them
              (let [c (p/put-sentex s3 (sx/->LiteralSentex '(cat Tom) 'C nil :true nil))]
                (is (= '(cat Tom) (:sentence (p/get-sentex s3 c))))
                (is (= '(dog Muffet) (:sentence (p/get-sentex s3 a))) "the tokenized ones keep reading"))
              (finally (drs/close! s3)))))))))

(deftest a-wipe-empties-the-dictionary-too
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir {:tokenize? true})]
        (try
          (p/put-sentex s (sx/->LiteralSentex '(dog Muffet) 'C nil :true nil))
          (is (pos? (dtok/token-count (:dict s))))
          (p/clear-records! s)
          (is (zero? (dtok/token-count (:dict s)))
              "a wiped store must not carry its predecessor's vocabulary")
          ;; and it still works afterwards — ids restart from 0 against an empty log
          (let [h (p/put-sentex s (sx/->LiteralSentex '(cat Tom) 'C nil :true nil))]
            (is (= '(cat Tom) (:sentence (p/get-sentex s h)))))
          (finally (drs/close! s)))))))

(deftest a-record-citing-a-lost-token-is-tombstoned-on-open
  ;; The residual exposure of ordering the fsyncs rather than fsyncing per token: a
  ;; machine crash between ticks can leave the record log's tail ahead of the
  ;; dictionary's.  That is the same cross-file skew `validate-idx-tail!` repairs
  ;; between a log and its idx, and it is repaired the same way.
  (with-tmp
    (fn [dir]
      (let [tl (str dir "/records/tokens.log")
            s1 (drs/open-record-store dir {:tokenize? true})
            a  (p/put-sentex s1 (sx/->LiteralSentex '(dog Muffet) 'C nil :true nil))
            ;; the dictionary exactly as of `a` — every later token is `b`'s
            after-a (do (drs/fsync s1) (.length (java.io.File. tl)))
            b  (p/put-sentex s1 (sx/->LiteralSentex '(elephant Jumbo) 'CxZoo nil :true nil))]
        (drs/close! s1)
        (is (> (.length (java.io.File. tl)) after-a) "b introduced new vocabulary")
        ;; roll the dictionary back to that point: b's frame now cites ids that are gone
        (let [raf (java.io.RandomAccessFile. tl "rw")]
          (.setLength raf after-a)
          (.close raf))
        (let [s2 (drs/open-record-store dir {:tokenize? true})]
          (try
            (is (= #{a} (p/sentex-ids s2))
                "the undecodable record is tombstoned; the decodable one is untouched")
            (is (= '(dog Muffet) (:sentence (p/get-sentex s2 a))))
            (is (nil? (p/get-sentex s2 b)))
            ;; and the store is usable afterwards — new tokens continue from where the
            ;; rolled-back dictionary now ends
            (let [c (p/put-sentex s2 (sx/->LiteralSentex '(cat Tom) 'C nil :true nil))]
              (is (= '(cat Tom) (:sentence (p/get-sentex s2 c)))))
            (finally (drs/close! s2))))))))

(deftest an-idle-tick-does-not-rewrite-the-counters-blob
  ;; The durability daemon calls `fsync` every three seconds for the life of the process,
  ;; and persisting the handle counter is a temp file, an fsync of it, an ATOMIC_MOVE and
  ;; an fsync of the directory.  A KB nobody is writing to must not pay those four
  ;; operations a tick forever, so the blob is rewritten only when the counter moved.
  (with-tmp
    (fn [dir]
      (let [s    (drs/open-record-store dir)
            blob (java.io.File. (str dir "/records/counters.nippy"))]
        (try
          (p/put-sentex s {:sentence '(dog Muffet) :context 'C})
          (drs/fsync s)
          (is (.exists blob) "the tick after a write persists the counter")
          ;; deleting it is the observation, and an unambiguous one: an unconditional
          ;; write puts the file straight back, a guarded one leaves it absent because
          ;; there is nothing about the counter it does not already say
          (.delete blob)
          (dotimes [_ 5] (drs/fsync s))
          (is (not (.exists blob)) "five idle ticks rewrite nothing")
          (p/put-sentex s {:sentence '(cat Tom) :context 'C})
          (drs/fsync s)
          (is (.exists blob) "and the tick after the next write writes it again")
          (is (= 3 (:seq (f/read-nippy-file (.getPath blob) {:seq :missing})))
              "holding the counter as of that write")
          (finally (drs/close! s)))))))

(deftest a-slot-whose-frame-the-log-lost-is-dropped-by-a-compaction
  ;; A slot can outlive the frame it points at — the state a truncated tail leaves under a
  ;; slot the truncation did not reach — and the read then answers nil.  Re-freezing that
  ;; nil put the handle back as a **live** record fetching to nothing: an id `sentex-ids`
  ;; names and `get-sentex` has no answer for, which every walk over the ids trips on.
  (with-tmp
    (fn [dir]
      (let [s (drs/open-record-store dir)
            [a b c] (mapv (fn [n] (p/put-sentex s {:sentence (list 'p n) :context 'C
                                                   :strength :monotonic}))
                          [1 2 3])]
        (drs/close! s)
        ;; blank b's payload length, keeping its offset: the slot stays live (only
        ;; offset=-1, the tombstone, or an all-zero slot is dead) and no frame can be read
        ;; back through it, which is exactly what a lost frame looks like
        (with-open [idx (RandomAccessFile. (str dir "/records/sentexes.idx") "rw")]
          (let [slot (f/read-slot idx b)]
            (f/write-slot! idx b (:offset slot) 0 (:flags slot) 0)))
        (let [s2 (drs/open-record-store dir)]
          (try
            (is (contains? (p/sentex-ids s2) b) "the handle is live and its record is gone")
            (is (nil? (p/get-sentex s2 b)))
            (drs/compact! s2)
            (testing "the compaction drops the handle rather than storing it empty"
              (is (not (contains? (p/sentex-ids s2) b)))
              (is (nil? (p/get-sentex s2 b)))
              (is (not (contains? (set (p/premise-ids s2)) b))
                  "and it leaves the premise set with it"))
            (testing "its neighbours come through untouched"
              (is (= #{a c} (p/sentex-ids s2)))
              (is (= (list 'p 1) (:sentence (p/get-sentex s2 a))))
              (is (= (list 'p 3) (:sentence (p/get-sentex s2 c)))))
            (finally (drs/close! s2))))
        (testing "and the drop is what the next open reads"
          (let [s3 (drs/open-record-store dir)]
            (try (is (= #{a c} (p/sentex-ids s3)))
                 (finally (drs/close! s3)))))))))

(deftest the-live-roster-answers-beside-a-writer
  ;; The live-handle set is a `Roaring64Bitmap` mutated in place
  ;; (`vaelii.impl.roster`'s `LiveRoster`), which is what takes it from 45 bytes a handle
  ;; to about one bit.  What that costs is a monitor, and this is the claim the monitor
  ;; has to hold: the store supports readers beside its one writer
  ;; (`docs/storage.md`, the single-writer contract), and a bitmap read beside a
  ;; concurrent `addLong` is the one way this representation can answer garbage or throw
  ;; where the boxed set could not.  Every read is asserted, because they take the lock
  ;; separately: an enumeration, a tally, and a first handle.
  ;;
  ;; The hazard is a measured one rather than a caution.  An unsynchronized
  ;; `Roaring64Bitmap` under one adder and four readers throws
  ;; `ArrayIndexOutOfBoundsException` out of `getLongIterator` — in roughly one run in
  ;; five, and only once the keys are spread across enough 2^32 buckets that the ART trie
  ;; itself restructures, which is why a contiguous run never shows it and a store whose
  ;; handles interleave with two other kinds' would.
  (with-tmp
    (fn [dir]
      (let [s      (drs/open-record-store dir)
            n      2000
            stop   (atom false)
            errors (atom [])
            reader (fn [read!]
                     (future
                       (try
                         (loop [prev 0]
                           (if @stop
                             :done
                             (recur (long (or (read!) prev)))))
                         (catch Throwable t (swap! errors conj t) :failed))))]
        (try
          ;; one handle up front, so `a-sentex-id` has an answer from the first tick
          (p/put-sentex s {:sentence '(p 0) :context 'C})
          (let [ids   (reader #(count (p/sentex-ids s)))
                tally (reader #(cap/count-sentexes s))
                least (reader #(cap/some-sentex-id s))
                wrote (doall (for [i (range 1 (inc n))]
                               (p/put-sentex s {:sentence (list 'p i) :context 'C})))]
            (reset! stop true)
            (is (= [:done :done :done] [@ids @tally @least])
                "three readers ran the whole write through without throwing")
            (is (empty? @errors) (str "readers saw: " (mapv ex-message @errors)))
            (testing "and the store is exactly what the writer put in it"
              (is (= (inc n) (cap/count-sentexes s)))
              (is (= (set (cons 1 wrote)) (p/sentex-ids s)))))
          (testing "a first handle is the least live one, and follows a delete of it"
            (is (= 1 (cap/some-sentex-id s)))
            (p/delete-sentex! s 1)
            (is (= 2 (cap/some-sentex-id s)))
            (is (= n (cap/count-sentexes s)) "and the tally follows the delete too")
            (p/delete-sentex! s 1)
            (is (= n (cap/count-sentexes s)) "deleting a dead handle is a no-op")
            (p/delete-sentex! s :informant)
            (is (= n (cap/count-sentexes s))
                "and so is a non-handle, which `contains?` on the set it replaces answered"))
          (finally (drs/close! s)))))))
