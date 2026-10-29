;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-files-test
  "The disk substrate (`vaelii.impl.disk.files`) tested directly — the frame/slot
  primitives, torn-tail recovery, and the crash-safe compaction recovery branches the
  full suite never reaches because it never crashes mid-operation."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.disk.files :as f])
  (:import [java.io File]
           [java.nio.channels FileChannel]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-files-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (File. dir)))] (.delete ^File f)))

(defn- with-tmp [f]
  (let [dir (tmpdir)]
    (try (f dir) (finally (rm-rf! dir)))))

(defn- exists? [^String path] (.exists (File. path)))

;; ---- frames -------------------------------------------------------------

(deftest frames-round-trip-every-token-type
  (with-tmp
    (fn [dir]
      (let [log (f/open-log (str dir "/t.log"))
            vals [{:a 1 :sym 'foo :kw :bar}
                  #{1 2 3}
                  '(nested (list -7) "string")
                  [1.5 -3 0 :k 'S nil]
                  "a bare string"]
            offs (mapv #(f/append-record! log %) vals)]
        (testing "each value thaws back identical from its offset"
          (doseq [[o v] (map vector offs vals)]
            (is (= v (f/read-record log o)))))
        (is (nil? (f/read-record log -1)) "a negative offset reads nil")
        (is (nil? (f/read-record log (f/log-length log))) "an at-EOF offset reads nil")
        ;; `read-record-sized` is the hot path: a caller holding the slot already knows
        ;; the payload length, so it reads the payload alone — one positional read, with
        ;; neither a seek nor a re-read of the length prefix.  It must agree with
        ;; `read-record` frame for frame, or every paged record is subtly wrong.
        (testing "read-record-sized agrees with read-record on every frame"
          (loop [os offs, vs vals]
            (when (seq os)
              (let [o    (first os)
                    ;; the payload length is the next frame's offset (or EOF) minus
                    ;; this frame's offset and its 4-byte prefix — what a slot records
                    next (or (second os) (f/log-length log))
                    len  (- next o 4)]
                (is (= (first vs) (f/read-record-sized log o len)))
                (recur (rest os) (rest vs))))))
        (testing "and refuses what it cannot read rather than guessing"
          (is (nil? (f/read-record-sized log -1 10)) "a negative offset")
          (is (nil? (f/read-record-sized log 0 0))   "a zero length — no real frame is empty")
          (is (nil? (f/read-record-sized log (f/log-length log) 8)) "a payload past EOF"))
        (f/close! log)))))

;; ---- slots --------------------------------------------------------------

(deftest slots-read-write-tombstone-and-gaps
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 0 100 20 0 0)
        (f/write-slot! idx 5 200 30 0 0)          ; leaves 1..4 as a zero-filled gap
        (testing "written slots read back; gap slots read as nil"
          (is (= 100 (:offset (f/read-slot idx 0))))
          (is (= 30 (:length (f/read-slot idx 5))))
          (is (nil? (f/read-slot idx 2)) "a zero-filled gap reads as unwritten")
          (is (nil? (f/read-slot idx 99)) "past EOF reads as unwritten"))
        (testing "max-slot-id / slot-count reflect the high-water mark"
          (is (= 5 (f/max-slot-id idx)))
          (is (= 6 (f/slot-count idx))))
        (testing "a tombstone keeps its slot (so max-slot-id, hence next-id, is stable)"
          (f/tombstone-slot! idx 5)
          (is (:tombstone? (f/read-slot idx 5)))
          (is (= 5 (f/max-slot-id idx)) "tombstoning does not lower the high-water mark"))
        (f/close! idx)))))

(deftest scan-idx-yields-only-live-slots
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 0 10 5 0 0)
        (f/write-slot! idx 3 20 5 0 0)
        (f/write-slot! idx 7 30 5 (f/premise-flags true) 0)
        (f/tombstone-slot! idx 3)                 ; live: 0,7 ; gaps 1,2,4,5,6 ; tombstone 3
        (let [seen (atom [])]
          (f/scan-idx! idx (fn [id _ _ flags] (swap! seen conj [id flags])))
          (is (= #{0 7} (set (map first @seen))) "only live slots, no tombstones or gaps")
          (testing "the scan carries each slot's flags, so an open reads them once"
            (is (= {0 nil, 7 true} (into {} (map (fn [[id fl]] [id (f/slot-premise fl)]))
                                         @seen))
                "an unannotated slot says nothing; an annotated one says what it says")))
        (f/close! idx)))))

(deftest premise-flags-round-trip-through-a-slot
  (testing "the two bits: a slot says premise, says not-premise, or does not say"
    (is (= true  (f/slot-premise (f/premise-flags true))))
    (is (= false (f/slot-premise (f/premise-flags false))))
    (is (nil? (f/slot-premise 0))
        "0 — what every slot written before the bit existed holds — is unknown, not false"))
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 1 10 5 (f/premise-flags true) 0)
        (f/write-slot! idx 2 20 5 (f/premise-flags false) 0)
        (f/write-slot! idx 3 30 5 0 0)
        (is (= [true false nil]
               (map #(f/slot-premise (:flags (f/read-slot idx %))) [1 2 3])))
        (f/close! idx)))))

(deftest slot-strength-rides-the-premise-flags
  (testing "the rank rides bits 2..3 without disturbing what the premise bit says"
    (doseq [rank [0 1 2]]
      (is (= true (f/slot-premise (f/premise-flags true rank)))
          "a premise carrying any rank still decodes as a premise")
      (is (= rank (f/slot-strength (f/premise-flags true rank)))
          "and the rank reads back exactly"))
    (is (= 0 (f/slot-strength (f/premise-flags false 2)))
        "a non-premise carries no rank whatever it is handed")
    (is (= 0 (f/slot-strength 0))
        "a slot older than the strength bits reads rank 0 — which sends the caller to the record")
    (is (= 0 (f/slot-strength (f/premise-flags true)))
        "and so does a premise slot written with the 1-arg form"))
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 1 10 5 (f/premise-flags true 1) 0)   ; :default
        (f/write-slot! idx 2 20 5 (f/premise-flags true 2) 0)   ; :monotonic
        (f/write-slot! idx 3 30 5 (f/premise-flags false) 0)    ; not a premise
        (is (= [1 2 0] (map #(f/slot-strength (:flags (f/read-slot idx %))) [1 2 3]))
            "the ranks survive a slot write/read round-trip; the non-premise reads 0")
        (is (= [true true false] (map #(f/slot-premise (:flags (f/read-slot idx %))) [1 2 3]))
            "and the premise bit is unchanged by the ranks beside it")
        (f/close! idx)))))

(deftest reconcile-slot-flags-repairs-only-what-disagrees
  ;; The dirty-open repair: rewrite a slot whose flags would answer differently from its
  ;; record (a torn flags page), and leave alone one that agrees or falls back.
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (try
          (testing "a stale rank is rewritten to the record's, frame fields untouched"
            (f/write-slot! idx 1 100 20 (f/premise-flags true 1) 7)   ; slot says rank 1…
            (is (true? (f/reconcile-slot-flags! idx 1 true 2)))       ; …record is rank 2
            (let [s (f/read-slot idx 1)]
              (is (= 2 (f/slot-strength (:flags s))))
              (is (= [100 20 7] [(:offset s) (:length s) (:gen s)])
                  "only the flags word moved")))
          (testing "a stale premise bit is rewritten to match the record"
            (f/write-slot! idx 2 200 30 (f/premise-flags true 2) 0)   ; phantom premise…
            (is (true? (f/reconcile-slot-flags! idx 2 false 0)))      ; …record is not one
            (let [s (f/read-slot idx 2)]
              (is (false? (f/slot-premise (:flags s))))
              (is (zero?  (f/slot-strength (:flags s))) "phantom rank cleared too")))
          (testing "a slot that already agrees is left untouched"
            (f/write-slot! idx 3 300 10 (f/premise-flags true 2) 0)
            (is (nil? (f/reconcile-slot-flags! idx 3 true 2))))
          (testing "a silent (legacy) slot falls back to the record — consistent, not rewritten"
            (f/write-slot! idx 4 400 10 0 0)
            (is (nil? (f/reconcile-slot-flags! idx 4 true 2)))
            (is (zero? (f/slot-strength (:flags (f/read-slot idx 4)))) "left silent"))
          (testing "a premise slot with an unrecorded rank (0) also falls back — not rewritten"
            (f/write-slot! idx 5 500 10 (f/premise-flags true 0) 0)
            (is (nil? (f/reconcile-slot-flags! idx 5 true 2))))
          (testing "no slot, nothing to reconcile"
            (is (nil? (f/reconcile-slot-flags! idx 99 true 2))))
          (finally (f/close! idx)))))))

;; ---- log recovery -------------------------------------------------------

(deftest scan-log-finds-the-torn-tail
  (with-tmp
    (fn [dir]
      (let [path (str dir "/t.log")
            log  (f/open-log path)
            _    (f/append-record! log {:v 1})
            _    (f/append-record! log {:v 2})
            good-end (f/log-length log)]
        (.seek log (f/log-length log))
        (.writeInt log 999999)                    ; a prefix promising bytes never written
        (.write log (byte-array 8))
        (testing "scan-log returns the offset just past the last intact frame"
          (is (= good-end (f/scan-log log (fn [_ _] nil)))))
        (f/truncate-log! log (f/scan-log log (fn [_ _] nil)))
        (is (= good-end (f/log-length log)) "truncate-log! drops the torn tail")
        (f/close! log)))))

;; ---- an append is all or nothing ---------------------------------------
;; A write that fails partway (`ENOSPC`, an I/O error) must not leave a frame whose
;; prefix promises bytes that never landed: the session would append past it, and the
;; next dirty open's length walk would step from that prefix into the middle of a later
;; frame and truncate everything after it.  The failure is injected under the private
;; write primitive, which is the one boundary between the packed frame and the channel.

(defn- failing-after
  "A stand-in for `write-fully-at!` that lands the first `k` bytes of the buffer and
  then throws `t`, an `IOException` by default — a torn write."
  ([k] (failing-after k (java.io.IOException. "no space left on device")))
  ([k ^Throwable t]
   (fn [^java.nio.channels.FileChannel ch ^java.nio.ByteBuffer bb ^long pos]
     (let [head (java.nio.ByteBuffer/wrap (byte-array (take k (.array bb))))]
       (.write ch head pos)
       (throw t)))))

(deftest a-torn-append-leaves-the-log-as-it-was
  (with-tmp
    (fn [dir]
      (let [log  (f/open-log (str dir "/t.log"))
            _    (f/append-record! log {:v 1})
            before (f/log-length log)]
        (testing "a single record"
          (with-redefs [f/write-fully-at! (failing-after 3)]
            (is (thrown? java.io.IOException (f/append-record! log {:v :lost}))))
          (is (= before (f/log-length log)) "the log is set back to its pre-write length"))
        (testing "a batch"
          (with-redefs [f/write-fully-at! (failing-after 9)]
            (is (thrown? java.io.IOException (f/append-records! log [[:put :a 1] [:put :b 2]]))))
          (is (= before (f/log-length log)) "none of the batch is on disk"))
        (testing "an OutOfMemoryError part-way through a record"
          (with-redefs [f/write-fully-at! (failing-after 3 (OutOfMemoryError. "heap"))]
            (is (thrown? OutOfMemoryError (f/append-record! log {:v :lost}))))
          (is (= before (f/log-length log))))
        (testing "the log is appendable and walkable afterwards"
          (let [off (f/append-record! log {:v 2})]
            (is (= before off) "the next frame lands where the torn one was rolled back from")
            (is (= {:v 2} (f/read-record log off)))
            (is (= (f/log-length log) (f/log-tail-offset log))
                "the length walk reaches the end — no torn frame is left mid-log")))
        (f/close! log)))))

(deftest a-batch-appends-every-frame-in-order
  (with-tmp
    (fn [dir]
      (let [log (f/open-log (str dir "/t.log"))
            ops [[:put :a 1] [:add-to-set :s 7] [:increment :c] [:delete :a]]
            off (f/append-records! log ops)
            seen (atom [])]
        (is (zero? off) "the batch lands at the log's end, returning the first frame's offset")
        (f/scan-log log (fn [_ v] (swap! seen conj v)))
        (is (= ops @seen) "one frame per op, in order — the replay reads them as single appends")
        (is (= (f/log-length log) (f/append-records! log [])) "an empty batch writes nothing")
        (f/close! log)))))

;; ---- the length-only tail walk ------------------------------------------
;; `log-tail-offset` is what the open path uses instead of `scan-log`.  It must agree
;; with `scan-log` wherever `scan-log` was right, and it must keep working where
;; `scan-log` could not: on a log this build cannot decode.

(defn- append-raw-frame!
  "Append `[len][payload]` directly — a frame whose bytes we choose, so a test can write
  one no thaw would accept."
  [^java.io.RandomAccessFile log ^bytes payload]
  (.seek log (f/log-length log))
  (.writeInt log (alength payload))
  (.write log payload))

(deftest the-length-walk-agrees-with-the-decoding-scan
  ;; The claim the substitution rests on.  Not "it works" — the same answer, case by
  ;; case, including the shapes the open path actually meets.
  (with-tmp
    (fn [dir]
      (doseq [[label build!]
              [["an empty log" (fn [_] nil)]
               ["one frame" (fn [log] (f/append-record! log {:v 1}))]
               ["many frames" (fn [log] (dotimes [i 500] (f/append-record! log {:v i :pad (range 20)})))]
               ["a frame larger than the read buffer"
                (fn [log] (f/append-record! log {:big (vec (range 40000))})
                  (f/append-record! log {:v :after}))]]]
        (testing label
          (let [path (str dir "/" (hash label) ".log")
                log  (f/open-log path)]
            (build! log)
            (is (= (f/scan-log log (fn [_ _] nil)) (f/log-tail-offset log))
                "the walk and the decoding scan disagree")
            (f/close! log)))))))

(deftest the-length-walk-finds-the-same-torn-tail
  (with-tmp
    (fn [dir]
      (doseq [[label tear!]
              [["a prefix promising bytes never written"
                (fn [^java.io.RandomAccessFile log]
                  (.writeInt log 999999) (.write log (byte-array 8)))]
               ["a half-written prefix"
                (fn [^java.io.RandomAccessFile log] (.write log (byte-array 2)))]
               ["a zero-filled tail — a prefix that was never written at all"
                (fn [^java.io.RandomAccessFile log] (.write log (byte-array 4096)))]]]
        (testing label
          (let [path     (str dir "/" (hash label) ".log")
                log      (f/open-log path)
                _        (f/append-record! log {:v 1})
                _        (f/append-record! log {:v 2})
                good-end (f/log-length log)]
            (.seek log (f/log-length log))
            (tear! log)
            (is (= good-end (f/log-tail-offset log)) "the walk mislocated the tear")
            (is (= good-end (f/scan-log log (fn [_ _] nil)))
                "and the decoding scan agrees, so the substitution loses nothing")
            (f/close! log)))))))

(deftest a-log-this-build-cannot-decode-still-opens
  ;; The failure that motivated this: a record class rename made every frame undecodable,
  ;; and the open path — whose only question was how long the log is — raised one
  ;; exception per frame and then truncated the whole log at the first.  The walk never
  ;; thaws, so an undecodable log has an undecodable *record* and an intact length chain.
  (with-tmp
    (fn [dir]
      (let [path (str dir "/opaque.log")
            log  (f/open-log path)]
        (dotimes [i 30] (append-raw-frame! log (.getBytes (str "not-nippy-" i) "UTF-8")))
        (let [full (f/log-length log)]
          (is (= full (f/log-tail-offset log))
              "the walk truncated a log whose frames are merely undecodable")
          (let [e (is (thrown? clojure.lang.ExceptionInfo (f/scan-log log path (fn [_ _] nil))))]
            (is (= {:type :damaged-frame :path path :offset 0 :frame 0}
                   (select-keys (ex-data e) [:type :path :offset :frame]))
                "and the decoding scan refuses at the first frame rather than reading the log as empty")))
        (f/close! log)))))

;; ---- a frame that does not thaw ------------------------------------------
;; The decoding scan stops where the length chain stops.  A frame inside the chain that
;; does not thaw is damage when frames follow it and a torn tail when none do: stopping
;; at a damaged frame as though the log ended there drops every frame after it, and a
;; caller rebuilding state from the log (the token dictionary) loses all of them.

(defn- zero-payload!
  "Zero the first two payload bytes of the frame whose prefix is at `offset`, leaving its
  length prefix intact."
  [^java.io.RandomAccessFile log ^long offset]
  (.seek log (+ offset 4))
  (.write log (byte-array 2)))

(deftest a-frame-that-does-not-thaw-mid-log-is-refused-by-name
  (with-tmp
    (fn [dir]
      (let [path (str dir "/t.log")
            log  (f/open-log path)
            offs (mapv #(f/append-record! log {:v %}) (range 10))
            seen (atom [])]
        (zero-payload! log (offs 7))
        (let [len (f/log-length log)
              e   (is (thrown? clojure.lang.ExceptionInfo
                               (f/scan-log log path (fn [_ v] (swap! seen conj v)))))]
          (is (= {:type :damaged-frame :path path :offset (offs 7) :frame 7}
                 (select-keys (ex-data e) [:type :path :offset :frame]))
              "the refusal names the file, the byte offset and the frame")
          (is (some? (ex-cause e)) "and carries the thaw's own exception")
          (is (= len (f/log-length log)) "the scan leaves the file as it found it"))
        (is (= (mapv (fn [i] {:v i}) (range 7)) @seen) "the frames before it were read")
        (f/close! log)))))

(deftest a-last-frame-that-does-not-thaw-is-a-torn-tail
  (with-tmp
    (fn [dir]
      (let [path (str dir "/t.log")
            log  (f/open-log path)
            offs (mapv #(f/append-record! log {:v %}) (range 4))]
        (zero-payload! log (offs 3))
        (is (= (offs 3) (f/scan-log log path (fn [_ _] nil)))
            "the scan stops at the last frame's offset, the point a caller truncates to")
        (testing "a zero-filled region after it ends the chain there too"
          (.seek log (f/log-length log))
          (.write log (byte-array 64))
          (is (= (offs 3) (f/scan-log log path (fn [_ _] nil)))))
        (f/close! log)))))

(deftest an-error-thrown-inside-a-thaw-is-not-a-verdict-on-the-frame
  ;; An `OutOfMemoryError` inside one thaw said nothing about the frame; read as a torn
  ;; tail, it cut the token dictionary short and the open tombstoned every record citing
  ;; a later token.
  (with-tmp
    (fn [dir]
      (let [log  (f/open-log (str dir "/t.log"))
            _    (dotimes [i 10] (f/append-record! log {:v i}))
            thaw @#'f/thaw-bytes
            n    (atom 0)]
        (with-redefs [f/thaw-bytes (fn [bs] (if (= 5 (swap! n inc))
                                              (throw (OutOfMemoryError. "witness"))
                                              (thaw bs)))]
          (is (thrown? OutOfMemoryError (f/scan-log log (fn [_ _] nil)))))
        (is (= (f/log-length log) (f/scan-log log (fn [_ _] nil)))
            "and the log reads whole once the thaw can finish")
        (f/close! log)))))

;; ---- the clean-shutdown marker ------------------------------------------

(deftest the-clean-marker-is-believed-only-when-the-length-still-agrees
  (with-tmp
    (fn [dir]
      (let [path (str dir "/c.log")
            log  (f/open-log path)
            _    (dotimes [i 10] (f/append-record! log {:v i}))
            len  (f/log-length log)]
        (testing "a matching length skips the walk"
          (is (= [len false] (f/log-tail-offset-from log len))))
        (testing "every disagreement falls back to the walk"
          (doseq [[label recorded] [["absent"       nil]
                                    ["stale/short"  (- len 40)]
                                    ["past EOF"     (+ len 4096)]
                                    ["not a number" :garbage]]]
            (is (= [len true] (f/log-tail-offset-from log recorded)) (str "marker " label))))
        (testing "and the fallback is still correct when there is a real tear"
          (.seek ^java.io.RandomAccessFile log (f/log-length log))
          (.writeInt ^java.io.RandomAccessFile log 999999)
          (is (= [len true] (f/log-tail-offset-from log (+ len 999999)))
              "a marker longer than the log must not be believed"))
        (f/close! log))))
  (with-tmp
    (fn [dir]
      (testing "write / read / remove round-trips, and a missing marker reads nil"
        (is (nil? (f/read-clean-marker dir)))
        (f/write-clean-marker! dir {"sentexes" 12 "kv" 34})
        (is (= {"sentexes" 12 "kv" 34} (f/read-clean-marker dir)))
        (f/remove-clean-marker! dir)
        (is (nil? (f/read-clean-marker dir)))))))

(deftest validate-idx-tail-tombstones-slots-past-eof
  (with-tmp
    (fn [dir]
      (let [log (f/open-log (str dir "/t.log"))
            idx (f/open-idx (str dir "/t.idx"))
            o0  (f/append-record! log {:v 1})]
        (f/write-slot! idx 0 o0 (- (f/log-length log) o0 4) 0 0)   ; valid
        (f/write-slot! idx 1 (+ (f/log-length log) 1000) 50 0 0)   ; frame past EOF
        (is (= 1 (f/validate-idx-tail! idx log)))
        (is (some? (f/read-slot idx 0)) "the valid slot is untouched")
        (is (:tombstone? (f/read-slot idx 1)) "the past-EOF slot is tombstoned")
        (f/close! log) (f/close! idx)))))

;; ---- crash-safe compaction: the (log, idx) pair -------------------------

(defn- write-one-record! [log-path idx-path v]
  (let [log (f/open-log log-path)
        idx (f/open-idx idx-path)
        o   (f/append-record! log v)]
    (f/write-slot! idx 0 o (- (f/log-length log) o 4) 0 0)
    (f/close! log) (f/close! idx)))

(defn- slot0 [log-path idx-path]
  (let [log (f/open-log log-path)
        idx (f/open-idx idx-path)
        v   (f/read-record log (:offset (f/read-slot idx 0)))]
    (f/close! log) (f/close! idx)
    v))

(deftest recover-compaction-replays-a-committed-crash
  (with-tmp
    (fn [dir]
      (let [lp (str dir "/x.log") ip (str dir "/x.idx")
            {:keys [temps marker]} (f/compact-temp-paths lp ip)
            [[_ log-tmp] [_ idx-tmp]] temps]
        (write-one-record! lp ip {:v :orig})            ; the original (pre-compaction) content
        (write-one-record! log-tmp idx-tmp {:v :compacted})  ; the finished compaction temps
        (f/write-commit-marker! marker {:log lp})       ; commit point crossed, then "crash"
        (testing "a marker + both temps present ⇒ finish the compaction on recovery"
          (is (= :replayed (f/recover-compaction! lp ip)))
          (is (= {:v :compacted} (slot0 lp ip)) "the compacted content replaced the original")
          (is (not (exists? marker)) "temps + marker cleaned up")
          (is (not (exists? log-tmp))))))))

(deftest recover-compaction-keeps-originals-when-not-committed
  (with-tmp
    (fn [dir]
      (testing "temps present but NO marker (crashed before commit) ⇒ drop temps, keep original"
        (let [lp (str dir "/a.log") ip (str dir "/a.idx")
              [[_ log-tmp] [_ idx-tmp]] (:temps (f/compact-temp-paths lp ip))]
          (write-one-record! lp ip {:v :orig})
          (write-one-record! log-tmp idx-tmp {:v :half})
          (is (= :discarded-incomplete (f/recover-compaction! lp ip)))
          (is (= {:v :orig} (slot0 lp ip)) "the original is authoritative")
          (is (not (exists? log-tmp)) "the orphan temp is removed")))
      (testing "marker present but a temp missing (deeper damage) ⇒ keep originals"
        (let [lp (str dir "/b.log") ip (str dir "/b.idx")
              {:keys [marker]} (f/compact-temp-paths lp ip)]
          (write-one-record! lp ip {:v :orig})
          (f/write-commit-marker! marker {:log lp})       ; marker but no temps
          (is (= :discarded-incomplete (f/recover-compaction! lp ip)))
          (is (= {:v :orig} (slot0 lp ip)))
          (is (not (exists? marker)))))
      (testing "nothing pending ⇒ :none"
        (let [lp (str dir "/c.log") ip (str dir "/c.idx")]
          (write-one-record! lp ip {:v :orig})
          (is (= :none (f/recover-compaction! lp ip))))))))

;; ---- crash-safe compaction: one target rather than two (the KV WAL) -----
;; The same family, handed a single log: `compact-temp-paths` and `recover-compaction!`
;; are variadic in their targets, so the KV backend's one-file compaction and a record
;; kind's (log, idx) pair take the same three branches through the same code.

(deftest recover-compaction-branches-over-a-single-target
  (with-tmp
    (fn [dir]
      (testing "committed (marker + temp) ⇒ replay the temp onto the log"
        (let [lp (str dir "/w.log")
              {:keys [temps marker]} (f/compact-temp-paths lp)
              [[_ tmp]] temps]
          (let [log (f/open-log lp)] (f/append-record! log {:v :orig}) (f/close! log))
          (let [t (f/open-log tmp)] (f/append-record! t {:v :compacted}) (f/close! t))
          (f/write-commit-marker! marker {:log lp})
          (is (= :replayed (f/recover-compaction! lp)))
          (let [log (f/open-log lp)]
            (is (= {:v :compacted} (f/read-record log 0)))
            (f/close! log))
          (is (not (exists? tmp)))
          (is (not (exists? marker)))))
      (testing "temp only (crashed before commit) ⇒ drop the temp, keep the log"
        (let [lp (str dir "/w2.log")
              [[_ tmp]] (:temps (f/compact-temp-paths lp))]
          (let [log (f/open-log lp)] (f/append-record! log {:v :orig}) (f/close! log))
          (let [t (f/open-log tmp)] (f/append-record! t {:v :half}) (f/close! t))
          (is (= :discarded-incomplete (f/recover-compaction! lp)))
          (is (not (exists? tmp)))
          (let [log (f/open-log lp)]
            (is (= {:v :orig} (f/read-record log 0)))
            (f/close! log))))
      (testing "marker but no temp ⇒ discard the partial state and keep the log"
        (let [lp (str dir "/w4.log")
              {:keys [marker]} (f/compact-temp-paths lp)]
          (let [log (f/open-log lp)] (f/append-record! log {:v :orig}) (f/close! log))
          (f/write-commit-marker! marker {:log lp})
          (is (= :discarded-incomplete (f/recover-compaction! lp)))
          (is (not (exists? marker)))
          (let [log (f/open-log lp)]
            (is (= {:v :orig} (f/read-record log 0)))
            (f/close! log))))
      (testing "clean ⇒ :none"
        (is (= :none (f/recover-compaction! (str dir "/w3.log"))))))))

(deftest a-transfer-that-moves-nothing-is-refused-rather-than-called-done
  ;; The post-marker install copies the finished temp over the original, so at that moment
  ;; the temp is the only whole copy of the file.  `transferFrom` is documented as free to
  ;; return 0 with bytes still outstanding, and a loop that took that for the end would
  ;; leave a truncated file where the original was and report a finished compaction.  The
  ;; throw is what lets the compaction paths retry and then mark the store failed.
  ;;
  ;; The stalling channel is a `proxy` rather than a staged disk: a real `transferFrom`
  ;; returning 0 is a kernel condition no test can arrange, and the destination is the one
  ;; boundary where a stand-in answers exactly the two calls the copy makes.
  (with-tmp
    (fn [dir]
      (let [src     (str dir "/src.bin")
            _       (spit src "the bytes the install owes the original")
            stalled (proxy [FileChannel] []
                      (truncate [_n] this)
                      (transferFrom [_src _pos _count] 0)
                      (implCloseChannel [] nil))
            e       (is (thrown? clojure.lang.ExceptionInfo
                                 (#'f/copy-into-channel! stalled src)))]
        (is (= :short-transfer (:type (ex-data e))))
        (is (= src (:path (ex-data e))) "naming the file whose copy stalled")
        (is (= 0 (:copied (ex-data e))))
        (is (= (.length (File. src)) (:total (ex-data e)))
            "and how many bytes it owed")))))

;; ---- whole-blob metadata + markers --------------------------------------

(deftest nippy-blob-round-trip-and-fallbacks
  (with-tmp
    (fn [dir]
      (let [p (str dir "/meta.nippy")]
        (f/write-nippy-atomic! p {:seq 42 :prem #{1 2 3}})
        (is (= {:seq 42 :prem #{1 2 3}} (f/read-nippy-file p)))
        (f/write-nippy-atomic! p {:seq 43})               ; atomic overwrite
        (is (= {:seq 43} (f/read-nippy-file p)))
        (is (= :default (f/read-nippy-file (str dir "/missing.nippy") :default)))
        (testing "every truncation of a blob falls back to the default rather than throwing"
          ;; a torn write leaves a prefix; arbitrary bytes can decode a count of any size
          ;; and allocate for it, which the read rethrows rather than defaults
          (let [bs  (java.nio.file.Files/readAllBytes (.toPath (File. ^String p)))
                bad (str dir "/bad.nippy")]
            (is (= [] (into [] (remove (fn [n]
                                         (with-open [o (java.io.FileOutputStream. ^String bad)]
                                           (.write o ^bytes bs 0 (int n)))
                                         (= :default (f/read-nippy-file bad :default))))
                            (range 1 (count bs)))))))))))

(deftest dirty-marker-lifecycle
  (with-tmp
    (fn [dir]
      (is (not (f/dirty-marker-present? dir)))
      (f/create-dirty-marker! dir)
      (is (f/dirty-marker-present? dir) "present after a crash-y open")
      (f/remove-dirty-marker! dir)
      (is (not (f/dirty-marker-present? dir)) "gone after a clean close"))))

(deftest assert-format-adopts-then-guards
  (with-tmp
    (fn [dir]
      (f/ensure-dir! dir)
      (f/assert-format! dir)                              ; writes format.edn
      (is (.exists (File. ^String dir "format.edn")))
      (f/assert-format! dir)                              ; a known version re-opens fine
      (testing "an unknown future version is refused with a clean error"
        (spit (File. ^String dir "format.edn") (pr-str {:format-version 999}))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                              (f/assert-format! dir)))))))

(deftest a-manifest-write-cut-mid-write-leaves-a-readable-manifest
  ;; the cut is a `spit` that writes half its content and throws, the torn file a plain
  ;; write leaves at a crash; each manifest then holds the old content or the new one
  (with-tmp
    (fn [dir]
      (f/write-reasoners! dir #{"a"})
      (f/write-records-identity! dir {:kind :one})
      (f/write-index-layout! dir 1)
      (with-redefs [spit (fn [p ^String s & _]
                           (with-open [o (java.io.FileOutputStream. (str p))]
                             (.write o (.getBytes (subs s 0 (quot (count s) 2)))))
                           (throw (java.io.IOException. "cut")))]
        (doseq [w [#(f/write-reasoners! dir #{"a" "b"})
                   #(f/write-records-identity! dir {:kind :two})
                   #(f/write-index-layout! dir 2)]]
          (try (w) (catch java.io.IOException _ nil))))
      (is (contains? #{#{"a"} #{"a" "b"}} (f/recorded-reasoners dir)))
      (is (contains? #{{:kind :one} {:kind :two}} (f/records-identity dir)))
      (is (= :current (f/index-layout-decision dir 2 true))))))
