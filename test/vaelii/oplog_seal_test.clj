;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.oplog-seal-test
  "Seals and restores (`vaelii.impl.seal`).  A `:disk-snapshot` KB attached to an
  operation log is sealed, takes writes, and its directory is copied as a crash would
  leave it; a restore over the copy replays the log to the belief a recover of the same
  records computes.  A frame whose replay writes a different record, a frame lost after
  its records reached the disk, and an unusable log each decline the restore.  A
  `:seal`-class operation seals when it returns, a KB whose network does not cover its
  records cannot be sealed, and closing the directory seals it."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.seal :as seal]
            [vaelii.impl.solve :as solve]
            [vaelii.test-util :as tu])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files StandardCopyOption]))

(defn- copy-dir!
  "Copy `from` into `to` as the files stand: the contents a crash leaves of a directory
  whose store is still open."
  [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        ;; A store still open on `from` renames a temp file away between the listing and
        ;; the copy (the durability daemon's `counters.nippy` write), and a file gone by
        ;; then is one the directory no longer holds.
        (try
          (Files/copy (.toPath f) (.toPath t)
                      ^"[Ljava.nio.file.CopyOption;"
                      (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))
          (catch java.nio.file.NoSuchFileException _ nil))))))

(defn- open
  ([dir] (open dir nil))
  ([dir opts] (v/open-kb (merge {:backend :disk-snapshot :dir dir} opts))))

(defn- write-world!
  "A forward rule, three facts it fires on, a retraction of one, and a fourth fact, all
  through `kb`.  Six operations."
  [kb]
  (v/assert kb '(set/forwardRule (implies (and (animal ?x)) (mortal ?x))) 'CxUniverse)
  (let [hs (mapv #(v/assert kb (list 'animal %) 'CxUniverse) '[Socrates Plato Aristotle])]
    (v/retract! kb (second hs))
    (v/assert kb '(animal Zeno) 'CxUniverse)))

(defn- belief
  "Handle -> believed?, over every sentex `kb`'s records hold."
  [kb]
  (into (sorted-map)
        (map (fn [h] [h (v/believed? kb h)]))
        (p/sentex-ids (oplog/inner-records (:records kb)))))

(defn- log-path ^String [dir] (str dir "/oplog/ops.log"))

(defn- rewrite-log!
  "Replace the operation frames of `dir`'s log with `(f frames)`, keeping its header."
  [dir f]
  (let [path   (log-path dir)
        frames (with-open [raf (RandomAccessFile. path "r")]
                 (let [acc (transient [])]
                   (f/scan-log raf (fn [_ v] (conj! acc v)))
                   (persistent! acc)))]
    (with-open [raf (f/open-log path)]
      (.setLength raf 0)
      (doseq [fr (cons (first frames) (f (vec (rest frames))))]
        (f/append-record! raf fr)))))

(defn- restore-copy
  "Copy `src` to a fresh directory, open it `{:recover? false}` and restore it.  Calls
  `(check r)` with the restore's result, then closes whatever it opened and removes the
  copy.  `(edit dir)` runs on the copy before the open."
  ([src check] (restore-copy src identity check))
  ([src edit check]
   (let [dir (tu/tmpdir "vaelii-seal-")]
     (try
       (copy-dir! src dir)
       (edit dir)
       (let [kb (open dir {:recover? false})
             r  (seal/restore! kb)]
         (try (check r)
              (finally (v/close! (or (:kb r) kb)))))
       (finally (tu/rm-rf! dir))))))

(deftest a-restore-replays-to-the-belief-a-recover-computes
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") c (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (copy-dir! a c)
            (let [kb-c (open c)]
              (try
                (restore-copy a (fn [r]
                                  (is (:restored r))
                                  (is (= 6 (:frames r)))
                                  (is (= (belief kb-c) (belief (:kb r)))
                                      "the restored KB believes what a recover of its records believes")))
                (finally (v/close! kb-c))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a) (tu/rm-rf! c))))))

(deftest a-replayed-write-that-differs-from-the-store-declines
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (restore-copy a
                          #(rewrite-log! % (fn [ops]
                                             (mapv (fn [fr]
                                                     (if (= '(animal Zeno) (first (:args fr)))
                                                       (assoc fr :args ['(animal Heraclitus) 'CxUniverse])
                                                       fr))
                                                   ops)))
                          (fn [r]
                            (is (not (:restored r)))
                            (is (= :diverged (first (:reason r))))
                            (is (false? (:clean? r)) "replayed state is in the KB")))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest a-frame-lost-after-its-records-reached-the-disk-declines
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (restore-copy a
                          #(rewrite-log! % (fn [ops] (vec (butlast ops))))
                          (fn [r]
                            (is (not (:restored r)))
                            (is (= :extra-records (:reason r))
                                "the last assert's records sit above every handle the replay allocated")))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest a-frame-that-fails-rather-than-refuses-stops-the-restore
  (tu/with-snapshot-platform
    ;; A frame that refused when it was made refuses again, and replay goes on.  A frame
    ;; that throws something else did not refuse: skipped, it restored a KB missing the
    ;; write — here the retraction, so `(animal Plato)` came back believed — and answered
    ;; `:restored true`.
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (let [dir (tu/tmpdir "vaelii-seal-")]
              (try
                (copy-dir! a dir)
                (let [kb (open dir {:recover? false})]
                  (try
                    (is (thrown? OutOfMemoryError
                                 (with-redefs [v/retract! (fn [& _] (throw (OutOfMemoryError. "witness")))]
                                   (seal/restore! kb))))
                    (finally (v/close! kb))))
                (finally (tu/rm-rf! dir))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest an-unusable-log-declines
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (v/assert lkb '(animal Socrates) 'CxUniverse)
            (v/set-solver lkb solve/local-solver)
            (restore-copy a (fn [r]
                              (is (not (:restored r)))
                              (is (= [:unusable [:config :set-solver]] (:reason r)))
                              (is (:clean? r))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest a-replayed-write-runs-to-its-end-over-a-nearly-full-heap
  ;; The log after the seal holds the rows' writes: one `forward-chain` frame over three
  ;; facts stored before the seal, three asserts each chaining the forward rule inside a
  ;; rollback scope, or one `bulk-assert-facts!` frame.  The heap mark holds through the
  ;; restore, and the replay stores what the logged writes stored.
  (doseq [[how write! frames mortal]
          [[:forward-chain #(is (= 3 (:derived (v/forward-chain %)))) 1 3]
           [:assert #(doseq [x '[Socrates Plato Aristotle]]
                       (v/assert % (list 'animal x) 'CxUniverse))
            3 3]
           [:bulk-assert-facts! #(v/bulk-assert-facts! % '[(animal Socrates) (animal Plato)
                                                           (animal Aristotle)]
                                                       'CxUniverse)
            1 0]]]
    (tu/with-snapshot-platform
      (let [a (tu/tmpdir "vaelii-seal-")]
        (try
          (let [lkb (seal/attach! (open a))]
            (try
              (when (= :forward-chain how)
                (doseq [x '[Socrates Plato Aristotle]]
                  (v/assert lkb (list 'animal x) 'CxUniverse)))
              (v/assert lkb '(set/forwardRule (implies (and (animal ?x)) (mortal ?x))) 'CxUniverse
                        {:chain? (not= :forward-chain how)})
              (v/seal lkb)
              (write! lkb)
              (with-redefs [caches/heap-critical? (constantly true)]
                (restore-copy a (fn [r]
                                  (is (= [true frames] ((juxt :restored :frames) r))
                                      (str (name how) " " (pr-str (:reason r))))
                                  (is (= [3 mortal]
                                         (map #(count (some-> (:kb r) (v/sentexes-with-functor % {:believed? true})))
                                              '[animal mortal]))
                                      (name how)))))
              (finally (v/close! lkb))))
          (finally (tu/rm-rf! a)))))))

(deftest a-log-with-a-damaged-frame-inside-it-declines
  (tu/with-snapshot-platform
    ;; A frame that does not thaw with frames after it ends what can be replayed.  Read as a
    ;; torn tail, the log was cut there and the frames before it replayed: here the two
    ;; retractions were lost, the replay rewrote both records, and the restore answered
    ;; `:restored true` with `(animal Plato)` believed.  A retraction allocates no handle,
    ;; so the extra-records check has nothing to find.
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (let [hs (mapv #(v/assert lkb (list 'animal %) 'CxUniverse) '[Socrates Plato Aristotle])]
              (v/retract! lkb (hs 1))
              (v/retract! lkb (hs 2)))
            (let [offset (atom nil)]
              (restore-copy a
                            (fn [dir]
                              ;; frame 0 is the header, 1-3 the asserts, 4 the first retraction
                              (with-open [raf (RandomAccessFile. (log-path dir) "rw")]
                                (let [off (loop [pos 0 k 0]
                                            (if (= k 4)
                                              pos
                                              (do (.seek raf pos)
                                                  (recur (+ pos 4 (.readInt raf)) (inc k)))))]
                                  (reset! offset off)
                                  (.seek raf (+ off 4))
                                  (.write raf (byte-array 2)))))
                            (fn [r]
                              (is (not (:restored r)))
                              (is (= [:unusable [:damaged-frame @offset]] (:reason r)))
                              (is (:clean? r)))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest a-seal-class-operation-seals-when-it-returns
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") txt (tu/tmpdir "vaelii-seal-")]
      (try
        (spit (io/file txt "CxUniverse.txt") "(animal Socrates)\n(animal Plato)\n")
        (let [lkb (seal/attach! (open a))
              g   (:generation (seal/read-seal a))]
          (try
            (v/assert lkb '(animal Zeno) 'CxUniverse)
            (v/load-text! lkb txt)
            (is (= (inc (long g)) (:generation (seal/read-seal a))))
            (is (nil? (oplog/unusable (:oplog lkb))) "the seal starts the log again")
            (is (empty? (oplog/read-frames (:oplog lkb))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a) (tu/rm-rf! txt))))))

(deftest a-kb-whose-network-does-not-cover-its-records-is-not-sealed
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))
              g   (:generation (seal/read-seal a))]
          (try
            (v/assert lkb '(animal Zeno) 'CxUniverse)
            ;; `clear!` wipes the records and leaves the network's nodes, so the seal it
            ;; requests is refused
            (v/clear! lkb)
            (is (= [:seal :clear] (oplog/unusable (:oplog lkb)))
                "the refused seal leaves the mark the operation made")
            (is (= g (:generation (seal/read-seal a))) "and starts no generation")
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest a-seal-class-operation-fsyncs-its-unusable-mark-before-it-writes-a-record
  ;; a machine crash that keeps the records' deletes and loses an unsynced mark leaves a
  ;; usable log over records its seal does not describe.  The events are this thread's
  ;; and this log's, so a durability tick's fsync is not counted.
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb    (seal/attach! (open a))
              raf    (:raf (:oplog lkb))
              t      (Thread/currentThread)
              events (atom [])
              note!  (fn [e r] (when (and (identical? raf r) (identical? t (Thread/currentThread)))
                                 (swap! events conj e)))
              force  f/force!
              append f/append-record!
              write  @#'oplog/before-write!]
          (try
            (v/assert lkb '(animal Zeno) 'CxUniverse)
            (with-redefs [f/force!            (fn [r m] (note! :fsync r) (force r m))
                          f/append-record!    (fn ^long [r v] (when (:unusable v) (note! :mark r)) (append r v))
                          oplog/before-write! (fn [& args] (apply write args) (note! :write raf))]
              (v/clear! lkb))
            (is (= [:mark :fsync :write] (take 3 (dedupe @events))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest closing-the-directory-seals-it
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))
              g   (:generation (seal/read-seal a))
              h   (v/assert lkb '(animal Zeno) 'CxUniverse)]
          (v/close! lkb)
          (is (= (inc (long g)) (:generation (seal/read-seal a))))
          (let [kb (open a {:recover? false})
                r  (seal/restore! kb)]
            (try
              (is (:restored r))
              (is (zero? (long (:frames r))) "every write is in the images the close wrote")
              (is (v/believed? (:kb r) h))
              (finally (v/close! (or (:kb r) kb))))))
        (finally (tu/rm-rf! a))))))

(defn- log-registered?
  "Does the durability daemon hold the operation log under `dir`?"
  [dir]
  (boolean (some #(= (str "oplog " (log-path dir)) (:label %)) (vals @@#'dur/registry))))

(defn- boom [& _] (throw (ex-info "boom" {})))

(deftest an-attach-that-throws-after-the-log-opens-closes-the-log
  (tu/with-snapshot-platform
    (let [a  (tu/tmpdir "vaelii-seal-")
          kb (open a)]
      (try
        (let [thrown (try (with-redefs [seal/seal! boom] (seal/attach! kb)) nil
                          (catch clojure.lang.ExceptionInfo e (ex-message e)))]
          (is (= ["boom" false] [thrown (log-registered? (:snapshot-dir kb))])))
        (finally (v/close! kb) (tu/rm-rf! a))))))

(deftest an-attach-whose-log-close-throws-rethrows-its-own-throw-with-the-close-s-suppressed
  (tu/with-snapshot-platform
    (let [a      (tu/tmpdir "vaelii-seal-")
          kb     (open a)
          close! oplog/close-log!]
      (try
        (let [^Throwable e (try (with-redefs [seal/seal!       boom
                                              oplog/close-log! (fn [log]
                                                                 (close! log)
                                                                 (throw (java.io.IOException. "disk full")))]
                                  (seal/attach! kb))
                                nil
                                (catch Throwable e e))]
          (is (= ["boom" ["disk full"] false]
                 [(ex-message e) (mapv ex-message (.getSuppressed e)) (log-registered? (:snapshot-dir kb))])))
        (finally (v/close! kb) (tu/rm-rf! a))))))

(deftest a-log-close-whose-fsync-throws-still-closes-and-latches-the-log
  (let [a     (tu/tmpdir "vaelii-seal-")
        log   (oplog/open-log a 1)
        force f/force!]
    (try
      (let [thrown (try (with-redefs [f/force! (fn [raf meta?]
                                                 (if (identical? raf (:raf log))
                                                   (throw (java.io.IOException. "disk full"))
                                                   (force raf meta?)))]
                          (oplog/close-log! log))
                        nil
                        (catch java.io.IOException e (ex-message e)))]
        (is (= ["disk full" :closed false false]
               [thrown (:reason @(:fault log)) (.. ^RandomAccessFile (:raf log) getChannel isOpen)
                (log-registered? a)])))
      (finally (tu/rm-rf! a)))))

(deftest a-close-whose-directory-close-throws-still-closes-the-operation-log
  (tu/with-snapshot-platform
    (let [a          (tu/tmpdir "vaelii-seal-")
          lkb        (seal/attach! (open a))
          close-dir! disk/close-dir!]
      (try
        (let [thrown (try (with-redefs [disk/close-dir! (fn [& args] (apply close-dir! args) (boom))]
                            (v/close! lkb))
                          nil
                          (catch clojure.lang.ExceptionInfo e (ex-message e)))]
          (is (= ["boom" false] [thrown (log-registered? (:snapshot-dir lkb))])))
        (finally (tu/rm-rf! a))))))

;; ---- open-kb with :oplog? ---------------------------------------------------

(defn- opened [kb] (dissoc (oplog/opened (:oplog kb)) :ms))

(defn- write-dilemma!
  "`write-world!`, a `genl` edge, and a rebuttal the settle leaves standing: two forward
  rules concluding opposite literals over one individual."
  [kb]
  (write-world! kb)
  (v/assert kb '(genl animal living) 'CxUniverse)
  (v/assert kb '(set/forwardRule (implies (and (quaker ?x)) (pacifist ?x))) 'CxUniverse)
  (v/assert kb '(set/forwardRule (implies (and (republican ?x)) (not (pacifist ?x)))) 'CxUniverse)
  (v/assert kb '(quaker Nixon) 'CxUniverse)
  (v/assert kb '(republican Nixon) 'CxUniverse))

(defn- reading
  "What a reader sees of `kb` without a write: the stored count, belief per handle, the
  supertypes of `animal`, and the contradictions."
  [kb]
  {:count          (v/sentex-count kb)
   :belief         (belief kb)
   :genls          (v/genls kb 'animal 'CxUniverse)
   :contradictions (set (map #(set (map :sentence (:sides %))) (v/contradictions kb)))})

(deftest an-open-with-an-oplog-restores-what-a-crash-left
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") c (tu/tmpdir "vaelii-seal-") d (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (open a {:oplog? true})]
          (try
            (is (= {:restored false :reason :no-seal} (opened lkb))
                "a directory with no seal is opened from its records, attached and sealed")
            (is (some? (seal/read-seal a)))
            (write-dilemma! lkb)
            ;; two copies of the directory as a crash leaves it
            (copy-dir! a c)
            (copy-dir! a d)
            (finally (v/close! lkb))))
        (let [restored (open c {:oplog? true})
              rebuilt  (open d)]
          (try
            (is (= {:restored true :frames 11} (opened restored)))
            (is (seq (:contradictions (reading rebuilt))) "the world leaves a dilemma standing")
            (is (= (reading rebuilt) (reading restored))
                "the restored KB answers each read as a rebuild from the same records answers it")
            (is (number? (v/assert restored '(animal Thales) 'CxUniverse)) "and takes writes")
            (finally (v/close! restored) (v/close! rebuilt))))
        (finally (tu/rm-rf! a) (tu/rm-rf! c) (tu/rm-rf! d))))))

(deftest a-restore-replays-a-preview-s-writes-and-rollback-and-none-of-its-reads
  ;; the preview's frame is replayed so the handles it allocated stay allocated and the
  ;; records a crash inside it left are taken back; its answer went to the caller, so the
  ;; replay takes neither the reading before it nor the dilemma reports
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") c (tu/tmpdir "vaelii-seal-") d (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (open a {:oplog? true})]
          (try
            (write-dilemma! lkb)
            (is (seq (:contradictions (v/preview lkb {:add [['(not (animal Zeno)) 'CxUniverse]]}))))
            (v/assert lkb '(animal Thales) 'CxUniverse)
            (copy-dir! a c)
            (copy-dir! a d)
            (finally (v/close! lkb))))
        (let [reads    (atom {})
              count!   (fn [k f] (fn [& args] (swap! reads update k (fnil inc 0)) (apply f args)))
              restored (with-redefs [kb/prior-kb          (count! :prior-kb kb/prior-kb)
                                     clashes/opened       (count! :opened clashes/opened)]
                         (open c {:oplog? true}))
              rebuilt  (open d)]
          (try
            (is (= {:restored true :frames 13} (opened restored)))
            (is (= {} @reads))
            (is (= (reading rebuilt) (reading restored)))
            (finally (v/close! restored) (v/close! rebuilt))))
        (finally (tu/rm-rf! a) (tu/rm-rf! c) (tu/rm-rf! d))))))

(deftest a-restore-replays-a-batch-that-owes-a-lazy-reader-its-re-join
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (v/with-deferred-settle lkb
              (v/assert lkb '(set/lazyForwardRule (implies (and (dog ?x)) (hasVoice ?x Bark)))
                        'CxUniverse)
              (v/assert lkb '(set/forwardRule (implies (and (hasVoice ?x ?v)) (vocal ?x))) 'CxUniverse)
              (v/assert lkb '(dog Rex) 'CxUniverse)
              (v/assert lkb '(cat Tom) 'CxUniverse))
            (is (v/ask? lkb '(vocal Rex) 'CxUniverse))
            (restore-copy a (fn [r]
                              (is (= [true 5] [(:restored r) (:frames r)]) (pr-str (:reason r)))
                              (when (:restored r)
                                (is (= (belief lkb) (belief (:kb r)))))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest a-restore-runs-no-re-join-a-batch-that-threw-owed-at-the-next-batch-s-settle
  ;; a batch that throws records no `:settle` frame, and its owed re-joins run nowhere
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (is (thrown? clojure.lang.ExceptionInfo
                         (v/with-deferred-settle lkb
                           (v/assert lkb '(set/lazyForwardRule (implies (and (dog ?x)) (hasVoice ?x Bark)))
                                     'CxUniverse)
                           (v/assert lkb '(set/forwardRule (implies (and (hasVoice ?x ?v)) (vocal ?x)))
                                     'CxUniverse)
                           (v/assert lkb '(dog Rex) 'CxUniverse)
                           (throw (ex-info "the batch stops" {})))))
            (v/with-deferred-settle lkb (v/assert lkb '(cat Tom) 'CxUniverse))
            (is (nil? (v/handle-of lkb '(vocal Rex) 'CxUniverse)))
            (restore-copy a (fn [r]
                              (is (= [true 5] [(:restored r) (:frames r)]) (pr-str (:reason r)))
                              (when (:restored r)
                                (is (= (belief lkb) (belief (:kb r)))))))
            (finally (v/close! lkb))))
        (finally (tu/rm-rf! a))))))

(deftest an-open-whose-restore-declines-rebuilds-from-the-records-and-seals
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") c (tu/tmpdir "vaelii-seal-")]
      (try
        (let [lkb (open a {:oplog? true})]
          (try
            (v/assert lkb '(animal Socrates) 'CxUniverse)
            (v/set-solver lkb solve/local-solver)
            (copy-dir! a c)
            (finally (v/close! lkb))))
        (let [g  (:generation (seal/read-seal c))
              kb (open c {:oplog? true})]
          (try
            (is (= {:restored false :reason [:unusable [:config :set-solver]]} (opened kb)))
            (is (v/ask? kb '(animal Socrates) 'CxUniverse) "the records are rebuilt")
            (is (= (inc (long g)) (:generation (seal/read-seal c))) "and sealed again")
            (is (nil? (oplog/unusable (:oplog kb))) "so the log starts usable")
            (finally (v/close! kb))))
        (finally (tu/rm-rf! a) (tu/rm-rf! c))))))

(deftest a-clean-close-reopens-by-restoring-no-operation
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (let [h (let [lkb (open a {:oplog? :tick})]
                  (try (v/assert lkb '(animal Zeno) 'CxUniverse)
                       (finally (v/close! lkb))))
              kb (open a {:oplog? :tick})]
          (try
            (is (= {:restored true :frames 0} (opened kb)))
            (is (= :tick (oplog/fsync-mode (:oplog kb))))
            (is (v/believed? kb h))
            (finally (v/close! kb))))
        (finally (tu/rm-rf! a))))))

(deftest a-write-without-the-log-retires-the-seal
  ;; the unlogged KB's writes reach the records and no log, so a restore from the seal
  ;; would answer without them.  A retraction adds no record for `extra-records?` to see,
  ;; and a non-snapshot disk backend over the same records writes no image.
  (tu/with-snapshot-platform
    (doseq [unlogged [nil {:backend :disk-dense} {:backend :disk-columnar}]]
      (let [a (tu/tmpdir "vaelii-seal-")]
        (try
          (let [kb (open a {:oplog? true})]
            (v/assert kb '(animal Plato) 'CxUniverse)
            (v/close! kb))
          (let [g (:generation (seal/read-seal a))]
            (let [kb (open a unlogged)]
              (try (v/retract! kb (v/handle-of kb '(animal Plato) 'CxUniverse))
                   (v/assert kb '(animal Zeno) 'CxUniverse)
                   (finally (v/close! kb))))
            (is (nil? (seal/read-seal a)) (pr-str unlogged))
            (let [kb (open a {:oplog? true})]
              (try
                (is (= {:restored false :reason :no-seal} (opened kb)) (pr-str unlogged))
                (is (= [false true] (mapv #(v/ask? kb (list 'animal %) 'CxUniverse) '[Plato Zeno]))
                    (pr-str unlogged))
                (is (< (long g) (long (:generation (seal/read-seal a))))
                    "the new seal's generation is above the retired one")
                (finally (v/close! kb)))))
          (finally (tu/rm-rf! a)))))))

(deftest retiring-the-seal-fsyncs-its-directory-before-returning
  ;; a power loss that keeps the records write and loses the rename leaves the seal in
  ;; place over records it does not describe
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-")]
      (try
        (v/close! (open a {:oplog? true}))
        (let [synced (atom [])
              sync   f/fsync-dir!]
          (with-redefs [f/fsync-dir! (fn [p] (swap! synced conj (.getParent (io/file p))) (sync p))]
            (seal/retire-unlogged! {:snapshot-dir a}))
          (is (nil? (seal/read-seal a)))
          (is (some #{(str a "/oplog")} @synced)))
        (finally (tu/rm-rf! a))))))

(deftest a-records-write-the-seal-did-not-see-declines-the-restore
  ;; a writer with no path to the seal, such as a second `:pg` KB over the same schema,
  ;; stands in here as a disk KB whose retire is a no-op.  With no frame, the records'
  ;; fingerprint moves from the seal's.  With a frame a crash left, the replay moves the
  ;; fingerprint too, and the retraction shows as a node with no record, or as a premise
  ;; mark the records dropped from a sentex a rule still derives.
  (tu/with-snapshot-platform
    (doseq [[frame? retracted believed?] [[false '(animal Plato) false]
                                          [true '(animal Plato) false]
                                          [true '(mortal Plato) true]]
            :let [row (pr-str [frame? retracted])]]
      (let [a (tu/tmpdir "vaelii-seal-") c (tu/tmpdir "vaelii-seal-")]
        (try
          (let [kb (open a {:oplog? true})]
            (v/assert kb '(set/forwardRule (implies (and (animal ?x)) (mortal ?x))) 'CxUniverse)
            (v/assert kb '(animal Plato) 'CxUniverse)
            (v/assert kb '(mortal Plato) 'CxUniverse)
            (v/close! kb))
          (let [kb (open a {:oplog? true})]
            (try (when frame? (v/assert kb '(animal Zeno) 'CxUniverse))
                 (copy-dir! a c)
                 (finally (v/close! kb))))
          (with-redefs [seal/retire-unlogged! (fn [_] nil)]
            (let [kb (open c {:backend :disk-dense})]
              (try (v/retract! kb (v/handle-of kb retracted 'CxUniverse))
                   (finally (v/close! kb)))))
          (is (some? (seal/read-seal c)) row)
          (let [kb (open c {:oplog? true})]
            (try
              (is (= {:restored false :reason :records-moved} (opened kb)) row)
              (is (= believed? (v/ask? kb retracted 'CxUniverse)) row)
              (let [h (v/assert kb retracted 'CxUniverse)]
                (is (contains? (set (p/premise-ids (oplog/inner-records (:records kb)))) h)
                    (str row " a re-assert stores a premise record")))
              (finally (v/close! kb))))
          (finally (tu/rm-rf! a) (tu/rm-rf! c)))))))

(defn- manifest-source [dir]
  (:source (edn/read-string (slurp (io/file dir "reasoning" "manifest.edn")))))

(deftest a-restore-under-trust-keeps-an-image-of-other-engine-source
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") c (tu/tmpdir "vaelii-seal-")]
      (try
        (v/close! (open a {:oplog? true}))
        (let [m (io/file a "reasoning" "manifest.edn")]
          (spit m (pr-str (assoc (edn/read-string (slurp m)) :source "stale"))))
        (let [lkb (open a {:oplog? true})]
          (try
            (is (= {:restored true :frames 0} (opened lkb)) "the default open trusts the image")
            (write-world! lkb)
            (copy-dir! a c)
            (finally (v/close! lkb))))
        (is (= "stale" (manifest-source a))
            "the close's seal names the source belief was last derived under in full")
        (let [kb (open c {:oplog? true})]
          (try
            (is (= {:restored true :frames 6} (opened kb)))
            (is (v/ask? kb '(mortal Zeno) 'CxUniverse))
            (is (not (v/ask? kb '(mortal Plato) 'CxUniverse)) "the replayed retraction holds")
            (finally (v/close! kb))))
        (let [kb (open c {:oplog? true :recover? :auto})]
          (try
            (is (= {:restored false :reason [:reasoning :source-differs]} (opened kb)))
            (is (v/ask? kb '(mortal Zeno) 'CxUniverse))
            (finally (v/close! kb))))
        (is (not= "stale" (manifest-source c)) "the :auto open re-derived belief and sealed it")
        (finally (tu/rm-rf! a) (tu/rm-rf! c))))))

(deftest seal-starts-a-generation-and-declines-while-a-settle-is-pending
  (tu/with-snapshot-platform
    (let [a (tu/tmpdir "vaelii-seal-") b (tu/tmpdir "vaelii-seal-")]
      (try
        (let [kb (open a {:oplog? true})
              g  (:generation (seal/read-seal a))]
          (try
            (v/assert kb '(animal Zeno) 'CxUniverse)
            (let [r (v/seal kb)]
              (is (= {:sealed true :generation (inc (long g))}
                     (select-keys r [:sealed :generation])))
              (is (pos? (long (:watermark r))))
              (is (empty? (oplog/read-frames (:oplog kb))) "the operation is in the images"))
            (v/with-deferred-settle kb
              (v/assert kb '(animal Thales) 'CxUniverse)
              (is (= {:sealed false :reason :settle-deferred :busy true} (v/seal kb))))
            (is (= [:assert :settle] (mapv :op (oplog/read-frames (:oplog kb))))
                "the declined seal leaves the log as it was")
            (finally (v/close! kb))))
        (let [kb (open b)]
          (try (is (= {:sealed false :reason :not-applicable} (v/seal kb)) "a KB with no log")
               (finally (v/close! kb))))
        (finally (tu/rm-rf! a) (tu/rm-rf! b))))))

(deftest oplog-is-read-on-a-snapshot-kb-that-recovers
  (is (= :each (kb/oplog-mode {:backend :pg-snapshot :oplog? true})))
  (is (= :each (kb/oplog-mode {:backend :disk-snapshot :oplog? true :recover? :trust})))
  (doseq [[opts mismatch] [[{:backend :disk-snapshot :oplog? :yes}            :bad-value]
                           [{:backend :disk-log :oplog? true}                 :conflict]
                           [{:backend :disk-snapshot :oplog? true :recover? false} :conflict]
                           [{:backend :disk-snapshot :oplog? true :recover? :background}
                            :conflict]]]
    (let [dir (tu/tmpdir "vaelii-seal-")
          e   (try (v/open-kb (assoc opts :dir dir)) nil
                   (catch clojure.lang.ExceptionInfo e e)
                   (finally (tu/rm-rf! dir)))]
      (is (= {:type :unknown-option :mismatch mismatch}
             (select-keys (ex-data e) [:type :mismatch]))
          (pr-str opts)))))
