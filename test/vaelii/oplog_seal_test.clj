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
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.seal :as seal]
            [vaelii.impl.solve :as solve])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-seal-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- copy-dir!
  "Copy `from` into `to` as the files stand — a crash's view of a directory whose store
  is still open."
  [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        (Files/copy (.toPath f) (.toPath t)
                    ^"[Ljava.nio.file.CopyOption;"
                    (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))))))

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
        (map (fn [h] [h (v/in? kb h)]))
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
   (let [dir (tmpdir)]
     (try
       (copy-dir! src dir)
       (edit dir)
       (let [kb (open dir {:recover? false})
             r  (seal/restore! kb)]
         (try (check r)
              (finally (v/close! (or (:kb r) kb)))))
       (finally (rm-rf! dir))))))

(deftest a-restore-replays-to-the-belief-a-recover-computes
  (let [a (tmpdir) c (tmpdir)]
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
      (finally (rm-rf! a) (rm-rf! c)))))

(deftest a-replayed-write-that-differs-from-the-store-declines
  (let [a (tmpdir)]
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
      (finally (rm-rf! a)))))

(deftest a-frame-lost-after-its-records-reached-the-disk-declines
  (let [a (tmpdir)]
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
      (finally (rm-rf! a)))))

(deftest an-unusable-log-declines
  (let [a (tmpdir)]
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
      (finally (rm-rf! a)))))

(deftest a-seal-class-operation-seals-when-it-returns
  (let [a (tmpdir) txt (tmpdir)]
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
      (finally (rm-rf! a) (rm-rf! txt)))))

(deftest a-kb-whose-network-does-not-cover-its-records-is-not-sealed
  (let [a (tmpdir)]
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
      (finally (rm-rf! a)))))

(deftest closing-the-directory-seals-it
  (let [a (tmpdir)]
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
            (is (v/in? (:kb r) h))
            (finally (v/close! (or (:kb r) kb))))))
      (finally (rm-rf! a)))))
