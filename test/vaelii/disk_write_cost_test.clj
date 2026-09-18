;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-write-cost-test
  "What a write costs the **durable** stores, as counted file operations — the storage
  half of `assert_cost_test`, which counts index operations against the memory backend
  and so has never priced a byte reaching a disk.

  `lein perf`'s checks are ratios over the in-RAM stores, and `assert_cost_test` opens on
  `:backend :memory` deliberately, because the calls it counts live in `KvIndexStore`.
  Between them the durable path is uncovered in both directions: a ratio cannot see a
  constant (that file's preamble says why), and neither gate runs a workload that touches
  `vaelii.impl.disk.files` at all.  A syscall per record is exactly a constant, and the
  write path spends them in fixed multiples that the source states as promises —
  `append-bytes!` says two on the hot path, `write-slot!` says one positional write where
  a seek plus four primitive writes would be five, `append-records!` says one write for a
  whole batch however many ops it carries.  Nothing held those promises.

  ## What is counted, and why it is not a syscall

  Nothing on this JVM counts syscalls without an agent, so the counted calls are the file
  operations themselves, each of which `files.clj` documents as a fixed number of them:

  | counted                      | what it is                        | syscalls |
  |------------------------------|-----------------------------------|----------|
  | `f/append-record-sized!`     | one nippy frame onto a log        | via `append-bytes!` |
  | `f/append-records!`          | a whole WAL batch onto a log      | via `append-bytes!` |
  | `f/append-bytes!`            | one all-or-nothing log append     | a length read + a write |
  | `f/write-slot!`              | one 24-byte idx slot              | one write |
  | `f/write-fully-at!`          | one positional channel write      | one write |

  So `write-fully-at!` is the write syscall count and `append-bytes!` is the length-read
  count, and the two above them say which caller spent them.  Counting the *pair* is what
  makes the shape checkable rather than only the total: a slot written as a seek plus four
  primitive writes never reaches `write-fully-at!` at all, so it fails this gate by
  reading **low**, and a second length read to learn a payload the caller was already
  handed fails it by reading high.

  `write-fully-at!` and `append-bytes!` are private, which is the right side of the boundare
  to be on — they are the two functions whose whole content is the syscall — and
  `with-redefs` reaches a private var the same way `settle_region_cost_test` reaches
  `settle/body-nogoods`.  Both carry primitive argument or return hints, so each stand-in
  repeats the signature; a varargs one cannot satisfy the `IFn$OOL` the call site
  compiled to.

  ## The KB is pinned, and to its own directory

  `{:backend :disk-log}` whatever `VAELII_TEST_BACKEND` selected, for `assert_cost_test`'s
  reason: the counts are file operations, and the memory stores perform none — inheriting
  the run's backend would make this gate read zero on six of the eight and pass by
  measuring nothing.  A private temp directory rather than the suite's disk space, so it
  takes its own writer lock and collides with neither a sharded test JVM nor a concurrent
  backend run; it is closed and deleted on the way out, which is what keeps a test that
  writes real files net-neutral.

  Auto-compaction is paused across each measured region.  Compaction is a background
  thread's rewrite of a whole log, it calls the very functions being counted, and
  `with-redefs` is process-wide — so a tick landing inside the window would add a reading
  that belongs to no assert.

  ## What it does not catch

  - **How much is written.**  One `append-bytes!` counts once for four bytes or four
    megabytes.  A frame that doubled in size reads identically here, and
    `bench/vaelii/bench/perf.clj`'s `:durable-fact-append` is the check that would see it
    as growth.
  - **fsync.**  The durability daemon's tick is `f/force!` and is not on the assert path;
    what it costs is a function of the tick interval and belongs to a durability test.
  - **A store that is not the disk one.**  `sqlite` and the foreign backends write
    through their own drivers and none of these calls."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.protocols :as p]))

;; ---- the instrument ------------------------------------------------------

(defn- file-ops
  "The durable file operations `body` performs, as `{family -> calls}`.

  Each stand-in repeats its target's signature rather than taking `& args`: the two
  private ones carry primitive hints, so the call sites compiled to `IFn$OOL` /
  `IFn$OOLO` and a varargs replacement fails the cast at the first append."
  [body]
  (let [n    (atom {})
        bump (fn [k] (swap! n update k (fnil inc 0)))
        wf   @#'f/write-fully-at!
        ab   @#'f/append-bytes!
        ars  f/append-record-sized!
        arr  f/append-records!
        ws   f/write-slot!]
    (with-redefs [f/write-fully-at!      (fn [ch bb ^long pos]
                                           (bump :positional-write) (wf ch bb pos))
                  f/append-bytes!        (fn ^long [raf buf]
                                           (bump :log-append) (ab raf buf))
                  f/append-record-sized! (fn [raf value]
                                           (bump :record-frame) (ars raf value))
                  f/append-records!      (fn ^long [raf values]
                                           (bump :wal-batch) (arr raf values))
                  f/write-slot!          (fn [raf id off len flags gen]
                                           (bump :slot-write) (ws raf id off len flags gen))]
      (dur/call-with-compaction-paused body))
    @n))

;; ---- the KB --------------------------------------------------------------

(defn- delete-tree!
  [^java.io.File file]
  (when (.isDirectory file)
    (doseq [child (.listFiles file)] (delete-tree! child)))
  (.delete file))

(defn- with-disk-kb
  "Run `f` over a `:backend :disk-log` KB in a directory of its own, closed and deleted
  afterwards.  `close!` first and always: it releases the exclusive directory lock and
  drops the store from the durability daemon, so a failing assertion cannot leave a
  registrant fsyncing a directory this then removes."
  [f]
  (let [dir (java.nio.file.Files/createTempDirectory
             "vaelii-disk-write-cost" (into-array java.nio.file.attribute.FileAttribute []))
        kb  (v/open-kb {:backend :disk-log :dir (str dir) :recover? false})]
    (try (f kb)
         (finally
           (v/close! kb)
           (delete-tree! (.toFile dir))))))

(def ^:private n
  "Asserts per workload.  Small — every quantity here is exactly linear in it, so the
  claim reads the same at 20 as at 20,000, and 20 real frames on a real filesystem cost
  nothing."
  20)

;; ---- one record, one frame, one slot -------------------------------------

(def ^:private per-assert
  "What one plain fact costs the durable stores, family by family.

  A fact reaching a `:backend :disk-log` KB writes **two** records — the sentex frame and the
  provenance frame beside it — and **one** index WAL batch, the batch that carries every
  index op of that one sentex.  So three log appends and two idx slots, and the
  positional-write count is their sum: five, with no seek among them."
  {:record-frame     2
   :wal-batch        1
   :log-append       3
   :slot-write       2
   :positional-write 5})

(deftest a-durable-fact-costs-a-fixed-number-of-file-operations
  (with-disk-kb
    (fn [kb]
      ;; one write outside the count: the first assert in a process pays a class load and
      ;; the codec's own warm-up, and neither is a per-record cost
      (v/assert kb '(dwc_warm DwcWarm) 'CxPerf {:chain? false})
      (let [ops (file-ops #(dotimes [i n]
                             (v/assert kb (list 'dwcFact (symbol (str "DwcA" i)) i)
                                       'CxPerf {:chain? false})))]
        (testing "every family is exactly n times its per-assert constant"
          (is (= (into {} (map (fn [[k c]] [k (* n (long c))])) per-assert) ops)))
        (testing "and the positional writes are the log appends plus the slots — no seek"
          (is (= (long (:positional-write ops))
                 (+ (long (:log-append ops)) (long (:slot-write ops))))))))))

;; ---- a WAL batch is one write --------------------------------------------

(def ^:private batch-sizes
  "Batch widths the WAL claim is taken over.  Three, spanning two orders of magnitude,
  because the claim is *flatness*: one width could be a coincidence of the workload."
  [4 64 1024])

(deftest a-wal-batch-costs-one-write-however-many-ops-it-carries
  (with-disk-kb
    (fn [kb]
      (let [backend (:backend (:index kb))]
        (is (some? backend) "the index must be the disk KV backend, or nothing below is durable")
        ;; warm, outside the count
        (p/kv-batch backend [[:put [::dwc :warm] 1]])
        (doseq [width batch-sizes]
          (testing (str "a batch of " width " ops")
            (let [ops (file-ops #(p/kv-batch backend
                                             (mapv (fn [i] [:put [::dwc width i] i])
                                                   (range width))))]
              (is (= {:wal-batch 1 :log-append 1 :positional-write 1} ops)
                  (str "the batch must be one packed append and one write — a frame per op "
                       "is " width " of each, and a mid-batch failure then leaves the log "
                       "holding ops the RAM map lost")))))))))
