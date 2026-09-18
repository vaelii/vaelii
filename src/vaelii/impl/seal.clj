;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.seal
  "Seals and restores for a `:disk-snapshot` KB that records its writes in an operation
  log (`vaelii.impl.oplog`).

  ## A seal

  `seal!` writes the KB's derived state and starts the log again: the index image
  (`vaelii.impl.disk.index-snapshot`), the reasoning image (`vaelii.impl.reasoning-image`), then
  `<dir>/oplog/seal.nippy`, then a new generation of the log.  It fsyncs the record store
  before it writes `seal.nippy`, so every record below the watermark is on disk once a
  seal names the watermark.  `seal.nippy` holds the
  generation, the records watermark — one above every handle the store held when the seal
  was taken — and the two record fingerprints the images are stamped with.  It is written
  after both images and before the log restarts, so each crash point leaves a state an
  open can tell apart:

  - before `seal.nippy`: the images carry fingerprints the previous seal does not, so
    neither installs against it, and the open rebuilds from the records;
  - after `seal.nippy` and before the restart: the log's header names the previous
    generation, so its frames describe writes both images already hold, and the open
    replays none of them.

  A KB is sealed when a `:seal`-class operation returns, when its directory closes, and
  when its index drifts past `vaelii.index.snapshot-drift`: the drift is measured inside
  a write, so the seal waits until the operation returns (`oplog/request-seal!`).  A KB
  `reasoning-image/refusal` names a reason for, or whose network does not cover its records,
  cannot be sealed, and its log is marked unusable instead.

  ## A restore

  `restore!` takes a KB opened with `{:recover? false}` over the directory and brings it
  to the state its last durable operation left.  It installs both images against the
  fingerprints `seal.nippy` records, attaches the log in replay mode, and replays the
  current generation's frames (`oplog/replay!`).  It declines — returning a reason and
  leaving the caller to rebuild from the records — when there is no seal, the log is
  unusable, an image does not install, a replayed write differs from the record stored at
  its handle, or the store holds a record at or above the last handle the replay
  allocated, which a write whose frame never reached the disk left behind.

  A decline after the images installed leaves replayed state in the KB.  `restore!` then
  withdraws the directory's image writers and notes the `:no-belief` and `:no-index`
  hazards (`kb/note-hazards!`), so closing that KB writes no image of the state."
  (:require [clojure.java.io :as io]
            [taoensso.trove :as trove]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.index-snapshot :as snapshot]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reasoning-image :as ri])
  (:import [vaelii.impl.disk.record_store DiskRecordStore]))

(def format-version
  "`seal.nippy`'s layout number.  A seal of any other number is not restored.  Version 2
  names the reasoning image's fingerprint `:reasoning-fp` and reads the image from
  `<dir>/reasoning/`."
  2)

(defn- seal-path ^String [dir] (str dir "/oplog/seal.nippy"))

(defn read-seal
  "The seal `dir` holds, or nil."
  [dir]
  (let [s (f/read-nippy-file (seal-path dir) nil)]
    (when (= format-version (:format s)) s)))

(defn seal!
  "Seal `kb` (the namespace docstring, \"A seal\").  Returns `{:sealed true :generation g}`
  or `{:sealed false :reason r}`."
  [kb]
  (let [log   (:oplog kb)
        dir   (:snapshot-dir kb)
        inner (oplog/inner-records (:records kb))]
    (cond
      (not (and log dir (instance? DiskRecordStore inner)))
      {:sealed false :reason :not-applicable}

      (or (ri/refusal kb) (not (ri/writable? kb)))
      (let [why (or (ri/refusal kb) :reasoning-not-built)]
        (oplog/mark-unusable! log [:seal-refused why])
        {:sealed false :reason why})

      :else
      (let [gen          (inc (long (or (:generation (read-seal dir)) -1)))
            slot-fp      (drs/slot-fingerprint inner)
            reasoning-fp (drs/reasoning-fingerprint inner)
            idx          (snapshot/save! dir (:index kb) (constantly slot-fp))
            _            (ri/write-sections! kb (io/file dir ri/dir-name)
                                             (ri/stamp kb reasoning-fp))
            watermark    (inc (long (p/next-id inner)))]
        ;; every record below the watermark is on disk before the seal says it is
        (drs/fsync inner)
        (f/write-nippy-atomic! (seal-path dir)
                               {:format       format-version
                                :generation   gen
                                :watermark    watermark
                                :slot-fp      slot-fp
                                :reasoning-fp reasoning-fp
                                :index        (select-keys idx [:index :reason])})
        (oplog/rotate! log gen)
        (oplog/set-watermark! (:records kb) watermark)
        (trove/log! {:level :info :id ::sealed
                     :msg (str "sealed " dir " at generation " gen)})
        {:sealed true :generation gen}))))

(defn- seal-or-request!
  "The image writer a logged KB's directory runs: a seal outside every operation, and a
  request for one when an operation is running."
  [kb]
  (if oplog/*in-op?*
    (oplog/request-seal! (:oplog kb))
    (seal! kb)))

(defn- install-writers!
  "Make `kb`'s directory write its images only as a seal: the index writer `open-kb`
  registered becomes `seal-or-request!`, and the reasoning image's writer does nothing,
  since a seal writes both."
  [kb]
  (let [dir (:snapshot-dir kb)]
    (oplog/set-seal-fn! (:oplog kb) seal!)
    (disk/replace-index-snapshot! dir #(seal-or-request! kb))
    (disk/register-reasoning-image! dir (fn [] nil))))

(defn attach!
  "`kb` — a `:disk-snapshot` KB whose belief and index cover its records — recording its
  writes into a log under its directory, sealed once so the log starts at a generation
  its images describe.  Returns the logged KB."
  [kb]
  (let [dir (:snapshot-dir kb)
        log (oplog/open-log dir (inc (long (or (:generation (read-seal dir)) -1))))
        lkb (oplog/attach kb log)]
    (seal! lkb)
    ;; installed here and by `restore!`, never by `seal!`: `close-dir!` runs a seal
    ;; after it has withdrawn the directory's writers, and must not register new ones
    (install-writers! lkb)
    lkb))

(defn- extra-records?
  "Does `store` hold a sentex or justification at or above `next`?"
  [store ^long next]
  (boolean (or (some #(>= (long %) next) (p/sentex-ids store))
               (some #(>= (long %) next) (p/justification-ids store)))))

(defn restore!
  "Restore `kb`, opened `{:recover? false}` over its directory (the namespace docstring,
  \"A restore\").  Returns `{:restored true :kb lkb :frames n}`, or `{:restored false
  :reason r :clean? b}`: `:clean?` false when the KB already holds replayed state and
  the caller rebuilds by reopening rather than by recovering this value.  A throw
  declines as an unclean decline does — the log closed and the image writers withdrawn —
  before it propagates."
  [kb]
  (let [dir (:snapshot-dir kb)
        s   (read-seal dir)]
    (if (nil? s)
      {:restored false :reason :no-seal :clean? true}
      (let [log     (oplog/open-log dir (:generation s))
            decline (fn [reason clean?]
                      (oplog/close-log! log)
                      (when-not clean?
                        ;; the KB holds part of a replay, and the writers `open-kb`
                        ;; registered would image it stamped with the store it now holds
                        (disk/replace-index-snapshot! dir (fn [] nil))
                        (disk/register-reasoning-image! dir (fn [] nil))
                        (kb/note-hazards! kb {:no-belief true :no-index true}))
                      (trove/log! {:level :info :id ::declined
                                   :msg (str "operation log for " dir " not replayed: "
                                             (pr-str reason))})
                      {:restored false :reason reason :clean? clean?})]
        (try
          (if-let [why (oplog/unusable log)]
            (decline [:unusable why] true)
            (let [frames (if (= (:generation s) (oplog/generation log))
                           (oplog/read-frames log)
                           (do (oplog/rotate! log (:generation s)) []))
                  idx    (snapshot/load! dir (:index kb) (constantly (:slot-fp s)))
                  empty? (= :empty (get-in s [:index :reason]))]
              (cond
                (not (or (= :mapped (:index idx)) (and empty? (= :absent (:reason idx)))))
                (decline [:index (:reason idx)] true)

                :else
                (let [bel (ri/install-from! kb (io/file dir ri/dir-name)
                                            (constantly (:reasoning-fp s)))]
                  (if-not (= :installed (:reasoning bel))
                    (decline [:reasoning (:reason bel)] false)
                    (let [_   (kb/note-hazards! kb {:no-belief false :no-index false})
                          lkb (oplog/attach-replaying kb log (:watermark s))
                          r   (try (oplog/replay! lkb frames) nil
                                   (catch clojure.lang.ExceptionInfo e
                                     (if (:vaelii.impl.oplog/diverged (ex-data e))
                                       [:diverged (select-keys (ex-data e) [:handle :kind])]
                                       (throw e))))]
                      (cond
                        r (decline r false)

                        (extra-records? (oplog/inner-records (:records lkb))
                                        (oplog/replay-next (:records lkb)))
                        (decline :extra-records false)

                        :else
                        (do (oplog/finish-replay! lkb)
                            (install-writers! lkb)
                            {:restored true :kb lkb :frames (count (filter :op frames))}))))))))
          (catch Throwable t
            (decline [:threw (.getName (class t))] false)
            (throw t)))))))
