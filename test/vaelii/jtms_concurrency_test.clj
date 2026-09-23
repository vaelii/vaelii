;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-concurrency-test
  "A reader thread beside a writer thread is the supported shape (docs/storage.md, the
  single-writer contract): the web browser over a REPL's KB.  The atom-over-persistent-map
  reference gives that reader a consistent view for free; the dense network mutates its
  bitmaps in place, so it earns the same guarantee with a `StampedLock`.

  This is the guarantee under stress.  One writer churns a graph — asserting and
  retracting premises, rebuilding a chain over them (so nodes, belief and adjacency are
  swept and re-grown every pass), and defeating then clearing — while several readers
  continuously take a whole-network snapshot and a handful of point reads.  Two things
  must hold for **both** representations:

  - **No reader ever throws.**  An unlocked walk over a bitmap a writer is rewriting in
    place can read a half-installed container and fault; a consistent read cannot.
  - **Every snapshot is internally consistent.**  A believed, non-superseded datum is
    always a node.  `sweep!` deletes a datum from the node set and from the believed set
    in two steps, and a reader that catches the gap on an unsynchronized structure would
    see belief in a datum that no longer has a node — the torn read the lock forecloses.

  The reference arm is the control: it has always held this, so a failure there is the
  harness's own bug, not the network's.  The dense arm is the claim the default rests on."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.jtms :as jtms])
  (:import [java.util.concurrent CountDownLatch TimeUnit]))

(defn- ->just
  "A ground justification: `id`, a `:rule` informant, one antecedent, one consequence."
  [id ante conseq]
  (jtms/->just id :rule [ante] conseq nil :default))

(defn- reader-during-writer-stress
  "Run the stress against the network `make-tms` builds.  Returns
  `{:errors [...] :violations n :reads n}` — errors any reader threw, violations any
  snapshot where a believed datum was not a node, reads the total snapshots taken."
  [make-tms {:keys [readers writer-iters premises chain]}]
  (let [tms   (make-tms)
        j0    100000                                    ; chain justification ids, disjoint from handles
        stop  (atom false)
        errs  (atom [])
        viol  (atom 0)
        reads (atom 0)
        ;; the writer waits for every reader's first snapshot: on a loaded box the
        ;; writer's eight passes can otherwise end before a reader is scheduled, and the
        ;; run measures nothing
        started (CountDownLatch. (long readers))]
    ;; seed the premises and a chain node per the first `chain` of them
    (doseq [d (range premises)] (jtms/add-premise tms d :default))
    (doseq [i (range chain)]
      (jtms/ensure-node tms (+ premises i) 1)
      (jtms/add-justification tms (->just (+ j0 i) i (+ premises i))))
    (jtms/relabel tms)
    (let [reader (fn []
                   (try
                     (while (not @stop)
                       (let [s        @tms
                             nodes    (:nodes s)
                             believed (remove (:superseded s {}) (:in s))
                             c        (swap! reads inc)
                             probe    (mod c premises)]
                         (.countDown started)
                         (when-not (every? #(contains? nodes %) believed)
                           (swap! viol inc))
                         ;; exercise the optimistic point reads too — these fault on a
                         ;; torn bitmap if they are not validated
                         (jtms/in? tms probe)
                         (jtms/known-datum? tms probe)
                         (jtms/supports tms probe)
                         (jtms/defeat-class tms probe)))
                     (catch Throwable t (swap! errs conj t))
                     (finally (.countDown started))))
          writer (future
                   (try
                     (.await started 10 TimeUnit/SECONDS)
                     (dotimes [_ writer-iters]
                       (doseq [d (range premises)]
                         (jtms/retract! tms d)
                         (jtms/add-premise tms d :default)
                         (when (< d chain)
                           (jtms/ensure-node tms (+ premises d) 1)
                           (jtms/add-justification tms (->just (+ j0 d) d (+ premises d)))))
                       ;; and a defeat/clear sweep across a slice, another relabel shape
                       (jtms/defeat tms (range 0 premises 3))
                       (jtms/clear-defeats! tms))
                     (finally (reset! stop true))))
          rs     (mapv (fn [_] (future (reader))) (range readers))]
      @writer
      (run! deref rs)
      {:errors @errs :violations @viol :reads @reads})))

(def ^:private params {:readers 3 :writer-iters 8 :premises 100 :chain 32})

(defn- check! [label {:keys [errors violations reads]}]
  (is (empty? errors)
      (str label ": a reader faulted racing the writer — "
           (when-let [t (first errors)] (str (class t) ": " (.getMessage ^Throwable t)))))
  (is (zero? violations)
      (str label ": a reader observed belief in a datum with no node (" violations
           " torn snapshots)"))
  (is (pos? reads) (str label ": the readers never ran")))

(deftest ^:slow dense-reads-stay-consistent-under-a-concurrent-writer
  (check! "dense" (reader-during-writer-stress dense/create-dense-tms params)))

(deftest reference-reads-stay-consistent-under-a-concurrent-writer
  ;; the control: the reference has always given a consistent snapshot, so this proves
  ;; the harness measures the guarantee rather than tripping on its own races
  (check! "reference" (reader-during-writer-stress jtms/create-tms params)))
