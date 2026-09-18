;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-atomicity-test
  "The TMS mutation contract: retracting an
  unknown datum no-ops instead of materializing a phantom node and fabricating a
  removal count, retraction is idempotent, and every mutation applies atomically —
  a concurrent `swap!` composes with `retract!`/`sweep!` rather than being lost to
  a deref-then-`reset!` window.

  The atomicity half runs against **both** networks.  The claim is about the mutation
  rather than about one representation of it, and the two reach it differently — the
  reference by compare-and-set on its state atom, the dense network by taking its
  `StampedLock` for writing — so a check on one says nothing about the other.  Dense is
  the default *and* the sweep switch (`VAELII_TEST_TMS=reference`) replaces it with the
  reference, so a test naming only `create-tms` would leave the shipped network
  unexercised from both sides of that axis."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- unknown datums (pure, no KB) ---------------------------------------

(deftest retract-unknown-datum-no-ops
  (let [tms (jtms/create-tms)]
    (jtms/add-premise tms 1 :monotonic)
    (let [before @tms
          result (jtms/retract! tms 999999)]
      (is (= {:removed-sentexes [] :removed-justifications []} result)
          "an unknown datum must not claim a removal")
      (is (= before @tms)
          "an unknown datum must not materialize a node"))))

(deftest retract-is-idempotent
  (let [tms (jtms/create-tms)]
    (jtms/add-premise tms 1 :default)
    (is (= [1] (:removed-sentexes (jtms/retract! tms 1))))
    (let [after  @tms
          again  (jtms/retract! tms 1)]
      (is (= {:removed-sentexes [] :removed-justifications []} again))
      (is (= after @tms) "a second retraction must change nothing"))))

;; ---- atomicity under concurrent writers ---------------------------------
;;
;; The nodes in each test are deliberately unlinked, so every operation's region
;; is a singleton and the writers interleave as densely as the scheduler allows.
;; A deref-then-reset! shape loses updates here; compare-and-set and an exclusive
;; write lock both cannot.  Each check runs on both networks — see the namespace
;; docstring on why one says nothing about the other.

(defn- retractions-that-race
  "Retract every premise from two threads at once, and answer the node set left behind."
  [make-tms]
  (let [tms (make-tms)
        n   400]
    (doseq [d (range n)] (jtms/add-premise tms d :default))
    (let [evens (future (doseq [d (range 0 n 2)] (jtms/retract! tms d)))
          odds  (future (doseq [d (range 1 n 2)] (jtms/retract! tms d)))]
      @evens @odds)
    (:nodes @tms)))

(deftest reference-concurrent-retractions-all-land
  (is (empty? (retractions-that-race jtms/create-tms))
      "reference: every concurrent retraction must land — a lost update leaves a node behind"))

(deftest dense-concurrent-retractions-all-land
  (is (empty? (retractions-that-race dense/create-dense-tms))
      "dense: every concurrent retraction must land — a lost update leaves a node behind"))

(defn- retraction-beside-a-relabelling-writer
  "Retract one range while another thread defeats and revives a disjoint one.  Answers
  `{:tms :retracted :parked}` for the caller to read both halves off."
  [make-tms]
  (let [tms  (make-tms)
        n    200
        park (range n (+ n 50))]                      ; disjoint from the retracted range
    (doseq [d (range (+ n 50))] (jtms/add-premise tms d :default))
    (let [retracting (future (doseq [d (range n)] (jtms/retract! tms d)))
          defeating  (future (dotimes [_ 25]
                               (jtms/defeat tms park)
                               (jtms/clear-defeats! tms)))]
      @retracting @defeating)
    {:tms tms :retracted (range n) :parked park}))

(defn- check-composed [label make-tms]
  (let [{:keys [tms retracted parked]} (retraction-beside-a-relabelling-writer make-tms)]
    (testing (str label ": every retraction survived the concurrent relabels")
      (is (not-any? #(get-in @tms [:nodes %]) retracted)))
    (testing (str label ": and the relabelling writer's final state survived the retractions")
      (is (every? #(jtms/in? tms %) parked)))))

(deftest reference-retraction-composes-with-a-concurrent-relabel
  (check-composed "reference" jtms/create-tms))

(deftest dense-retraction-composes-with-a-concurrent-relabel
  (check-composed "dense" dense/create-dense-tms))

;; ---- the public API contract --------------------------------------------

(deftest kb-retract-of-unknown-handle-counts-zero
  (tu/with-neutral-kb [kb tu/fresh]
    (is (= {:removed-sentexes 0 :removed-justifications 0}
           (v/retract! kb 999999)))
    (is (not-any? #{999999} (jtms/datums (reasoning/tms kb)))
        "the phantom node must not survive into the TMS")))
