;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-locality-test
  "Locality for the operations `jtms_blocked_test` does not cover, and `sweep!`'s
  semantics.

  docs/nmtms.md publishes a measured, flat-in-graph-size claim for the relabelling
  operations.  The instrument that makes that checkable already exists
  (`regions-touched`, in `jtms_blocked_test`), which applies it to `set-blocked`.  So a
  regression in any of the others — a region widened back to `(set (keys (:nodes
  state)))`, say — costs a 2000× slowdown that no assertion catches and only a benchmark
  nobody runs would notice.

  Measuring the *region* rather than a wall clock is what makes this a test rather
  than a flake: the claim is about how much work is scoped, not how fast the machine
  is.

  Two instruments, because one of them reaches only one network.  `regions-touched`
  redefines `relabel-region*`, which is the reference's own fixpoint, and gives the
  finest reading — one entry per region the operation asked for.  The closing section
  measures the published `touched` set instead: coarser, but it is on the `Tms`
  protocol, so the same claim is checked against the network the engine actually ships.
  That gap is worth closing here rather than in the differential oracle, which compares
  `snapshot` — labels, not the touched set — so a dense relabel that widened to the whole
  graph would answer identically and pass.

  Pure — no store, no fixture.  Helpers are duplicated from
  `jtms_blocked_test` rather than shared, so the two files stay independent."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.jtms :as jtms])
  (:import [java.io PushbackReader]))

;; ---- builders (deliberately duplicated — see the ns docstring) ----------

(defn- premise
  ([tms d] (premise tms d :default))
  ([tms d s] (jtms/add-premise tms d s) d))

(defn- justify
  ([tms jid antes conseq] (justify tms jid antes conseq :monotonic))
  ([tms jid antes conseq strength]
   (jtms/ensure-node tms conseq 1)
   (jtms/add-justification tms (jtms/->just jid 'rule antes conseq {} strength))
   jid))

(defn- regions-touched
  "The sizes of every region `relabel-region*` was asked to recompute while `f` ran."
  [f]
  (let [sizes (atom [])
        orig  @#'jtms/relabel-region*]
    (with-redefs [jtms/relabel-region* (fn [state region]
                                         (swap! sizes conj (count region))
                                         (orig state region))]
      (f))
    @sizes))

(defn- fan-of
  "`n` independent premise ⇒ conclusion pairs: premise 2i, conclusion 2i+1,
  justification 1000+i.  Nothing connects the pairs, so a correctly-scoped
  operation on one of them must not grow with `n`."
  [n]
  (let [tms (jtms/create-tms)]
    (dotimes [i n]
      (premise tms (* 2 i))
      (justify tms (+ 1000 i) [(* 2 i)] (inc (* 2 i))))
    tms))

(defn- chain-of
  "A depth-`n` linear derivation: premise 0, then justification 2000+i concludes i+1
  from i, so node n rests on a chain of n justifications.  The region a root change
  relabels is the whole chain — the structure that exercises depth."
  ([n] (chain-of n :default))
  ([n strength]
   (let [tms (jtms/create-tms)]
     (premise tms 0 strength)
     (dotimes [i n]
       (justify tms (+ 2000 i) [i] (inc i) strength))
     tms)))

(def ^:private sizes [50 500 2000])

;; ---- locality of the operations docs/nmtms.md measures -------------------

(deftest adding-a-justification-touches-only-its-consequence
  (testing "a new justification relabels its conclusion, not the graph"
    (doseq [n sizes]
      (let [tms (fan-of n)]
        (is (= [1] (regions-touched #(justify tms 77777 [0] 999999)))
            (str "region grew with the graph at n=" n))))))

(deftest a-redundant-justification-relabels-nothing-and-is-still-in-the-touched-set
  ;; The two halves of the fast path, and each is a bug without the other.
  ;;
  ;; **Relabels nothing** is what collapses a recursive forward load from O(derived²):
  ;; an already-IN node feeds its consequences identically on one witness or two, so a
  ;; second derivation must not walk its forward closure again.
  ;;
  ;; **Still in the touched set** is what a reader of `touched` needs, and belief cannot say
  ;; it: a reader of the touched set that kept an answer about the datum keeps one that reads
  ;; fewer reasons than the KB holds.  `touched-in` takes it too — the datum was believed before, and a
  ;; touched set that said otherwise would read as "newly believed" to `preview` and the feed.
  (doseq [n sizes]
    (let [tms (fan-of n)]
      (jtms/reset-touched! tms)
      (is (every? zero? (regions-touched #(justify tms 77777 [0] 1)))
          (str "a second witness for an already-believed conclusion relabelled at n=" n))
      (is (contains? (jtms/touched tms) 1)
          "the consequence is not in the touched set, so a stale report is served for it")
      (is (contains? (jtms/touched-in tms) 1)
          "and it reads as newly believed, which it is not"))))

(deftest adding-a-premise-touches-only-its-own-region
  (doseq [n sizes]
    (let [tms (fan-of n)]
      (is (= [1] (regions-touched #(premise tms 888888)))
          (str "region grew with the graph at n=" n)))))

(deftest retraction-touches-only-the-retracted-datums-closure
  ;; `retract!` relabels before it sweeps; both halves must stay scoped.
  (doseq [n sizes]
    (let [tms (fan-of n)]
      (let [touched (regions-touched #(jtms/retract! tms 0))]
        (is (every? #(<= % 2) touched)
            (str "retraction relabelled a region of " (pr-str touched) " at n=" n))))))

;; ---- depth: the region-local fixpoints are worklists, not round-robin ----
;;
;; The region fixpoints iterate to stability, so a
;; round-robin sweep re-scans the whole region each round and costs O(region depth ×
;; region) on a deep chain.  The worklist re-touches a node only when one of its inputs
;; moves, so the same unique least fixpoint costs O(region edges).  Correctness first,
;; then the work bound — counting evaluations, not wall-clock, keeps it a test.

(deftest deep-chain-belief-propagates-and-withdraws-through-depth
  (let [n 300, tms (chain-of n)]
    (testing "belief reaches the end of a deep chain"
      (is (every? #(jtms/in? tms %) (range (inc n)))))
    (testing "suspending the root withdraws the entire chain"
      (jtms/suspend-premise tms 0)
      (is (not-any? #(jtms/in? tms %) (range (inc n)))))
    (testing "restoring it brings all of it back"
      (jtms/add-premise tms 0 :default)
      (is (every? #(jtms/in? tms %) (range (inc n)))))))

(deftest region-classes-relabels-a-deep-chain-in-linear-work
  ;; A :monotonic chain makes the class front actually advance through depth (a
  ;; round-robin sweep needs one round per node to propagate it, O(k²) node-class
  ;; evaluations).  Re-asserting the root premise forces ONE relabel of the whole
  ;; depth-k region; the worklist recomputes each node O(1) times.
  (let [n     400
        tms   (chain-of n :monotonic)
        calls (atom 0)
        orig  @#'jtms/node-class]
    (with-redefs [jtms/node-class (fn [& a] (swap! calls inc) (apply orig a))]
      (jtms/add-premise tms 0 :monotonic))   ; resettles 0's closure = the whole chain
    (testing "the deep relabel is correct — the class propagates to every node"
      (is (every? #(= :monotonic (jtms/defeat-class tms %)) (range (inc n)))))
    (testing "and it cost O(k), not O(k²), node-class evaluations"
      (is (< @calls (* 4 n))
          (str "node-class ran " @calls " times at depth " n
               "; a round-robin sweep would run ~" (* n n))))))

(deftest dense-region-classes-evaluates-a-node-once-per-rise-not-once-per-justification
  ;; Premise 0 rises to :monotonic and n :default justifications [0 i] conclude node 1,
  ;; which stays :default: 0's rise reaches node 1 through each of 0's n dependents.
  (let [n     400
        tms   (dense/create-dense-tms)
        calls (atom 0)
        orig  @#'dense/node-class]
    (premise tms 0)
    (dotimes [i n]
      (premise tms (+ 10 i))
      (justify tms (+ 5000 i) [0 (+ 10 i)] 1 :default))
    (with-redefs-fn {#'dense/node-class (fn [& a] (swap! calls inc) (apply orig a))}
      #(jtms/add-premise tms 0 :monotonic))
    (is (= [:monotonic :default] (mapv #(jtms/defeat-class tms %) [0 1])))
    (is (< @calls 8) (str "node-class ran " @calls " times over " n " justifications"))))

;; ---- sweep! semantics ---------------------------------------------------
;;
;; `sweep!` is `retract!`'s collector without the retraction, and `exceptWhen` makes
;; it a routine path rather than a retraction-only one.  Every existing test reaches
;; it through `retract!` or through a full `settle`, so its own contract is untested elsewhere.

(deftest sweep-collects-the-whole-closure-of-its-seeds
  ;; The seeds are where the walk *starts*, not what it collects: a blocked
  ;; justification orphans its conclusion and everything resting on that.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (justify tms 102 [2] 3)
    (justify tms 103 [3] 4)
    (jtms/set-blocked tms #{101})
    (is (not-any? #(jtms/in? tms %) [2 3 4]))
    (let [{:keys [removed-sentexes removed-justifications]} (jtms/sweep! tms [2])]
      (testing "seeding at 2 collects 3 and 4 as well — the consequence closure"
        (is (= #{2 3 4} (set removed-sentexes))))
      (testing "and the justifications that touched them go too"
        (is (= #{101 102 103} (set removed-justifications))))
      (testing "the premise is not swept — it is still asserted"
        (is (jtms/in? tms 1))
        (is (jtms/premise? tms 1))))))

(deftest sweep-keeps-a-datum-that-still-has-a-witness
  ;; Groundability, not belief: a second derivation means the datum is still
  ;; structurally derivable and must survive the collector.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (premise tms 2)
    (justify tms 101 [1] 3)
    (justify tms 102 [2] 3)
    (jtms/set-blocked tms #{101})
    (let [{:keys [removed-sentexes]} (jtms/sweep! tms [3])]
      (is (empty? removed-sentexes) "3 is still derivable through 102")
      (is (jtms/in? tms 3)))))

(deftest sweep-prunes-the-blocked-set-of-justifications-it-removed
  ;; A blocked id outliving its justification is a leak that only shows up later,
  ;; when a new justification is allocated the same id and arrives pre-blocked.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (is (= #{101} (jtms/blocked tms)))
    (jtms/sweep! tms [2])
    (is (empty? (jtms/blocked tms))
        "the swept justification's block went with it")))

(deftest sweep-does-not-report-a-premise-marker-as-a-removed-justification
  ;; A premise's own marker justification is bookkeeping, not a justification the caller
  ;; should be told to delete from its justification store.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (let [{:keys [removed-justifications]} (jtms/sweep! tms [2])]
      (is (= [101] (vec removed-justifications)))
      (is (not-any? #(= :premise (:informant (jtms/justification tms %)))
                    removed-justifications)))))

(deftest sweeping-a-live-datum-removes-nothing
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (let [{:keys [removed-sentexes removed-justifications]} (jtms/sweep! tms [2])]
      (is (empty? removed-sentexes) "2 is still derived, so it stays")
      (is (empty? removed-justifications)))))

;; ---- ensure* keeps the SHALLOWEST depth --------------------------------

(deftest a-datum-keeps-the-shallowest-depth-it-was-ever-given
  ;; Depth bounds forward chaining (`:max-depth`), and a datum re-derived by a longer
  ;; route must not inherit the longer route's depth — otherwise re-deriving an
  ;; existing conclusion could push it past the truncation bound and drop it.
  (let [tms (jtms/create-tms)]
    (jtms/ensure-node tms 5 7)
    (is (= 7 (jtms/depth tms 5)))
    (jtms/ensure-node tms 5 3)
    (is (= 3 (jtms/depth tms 5)) "a shallower derivation lowers the recorded depth")
    (jtms/ensure-node tms 5 9)
    (is (= 3 (jtms/depth tms 5)) "a deeper one does not raise it back")))

;; ---- the same claim at the protocol, on both representations ---------------
;;
;; Everything above instruments `relabel-region*`, which is the reference network's own
;; fixpoint — so it says nothing about the network the engine actually ships.  The dense
;; one writes the whole relabel a second time against bitmaps and primitive-keyed maps,
;; and the differential oracle compares the two on `snapshot`, which carries labels and
;; not the touched set: a dense operation that widened its region back to the whole graph
;; answers identically and is invisible there.
;;
;; `touched` is the instrument that works at the protocol — it is on the protocol, both
;; implementations maintain it, and it is what `preview`, the consequence report and the
;; change feed read (docs/preview.md, docs/feed.md).  What locality claims about it is
;; not a constant but a *shape*: the touched set of an operation on one pair does not grow
;; when the graph around it does.

(def ^:private networks
  "Both shipped representations, each with the name a failure should print."
  [["reference" jtms/create-tms]
   ["dense"     dense/create-dense-tms]])

(defn- fan-on
  "`fan-of`'s graph on a caller-supplied network, so one shape runs against both."
  [make n]
  (let [tms (make)]
    (dotimes [i n]
      (premise tms (* 2 i))
      (justify tms (+ 1000 i) [(* 2 i)] (inc (* 2 i))))
    tms))

(defn- touched-by
  "The datums `f` relabelled, read through the protocol rather than through one
  implementation's internals."
  [tms f]
  (jtms/reset-touched! tms)
  (f)
  (jtms/touched tms))

(defn- flat-across-sizes
  "The touched-set size `op` produces at each of `sizes`, as a vector — so a failure prints
  the structure that grew rather than just that one number was wrong."
  [make op]
  (mapv (fn [n] (let [tms (fan-on make n)] (count (touched-by tms #(op tms))))) sizes))

(deftest every-representation-scopes-its-touched-set-to-the-region
  (doseq [[label make] networks]
    (testing label
      (testing "blocking one derivation publishes a touched set that does not grow with the graph"
        (let [ws (flat-across-sizes make #(jtms/set-blocked % #{1000}))]
          (is (apply = ws) (str label ": touched-set sizes " (pr-str ws) " across " (pr-str sizes)))
          (is (<= (first ws) 2) (str label ": the touched set is the datum and its closure"))))
      (testing "unblocking publishes a touched set scoped to what was blocked"
        (let [ws (mapv (fn [n]
                         (let [tms (fan-on make n)]
                           (jtms/set-blocked tms #{1000})
                           (count (touched-by tms #(jtms/set-blocked tms #{})))))
                       sizes)]
          (is (apply = ws) (str label ": touched-set sizes " (pr-str ws)))
          (is (<= (first ws) 2) (str label ": the release reaches only what was blocked"))))
      (testing "a settle that blocks nothing publishes an empty touched set"
        (let [tms (fan-on make 500)]
          (is (empty? (touched-by tms #(jtms/set-blocked tms #{}))))))
      (testing "a new justification publishes a touched set around its conclusion"
        (let [ws (flat-across-sizes make #(justify % 77777 [0] 999999))]
          (is (apply = ws) (str label ": touched-set sizes " (pr-str ws)))
          (is (<= (first ws) 2) (str label ": a new conclusion is not a graph-wide event"))))
      (testing "the touched set is the forward closure, so a chain is reached and nothing else"
        (let [tms (fan-on make 500)]
          (justify tms 9001 [1] 100001)
          (justify tms 9002 [100001] 100002)
          (let [w (touched-by tms #(jtms/set-blocked tms #{1000}))]
            (is (= #{1 100001 100002} (set w))
                (str label ": the blocked datum and its two descendants, not the other 499 pairs"))))))))

(deftest every-representation-keeps-a-redundant-witness-in-the-touched-set
  ;; The touched set's *superset* half, which the scoping tests above cannot see: a second
  ;; derivation of an already-believed conclusion moves no label, and the conclusion is
  ;; noted as touched anyway (docs/defenses.md, "The touched set is a superset, not
  ;; the flip set").  Both halves are needed and both are checked here.
  ;;
  ;; It is worth a protocol-level test because the failure is backend-specific and shows up
  ;; far away: a reader of the touched set that kept an answer about a silently-arriving witness
  ;; keeps one that reads fewer reasons than the KB holds — on one backend and not the
  ;; other.
  (doseq [[label make] networks]
    (testing label
      (let [tms (make)]
        (jtms/add-premise tms 0 :default)
        (jtms/ensure-node tms 1 1)
        (jtms/add-justification tms (jtms/->just 100 'firstRule [0] 1 {} :monotonic))
        (jtms/add-premise tms 2 :default)
        (let [w (touched-by tms #(jtms/add-justification
                                  tms (jtms/->just 101 'secondRule [2] 1 {} :monotonic)))]
          (is (jtms/in? tms 1) (str label ": the conclusion was believed throughout"))
          (is (contains? (set w) 1)
              (str label ": the consequence is outside the touched set, so a stale report is served for it"))
          (is (contains? (set (jtms/touched-in tms)) 1)
              (str label ": it reads as newly believed, which it is not")))))))

(deftest every-representation-re-marks-a-premise-at-its-own-strength-without-a-relabel
  ;; `recovery/rebuild-tms` over a network that already holds its records re-marks every
  ;; premise, and a relabel of each one's forward closure costs O(n²) over a chain n deep.
  (doseq [[label make] networks
          n            sizes]
    (testing (str label " n=" n)
      (let [tms    (make)
            labels #(mapv (fn [d] [(jtms/in? tms d) (jtms/defeat-class tms d)]) (range (inc n)))]
        (jtms/add-premise tms 0 :default)
        (dotimes [i n]
          (jtms/ensure-node tms (inc i) 1)
          (jtms/add-justification tms (jtms/->just (+ 2000 i) 'rule [i] (inc i) {} :default)))
        (let [before (labels)]
          (is (= #{0} (set (touched-by tms #(jtms/add-premise tms 0 :default))))
              "the re-mark relabelled the premise's forward closure")
          (is (contains? (set (jtms/touched-in tms)) 0)
              "the premise is noted as a relabel would note it")
          (is (= before (labels)))
          (is (= (inc n) (count (touched-by tms #(jtms/add-premise tms 0 :monotonic))))
              "a mark at another strength relabels the closure"))))))

;; ---- the structural half of the same claim ------------------------------

(deftest neither-representation-names-the-store-protocols
  ;; Obligation 4 of the `Tms` docstring, and the reason locality's per-boundary-node
  ;; cost is a claim about every representation rather than about the reference's
  ;; happens-to-be-free reads: the protocol passes the network plus integers and plain
  ;; values, so no implementation of it can turn a boundary read into a lock and a slot
  ;; decode, or into a round trip.
  ;;
  ;; What is checked is the narrow, exact thing the obligation rests on — that neither
  ;; namespace names `vaelii.impl.protocols`, where `RecordStore` and `IndexStore` live.
  ;; It is not "requires nothing storage-shaped": `dense-jtms` takes `IntPostings` from
  ;; `vaelii.impl.dense-kv`, which is a data structure and not a store.
  (doseq [ns-sym '[vaelii.impl.jtms vaelii.impl.dense-jtms vaelii.impl.jtms-protocol]]
    (let [path (-> (name ns-sym)
                   (str/replace "." "/")
                   (str/replace "-" "_")
                   (str ".clj"))
          form (with-open [r (PushbackReader. (io/reader (io/resource path)))]
                 (read {:read-cond :allow} r))]
      (is (= 'ns (first form)) (str path " does not open with an ns form"))
      (is (not (contains? (set (tree-seq coll? seq form)) 'vaelii.impl.protocols))
          (str ns-sym " names the store protocols; the network holds no store"
               " (see the `Tms` docstring, obligation 4)")))))

(deftest a-mark-reads-what-the-touched-set-recorded-after-it
  ;; `touched-since` is what a reader that asks the touched set more than once between resets reads.
  ;; Relabelling again a datum the touched set already holds is the case a set difference over
  ;; `touched` drops, and a redundant witness is the one that moves no label.
  (doseq [[label make] networks]
    (testing label
      (let [tms (fan-on make 50)]
        (jtms/reset-touched! tms)
        (jtms/set-blocked tms #{1000})
        (let [m (jtms/touch-mark tms)]
          (is (empty? (jtms/touched-since tms m)) "a mark reads nothing recorded before it")
          (jtms/set-blocked tms #{})
          (justify tms 77777 [2] 3)
          (is (= #{1 3} (jtms/touched-since tms m))
              (str label ": the datums relabelled again and the redundant witness's conclusion"))
          (let [m2 (jtms/touch-mark tms)]
            (justify tms 77778 [4] 5)
            (is (= #{5} (jtms/touched-since tms m2)) "each reader's mark reads from its own point")
            (is (= #{1 3 5} (jtms/touched-since tms m)) "and a later mark leaves an earlier one whole"))
          (is (= (jtms/touched tms) (jtms/touched-since tms nil)) "a nil mark reads the whole touched set")
          (jtms/reset-touched! tms)
          (justify tms 77779 [6] 7)
          (is (= (jtms/touched tms) (jtms/touched-since tms m))
              "a mark from before the reset reads the whole touched set, not a stale epoch"))))))

(deftest marks-taken-with-nothing-recorded-between-them-share-one-epoch
  ;; a settle takes a mark at each reconcile and discovery, and most of them follow no
  ;; relabel, so an epoch per mark lengthens every `touched-since` by the empty epochs
  (doseq [[label make] networks]
    (testing label
      (let [tms (fan-on make 50)]
        (jtms/reset-touched! tms)
        (let [ms (vec (repeatedly 5 #(jtms/touch-mark tms)))]
          (is (apply = ms) "five marks over an empty touched set are one")
          (justify tms 77777 [2] 3)
          (let [m2 (jtms/touch-mark tms)]
            (is (not= (first ms) m2) "a mark after a recording opens a new epoch")
            (justify tms 77778 [4] 5)
            (is (= #{3 5} (jtms/touched-since tms (first ms))))
            (is (= #{5} (jtms/touched-since tms m2)))))))))

(deftest a-held-reach-answer-agrees-with-a-fresh-walk-after-each-change-a-run-makes
  (doseq [[label make] networks]
    (testing label
      (let [tms     (make)
            targets (atom #{90})
            asked   [0 1 2 3 4 5 6 7 90]
            reached (fn [] (into #{} (filter #(jtms/support-reaches? tms % @targets @targets)) asked))
            check   (fn [step]
                      (let [held (reached)
                            walk (binding [jtms/*reach-memo* nil] (reached))]
                        (is (= walk held) (str step ": the held answers are the walk's"))
                        held))]
        (binding [jtms/*reach-memo* (jtms/run-reach-memo tms)]
          (premise tms 0)
          (premise tms 90)
          (justify tms 101 [0] 1)
          (justify tms 102 [1] 2)
          (justify tms 103 [2] 3)
          (justify tms 104 [3] 4)
          (justify tms 105 [4] 3)
          (is (= #{90} (check "a cycle reaching no target")))
          (justify tms 106 [90] 4)
          (is (= #{90 3 4} (check "a route gained inside the cycle")))
          (justify tms 107 [2] 5)
          (check "a new conclusion")
          (justify tms 108 [3] 1)
          (is (= #{90 1 2 3 4 5} (check "a route gained below handles answered false")))
          (justify tms 109 [90] 6)
          (premise tms 7)
          (justify tms 110 [6] 7)
          (is (= #{90 1 2 3 4 5 6} (check "a premise is not walked past")))
          (jtms/suspend-premise tms 7)
          (is (= #{90 1 2 3 4 5 6 7} (check "a suspended premise is")))
          (jtms/retract! tms 90)
          (is (= #{90} (check "a removal")))
          (swap! targets conj 0)
          (is (contains? (check "a target added") 0)))))))

(deftest a-held-reach-answer-follows-a-watched-handle-gaining-and-losing-support
  (doseq [[label make] networks]
    (testing label
      (let [tms     (make)
            target? (fn [d] (when (= 1 d)
                              (jtms/watch-support! tms 95)
                              (not (jtms/unsupported? tms 95))))
            reached (fn [] (into #{} (filter #(jtms/support-reaches? tms % target? :k)) [0 1 2]))
            check   (fn [step]
                      (let [held (reached)
                            walk (binding [jtms/*reach-memo* nil] (reached))]
                        (is (= walk held) (str step ": the held answers are the walk's"))
                        held))]
        (binding [jtms/*reach-memo* (jtms/run-reach-memo tms)]
          (premise tms 0)
          (justify tms 101 [0] 1)
          (justify tms 102 [1] 2)
          (premise tms 95)
          (jtms/suspend-premise tms 95)
          (is (= #{} (check "the naming handle has no support")))
          (premise tms 95)
          (is (= #{1 2} (check "it gains a premise mark")))
          (jtms/suspend-premise tms 95)
          (is (= #{} (check "it loses the mark")))
          (justify tms 103 [0] 95)
          (is (= #{1 2} (check "it gains a justification"))))))))
