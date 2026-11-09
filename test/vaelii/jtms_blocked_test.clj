;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-blocked-test
  "Blocked justifications: `exceptWhen` seen from inside the TMS.

  A rule may carry an exception, and when that exception holds for a particular
  derivation the justification is **blocked** — it supports nothing.  The TMS is pure
  and has no KB, so it cannot run the exception query itself: the answer is computed
  outside and handed in with `jtms/set-blocked`.

  These tests are **pure** — no store, no fixture.  `nmtms_test.clj` drives
  the same machinery end-to-end through `vaelii.core`; here the graph is built by hand
  so a claim about the *region* a relabel touches is checkable rather than inferred
  from a timing.  Both invariants of docs/nmtms.md are covered: order independence
  (the same blocked set reached by different routes lands in the same state) and
  locality (blocking seeds the region from the changed justifications' consequences,
  so the work is flat in graph size)."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.observe :as observe]))

;; ---- tiny graph builders ------------------------------------------------

(defn- premise
  ([tms d] (premise tms d :default))
  ([tms d strength] (jtms/add-premise tms d strength) d))

(defn- justify
  "Add justification `jid`: `antes` ⇒ `conseq`, at `strength` (default :monotonic)."
  ([tms jid antes conseq] (justify tms jid antes conseq :monotonic))
  ([tms jid antes conseq strength]
   (jtms/ensure-node tms conseq 1)
   (jtms/add-justification tms (jtms/->just jid 'rule antes conseq {} strength))
   jid))

(deftest queue-only-support-observers-are-network-local-without-write-reports
  (doseq [create [jtms/create-tms dense/create-dense-tms]]
    (let [a (create), b (create), other (create)
          events (atom [])
          frame (fn [tms label previous]
                  {:tms tms :previous previous :active? (constantly true)
                   :note (fn [hs removed?] (swap! events conj [label (set hs) removed?]))})]
      (premise a 1)
      (premise a 2)
      (justify a 101 [1] 3)
      (justify a 102 [2] 3)
      (binding [observe/*write-record* nil
                jtms/*support-observer* (frame a :inner-a (frame b :b (frame a :outer-a nil)))]
        (jtms/set-blocked a #{101})
        (jtms/set-blocked a #{})
        (jtms/set-forced a :void [101] true)
        (jtms/set-forced a :void [101] false)
        (jtms/add-premise b 20)
        (jtms/set-blocked a #{})
        (jtms/set-forced a :void [101] false)
        (jtms/add-premise b 20)
        (justify a 101 [1] 3)
        (jtms/retract! a 999)
        (jtms/add-premise other 30)
        (is (nil? observe/*write-record*))
        (is (jtms/in? a 3) "the independent alternate keeps the datum IN throughout")
        (is (= [[:inner-a #{3} false] [:inner-a #{3} false]
                [:inner-a #{3} false] [:inner-a #{3} false] [:b #{20} false]] @events)
            "first matching owner only, including blocked moves with reporting disabled"))
      (reset! events [])
      (binding [jtms/*support-observer* (assoc (frame a :inactive nil) :active? (constantly false))]
        (jtms/add-premise a 40))
      (is (empty? @events)))))

;; ---- the headline: a blocked justification supports nothing -------------

(deftest blocking-withdraws-a-solely-supported-conclusion
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (is (jtms/in? tms 2) "the conclusion holds while the justification is valid")
    (jtms/set-blocked tms #{101})
    (testing "the blocked justification stops supporting its conclusion"
      (is (= #{101} (jtms/blocked tms)))
      (is (not (jtms/in? tms 2))))
    (testing "and nothing else moved — the antecedent is a premise and stands"
      (is (jtms/in? tms 1)))))

(deftest a-second-valid-justification-keeps-the-conclusion-in
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (premise tms 2)
    (justify tms 101 [1] 3)
    (justify tms 102 [2] 3)
    (jtms/set-blocked tms #{101})
    (testing "an alternate witness survives the block"
      (is (jtms/in? tms 3)))
    (jtms/set-blocked tms #{101 102})
    (testing "blocking every support withdraws the conclusion"
      (is (not (jtms/in? tms 3))))))

(deftest unblocking-restores-belief
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (is (not (jtms/in? tms 2)))
    (testing "clearing the set revives the conclusion — belief is recomputed"
      (jtms/set-blocked tms #{})
      (is (jtms/in? tms 2)))))

(deftest blocking-cascades-to-the-consequences
  ;; 1 ⇒ 2 ⇒ 3 ⇒ 4.  Blocking the first link must withdraw the whole chain, not
  ;; just its immediate conclusion.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (justify tms 102 [2] 3)
    (justify tms 103 [3] 4)
    (is (every? #(jtms/in? tms %) [2 3 4]))
    (jtms/set-blocked tms #{101})
    (testing "everything downstream of the blocked justification goes OUT"
      (is (not-any? #(jtms/in? tms %) [2 3 4])))
    (jtms/set-blocked tms #{})
    (testing "and the whole chain comes back"
      (is (every? #(jtms/in? tms %) [2 3 4])))))

(deftest retracting-through-a-block-sweeps-the-conclusion
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (let [{:keys [removed-sentexes removed-justifications]} (jtms/retract! tms 1)]
      (is (= #{1 2} (set removed-sentexes)))
      (is (= [101] (vec removed-justifications))))
    (testing "the swept justification's block goes with it — no stale id survives"
      (is (empty? (jtms/blocked tms))))))

;; ---- defeat-class --------------------------------------------------------

(deftest a-blocked-justification-confers-no-defeat-class
  ;; Two supports for 3: a :monotonic one grounded in a :monotonic premise, and a
  ;; :default one.  The monotonic support decides the class — until it is blocked.
  (let [tms (jtms/create-tms)]
    (premise tms 1 :monotonic)
    (premise tms 2 :default)
    (justify tms 101 [1] 3 :monotonic)
    (justify tms 102 [2] 3 :default)
    (is (= :monotonic (jtms/defeat-class tms 3)))
    (jtms/set-blocked tms #{101})
    (testing "the blocked support's strength is never read"
      (is (jtms/in? tms 3))
      (is (= :default (jtms/defeat-class tms 3))))
    (jtms/set-blocked tms #{101 102})
    (testing "with every support blocked the datum is OUT and has no class"
      (is (not (jtms/in? tms 3)))
      (is (nil? (jtms/defeat-class tms 3))))
    (jtms/set-blocked tms #{})
    (is (= :monotonic (jtms/defeat-class tms 3)))))

;; ---- invariant 1: order independence ------------------------------------

(deftest the-same-blocked-set-yields-the-same-state-however-it-is-reached
  ;; A diamond with a shared conclusion, blocked by three different routes to the
  ;; same set.  Belief is computed from the current set, never accumulated, so the
  ;; three must be indistinguishable — down to the classes and groundability.
  (let [build (fn []
                (let [tms (jtms/create-tms)]
                  (premise tms 1 :monotonic)
                  (premise tms 2)
                  (justify tms 101 [1] 3 :monotonic)
                  (justify tms 102 [2] 3 :default)
                  (justify tms 103 [3] 4)
                  (justify tms 104 [1 2] 5)
                  tms))
        observe (fn [tms] (select-keys @tms [:in :classes :blocked]))
        routes [(fn [tms] (jtms/set-blocked tms #{101 104}))
                (fn [tms] (jtms/set-blocked tms #{104}) (jtms/set-blocked tms #{101 104}))
                (fn [tms] (jtms/set-blocked tms #{101}) (jtms/set-blocked tms #{101 104}))
                (fn [tms] (jtms/set-blocked tms #{102 103})
                  (jtms/set-blocked tms #{101 104}))]
        results (into #{} (map (fn [r] (let [tms (build)] (r tms) (observe tms)))) routes)]
    (is (= 1 (count results))
        (str "blocking is order-dependent: " (count results) " distinct states"))))

;; ---- invariant 2: locality ----------------------------------------------

(defn- regions-touched
  "Run `f`, returning the sizes of every region `relabel-region*` was asked to
  recompute.  Measuring the region directly rather than a wall-clock time is what
  makes the locality claim checkable instead of flaky."
  [f]
  (let [sizes (atom [])
        orig  @#'jtms/relabel-region*]
    (with-redefs [jtms/relabel-region* (fn [state region]
                                         (swap! sizes conj (count region))
                                         (orig state region))]
      (f))
    @sizes))

(defn- fan-of
  "`n` independent premise ⇒ conclusion pairs, premise 2i, conclusion 2i+1,
  justification id 1000+i."
  [n]
  (let [tms (jtms/create-tms)]
    (dotimes [i n]
      (premise tms (* 2 i))
      (justify tms (+ 1000 i) [(* 2 i)] (inc (* 2 i))))
    tms))

(deftest blocking-touches-only-the-affected-region
  (testing "one blocked justification relabels exactly its conclusion, at any size"
    (doseq [n [50 500 2000]]
      (let [tms (fan-of n)]
        (is (= [1] (regions-touched #(jtms/set-blocked tms #{1000})))
            (str "region grew with the graph at n=" n)))))
  (testing "the region is the forward closure, so a chain block reaches its cascade"
    (let [tms (fan-of 500)]
      (justify tms 9001 [1] 100001)                  ; hang a chain off conclusion 1
      (justify tms 9002 [100001] 100002)
      (is (= [3] (regions-touched #(jtms/set-blocked tms #{1000}))))))
  (testing "unblocking is equally local"
    (let [tms (fan-of 500)]
      (jtms/set-blocked tms #{1000})
      (is (= [1] (regions-touched #(jtms/set-blocked tms #{}))))))
  (testing "a call that changes nothing does no work at all"
    (let [tms (fan-of 500)]
      (jtms/set-blocked tms #{1000})
      (is (= [] (regions-touched #(jtms/set-blocked tms #{1000})))
          "re-stating the same blocked set must not relabel anything")
      (is (= [1] (regions-touched #(jtms/set-blocked tms #{})))
          "while a real change still relabels its region")))
  (testing "only the justifications whose status moved seed the region"
    (let [tms (fan-of 500)]
      (jtms/set-blocked tms #{1000 1001})
      ;; 1000 stays blocked, 1001 lifts, 1002 arrives: two changed, two conclusions
      (is (= [2] (regions-touched #(jtms/set-blocked tms #{1000 1002})))))))

;; ---- invariant 2, continued: the sweep is region-local too ---------------

;; A justification the TMS can *read* is a justification the TMS did work on.  This
;; wrapper is an ILookup that records its own id whenever any field of it is read, so
;; a test can name the exact set of justifications an operation touched — the same
;; move as `regions-touched`, one level down, and equally immune to machine speed.
;; The network normalizes what it is handed (`jtms/graph-just`, which is what lets the
;; two representations store equal values), so the probe goes on what it *stored*:
;; `watch-justs` rebuilds the network over wrapped copies, and every reader below
;; reaches them by keyword lookup.
(deftype CountingJust [m id touched]
  clojure.lang.ILookup
  (valAt [_ k]    (swap! touched conj id) (get m k))
  (valAt [_ k nf] (swap! touched conj id) (get m k nf)))

(defn- watch-justs
  "The same network with every stored justification wrapped in a read-counting proxy."
  [tms touched]
  (jtms/->RefTms
   (atom (update @tms :justs
                 #(into {} (map (fn [[jid j]] [jid (->CountingJust (into {} j) jid touched)])) %)))
   (java.util.concurrent.atomic.AtomicReference. nil)))

(defn- sweepable-fan
  "`n` independent premise ⇒ conclusion pairs as background, plus a separate two-link
  chain 900000 ⇒ 900001 ⇒ 900002 whose first justification (990001) is blocked — so
  900001 and 900002 are OUT and a sweep collects exactly them.  The swept
  region is two nodes at every `n`; only the background grows."
  [n]
  (let [tms (jtms/create-tms)]
    (dotimes [i n]
      (premise tms (* 2 i))
      (justify tms (+ 1000 i) [(* 2 i)] (inc (* 2 i))))
    (premise tms 900000)
    (justify tms 990001 [900000] 900001)
    (justify tms 990002 [900001] 900002)
    (jtms/set-blocked tms #{990001})
    tms))

(defn- justs-touched
  "The ids of the justifications `sweep!` read while collecting the blocked chain out
  of a graph with `n` background pairs."
  [n]
  (let [touched (atom #{})
        tms     (watch-justs (sweepable-fan n) touched)]
    (let [{:keys [removed-sentexes]} (jtms/sweep! tms [900001])]
      (assert (= #{900001 900002} (set removed-sentexes))))
    @touched))

(deftest sweeping-touches-only-the-swept-region
  ;; The justifications to tear down are named by the dead nodes' own :supports and
  ;; :consequences.  Finding them by scanning the whole :justs map instead would be
  ;; work proportional to the KB on every sweep — and `exceptWhen` makes sweeping
  ;; routine, so a run of them would be quadratic.  Counting reads, not milliseconds:
  ;; a scan is visible here as the background justifications turning up in the set.
  (let [small (justs-touched 50)
        big   (justs-touched 2000)]
    (is (= #{990001 990002} small)
        "a sweep read a justification outside the chain it was collecting")
    ;; counts, not the sets themselves — a scan's failure output would otherwise be
    ;; two thousand ids long
    (is (= (count small) (count big))
        (str "sweep cost grew with the graph: " (count small) " justifications touched "
             "at n=50, " (count big) " at n=2000"))))

;; ---- recovery ------------------------------------------------------------

(deftest a-whole-graph-relabel-starts-from-an-empty-blocked-set
  ;; `relabel` exists for `recover`, which rebuilds the network from the durable
  ;; store.  Nothing about an exception is stored, so a stale block must not survive
  ;; the rebuild — recovery lands unblocked and the caller re-evaluates.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (is (not (jtms/in? tms 2)))
    (jtms/relabel tms)
    (is (empty? (jtms/blocked tms)))
    (is (jtms/in? tms 2) "the conclusion is believed again until the caller re-blocks")))
