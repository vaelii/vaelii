;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-dense-oracle-test
  "The dense truth-maintenance network answers exactly as the reference does.

  `vaelii.impl.dense-jtms` is not a swap of one data structure for another: bitmaps
  are mutable and the reference is an atom over a persistent map, so the whole
  relabel — the affected region, the two least fixpoints, the class iteration and the
  sweep — is written a second time against the dense structures.  Duplicated
  algorithms drift, and belief is the last thing in the engine that may drift
  silently: a wrong label does not throw, it just answers a query differently.

  So this is the gate, in the shape `dense_kv_oracle_test` and
  `columnar_index_oracle_test` established for the index: drive **both**
  implementations through the same randomized operation stream and compare after
  *every* step.  The comparison is the whole network — `jtms/snapshot` — not a
  sampled read, because a divergence in `:groundable` is invisible to `in?` until a
  retraction three operations later collects the wrong node.

  Two things are compared as sets rather than sequences.  A retraction's
  `:removed-sentexes` / `:removed-justifications` are unordered by contract (the
  caller `doseq`es over them to delete records, and only their *count* reaches the
  public API); the reference happens to emit hash-map iteration order and the dense
  one sorted order, and pinning either would be pinning an accident.

  Pure — no store, no fixture: a TMS is a graph of integers and needs neither."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.jtms :as jtms]))

;; ---- comparison ---------------------------------------------------------

(defn- normalize
  "Both snapshots in one canonical shape.  Only the removal *sets* are loosened (see
  the ns docstring); everything else is compared exactly as stored."
  [snap]
  (-> snap
      (update :nodes (fn [ns] (into {} (map (fn [[d n]] [d (dissoc n :datum)])) ns)))))

(defn- same?
  "Do the two networks hold the same graph, the same beliefs and the same derived
  state?  Returns nil when equal, else **every** differing key with its two values.

  All of them, not the first: a whole-map mismatch on nine keys names none of them,
  but reporting only the first names the wrong one — the keys are compared in sorted
  order, so `:classes` would mask a `:groundable` divergence it is merely a symptom of."
  [ref dns]
  (let [a (normalize (jtms/snapshot ref))
        b (normalize (jtms/snapshot dns))
        diffs (into {} (for [k (sort (keys a))
                             :when (not= (get a k) (get b k))]
                         [k {:reference (get a k) :dense (get b k)}]))]
    (when (seq diffs) diffs)))

(defn- removals= [a b]
  (and (= (set (:removed-sentexes a)) (set (:removed-sentexes b)))
       (= (set (:removed-justifications a)) (set (:removed-justifications b)))
       (= (count (:removed-sentexes a)) (count (:removed-sentexes b)))
       (= (count (:removed-justifications a)) (count (:removed-justifications b)))))

;; ---- the operation stream ----------------------------------------------
;;
;; Operations are *data*, applied to both networks, so a failure prints the exact
;; sequence that produced it and can be replayed by hand.

(defn- apply-op!
  "Run one op against `t`, returning whatever it produced (nil for the pure mutations)."
  [t [op & args]]
  (case op
    :premise      (let [[d s] args] (jtms/add-premise t d s) nil)
    :ensure       (let [[d dep] args] (jtms/ensure-node t d dep) nil)
    ;; every antecedent gets a node first, and so does the consequence — the engine's
    ;; own discipline (a justification's antecedents are handles of stored datums, each
    ;; already a premise or an ensured node).  Neither implementation is specified when
    ;; that is violated: the reference grows a node with no `:depth` and the next
    ;; `ensure-node` on it throws, so a generator that skipped this would be comparing
    ;; two readings of undefined behaviour.
    ;; the informant is a rule handle conjoined as an antecedent when given — the
    ;; engine's own firing shape (`chain/derive-conclusion` conjoins `:rule-handle`) —
    ;; else the symbolic placeholder
    :justify      (let [[jid antes c s inf] args]
                    (doseq [a antes] (jtms/ensure-node t a 1))
                    (jtms/ensure-node t c 1)
                    (jtms/add-justification t (jtms/->just jid (or inf 'rule) antes c {} s))
                    nil)
    :restrength   (let [[inf s] args] (jtms/restrength-informant t inf s) nil)
    :defeat       (do (jtms/defeat t (first args)) nil)
    :clear-defeat (do (jtms/clear-defeats! t) nil)
    :set-blocked  (do (jtms/set-blocked t (first args)) nil)
    :block        (do (jtms/block t (first args)) nil)
    :unblock      (do (jtms/unblock t (first args)) nil)
    :supersede    (do (jtms/supersede t (first args)) nil)
    :suspend      (do (jtms/suspend-premise t (first args)) nil)
    :retract      (jtms/retract! t (first args))
    :sweep        (jtms/sweep! t (first args))
    :reset-touch  (do (jtms/reset-touched! t) nil)
    :relabel      (do (jtms/relabel t) nil)))

(defn- gen-ops
  "A random operation stream over a small datum space, weighted so the interesting
  states are actually reached: enough premises and justifications to build a layered
  graph, then defeats, blocks, supersessions, retractions and sweeps over it.

  `datums` is kept small on purpose — a wide sparse graph never exercises the shared
  antecedent, the re-derivation fast path, or the multi-witness revival that the
  region fixpoint exists for.

  **A justification id is never reused for a different justification**, because
  `p/next-id` is monotonic and the engine cannot produce one that is.  It matters more
  than it sounds: re-binding a live id makes the graph *inconsistent* — a node's
  `:supports` still names the id while the justification now concludes somewhere else —
  and the class fixpoint propagates along `:consequence` edges, so a node can end up
  depending on a class the propagation can never reach it from.  In that state the
  answer legitimately depends on the order members are visited, and BOTH
  implementations are order-dependent; comparing them there would be comparing two
  readings of a graph the engine cannot build.  Re-*asserting* an existing
  justification verbatim is a different thing entirely — it is the redundant-witness
  case the `add-just*` fast path exists for, so the generator does that deliberately."
  [^java.util.Random rng n datums]
  (let [d    #(long (.nextInt rng (int datums)))
        str* #(if (zero? (.nextInt rng 3)) :monotonic :default)]
    (first
     (reduce
      (fn [[ops issued next-jid] _]
        (let [reissue #(when (seq issued) (nth issued (.nextInt rng (count issued))))
              ;; a jid to block/unblock: a live one when there is one, else anything
              some-jid #(or (some-> (reissue) second) (long (+ 1000 (.nextInt rng 20))))
              op (case (.nextInt rng 14)
                   (0 1 2) [:premise (d) (str*)]
                   3       [:ensure (d) (.nextInt rng 4)]
                   (4 5 6 7)
                   (if (and (seq issued) (zero? (.nextInt rng 4)))
                     (reissue)                      ; the redundant-witness fast path
                     (let [k     (inc (.nextInt rng 2))
                           antes (vec (distinct (repeatedly k d)))
                           ;; half the fresh justifications carry an integer informant
                           ;; conjoined as an antecedent, so `:restrength` has real
                           ;; work — the engine's own firing shape
                           inf   (when (zero? (.nextInt rng 2)) (first antes))]
                       [:justify next-jid antes (d) (str*) inf]))
                   8       [:defeat (vec (distinct (repeatedly (inc (.nextInt rng 2)) d)))]
                   9       [:clear-defeat]
                   10      [:set-blocked (vec (distinct (repeatedly (.nextInt rng 3) some-jid)))]
                   11      (if (zero? (.nextInt rng 2))
                             [:block [(some-jid)]]
                             [:unblock [(some-jid)]])
                   12      [:retract (d)]
                   13      (case (.nextInt rng 5)
                             0 [:sweep [(d)]]
                             1 [:supersede (into {} (for [_ (range (.nextInt rng 2))]
                                                      [(d) {:rep (d)}]))]
                             2 [:reset-touch]
                             3 [:suspend (d)]
                             4 [:restrength (d) (str*)]))
              fresh? (and (= :justify (first op)) (= next-jid (second op)))]
          [(conj ops op)
           (if fresh? (conj issued op) issued)
           (if fresh? (inc next-jid) next-jid)]))
      [[] [] 1000]
      (range n)))))

;; ---- the differential run ----------------------------------------------

(defn- run-stream
  "Apply `ops` to a fresh pair and compare after every step.  Returns nil on agreement,
  else a map naming the op index, the op, and what differed."
  [ops]
  (let [ref (jtms/create-tms)
        dns (dense/create-dense-tms)]
    (first
     (keep-indexed
      (fn [i op]
        (let [ra (apply-op! ref op)
              rb (apply-op! dns op)]
          (cond
            (and (map? ra) (not (removals= ra rb)))
            {:at i :op op :reference-removals ra :dense-removals rb}

            :else
            (when-let [d (same? ref dns)]
              (assoc {:diffs d} :at i :op op)))))
      ops))))

(deftest ^:slow streams-are-not-vacuous
  ;; Agreement between two networks that both did nothing is worth nothing.  Before
  ;; trusting the comparison, pin that the generated streams actually reach every
  ;; state the comparison is supposed to cover — a generator tweak that stopped
  ;; producing sweeps (or defeats, or monotonic classes) would otherwise leave the
  ;; oracle green and empty.
  (let [tally (reduce
               (fn [acc seed]
                 (let [ops (gen-ops (java.util.Random. seed) 60 8)
                       t   (jtms/create-tms)
                       removed (reduce (fn [n op]
                                         (let [r (apply-op! t op)]
                                           (if (map? r) (+ n (count (:removed-sentexes r))) n)))
                                       0 ops)
                       s   @t]
                   (-> acc
                       (update :removed + removed)
                       (update :derived + (count (remove (comp :premise? val) (:nodes s))))
                       (update :justs + (count (:justs s)))
                       (update :defeated + (count (:defeated s)))
                       (update :blocked + (count (:blocked s)))
                       (update :superseded + (count (:superseded s)))
                       (update :monotonic + (count (:classes s))))))
               (zipmap [:removed :derived :justs :defeated :blocked :superseded :monotonic]
                       (repeat 0))
               (range 200))]
    (doseq [[k n] tally]
      (is (pos? n) (str "the streams never produced any " (name k))))))

(deftest ^:slow randomized-streams-agree
  (testing "200 random operation streams, compared after every single step"
    (doseq [seed (range 200)]
      (let [rng (java.util.Random. seed)
            ops (gen-ops rng 60 8)]
        (is (nil? (run-stream ops))
            (str "seed " seed))))))

(deftest ^:slow wider-graphs-agree
  (testing "longer streams over a wider datum space — deeper chains, more witnesses"
    (doseq [seed (range 40)]
      (let [rng (java.util.Random. (+ 10000 seed))
            ops (gen-ops rng 250 24)]
        (is (nil? (run-stream ops))
            (str "seed " seed))))))

;; ---- the shapes that must not be left to chance ------------------------
;;
;; A random stream reaches these eventually, but only a named test *says* they are
;; covered — and each is a place the two implementations could plausibly diverge.

(defn- both
  "Build the same network in both implementations, run `f` on each, and assert the
  results and the resulting networks are equal.  Returns the reference's result."
  [build f]
  (let [ref (jtms/create-tms)
        dns (dense/create-dense-tms)]
    (build ref) (build dns)
    (let [ra (f ref), rb (f dns)]
      (is (nil? (same? ref dns)) "the networks agree")
      (is (= ra rb) "and so do the results")
      ra)))

(deftest strength-propagates-identically
  (testing "a conclusion is no stronger than the weakest thing it rests on"
    ;; 1 monotonic, 2 default; a bare (monotonic) rule over both must confer :default,
    ;; and over 1 alone :monotonic.  This is the recursive class equation the dense
    ;; implementation solves with a bitmap least fixpoint.
    (is (= [:monotonic :default :default]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/add-premise t 2 :default)
                   (jtms/ensure-node t 3 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 3 {} :monotonic))
                   (jtms/ensure-node t 4 1)
                   (jtms/add-justification t (jtms/->just 11 'r [1 2] 4 {} :monotonic)))
                 (fn [t] [(jtms/defeat-class t 3) (jtms/defeat-class t 4)
                          (jtms/defeat-class t 2)]))))))

(deftest restrength-follows-the-informant
  (testing "the rule-contribution slot moves with the informant, in both representations"
    ;; premise 1 is the fact, premise 2 the rule — conjoined as an antecedent and named
    ;; as the informant, the engine's firing shape.  The justification confers :default
    ;; until the rule resolves strict, then :monotonic; the informant is excluded from
    ;; the antecedent cap, so the flip is the whole change.
    (is (= [:default :monotonic]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/add-premise t 2 :default)
                   (jtms/ensure-node t 3 1)
                   (jtms/add-justification t (jtms/->just 10 2 [1 2] 3 {} :default)))
                 (fn [t]
                   (let [before (jtms/defeat-class t 3)]
                     (jtms/restrength-informant t 2 :monotonic)
                     [before (jtms/defeat-class t 3)]))))))
  (testing "and a symbolic informant, which no rule handle names, moves nothing"
    (is (= [:default :default]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/ensure-node t 3 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 3 {} :default)))
                 (fn [t]
                   (let [before (jtms/defeat-class t 3)]
                     (jtms/restrength-informant t 'r :monotonic)
                     [before (jtms/defeat-class t 3)])))))))

(deftest deep-chain-classes-agree
  (testing "a class rises through a chain — the fixpoint, not a single pass"
    ;; 0 monotonic, then 0=>1=>2=>...=>n by bare rules: every node must end :monotonic,
    ;; which a single ordered pass would get right and a *wrongly ordered* one would not.
    (is (= (repeat 12 :monotonic)
           (both (fn [t]
                   (jtms/add-premise t 0 :monotonic)
                   (doseq [i (range 12)]
                     (jtms/ensure-node t (inc i) 1)
                     (jtms/add-justification t (jtms/->just (+ 100 i) 'r [i] (inc i) {} :monotonic))))
                 (fn [t] (map #(jtms/defeat-class t %) (range 1 13))))))))

(deftest revival-by-a-second-witness
  (testing "retracting one of two supports leaves the conclusion believed"
    (is (= [true true]
           (both (fn [t]
                   (jtms/add-premise t 1 :default)
                   (jtms/add-premise t 2 :default)
                   (jtms/ensure-node t 3 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 3 {} :monotonic))
                   (jtms/add-justification t (jtms/->just 11 'r [2] 3 {} :monotonic)))
                 (fn [t]
                   (jtms/retract! t 1)
                   [(jtms/in? t 3) (jtms/in? t 2)]))))))

(deftest blocking-suppresses-groundability-and-sweeps
  (testing "a blocked justification is invalid, so its conclusion is collected"
    ;; the exceptWhen contract: blocking is garbage collection, not defeat
    (is (= [false false]
           (both (fn [t]
                   (jtms/add-premise t 1 :default)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 2 {} :monotonic)))
                 (fn [t]
                   (jtms/set-blocked t #{10})
                   (jtms/sweep! t [2])
                   [(jtms/in? t 2) (jtms/known-datum? t 2)]))))))

(deftest defeat-keeps-a-defeated-node-for-revival
  (testing "a defeated node stays groundable and comes back when the defeat lifts"
    (is (= [false true true]
           (both (fn [t]
                   (jtms/add-premise t 1 :default)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 2 {} :monotonic)))
                 (fn [t]
                   (jtms/defeat t [2])
                   (let [out (jtms/in? t 2)
                         kept (jtms/known-datum? t 2)]
                     (jtms/clear-defeats! t)
                     [out kept (jtms/in? t 2)])))))))

(deftest supersession-subtracts-from-reported-belief-only
  (testing "a superseded datum leaves the fixpoint alone but stops being believed"
    (is (= [false true]
           (both (fn [t]
                   (jtms/add-premise t 1 :default)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 2 {} :monotonic)))
                 (fn [t]
                   (jtms/supersede t {1 {:rep 9}})
                   ;; 1 is not believed, but 2 — justified BY it — still is
                   [(jtms/in? t 1) (jtms/in? t 2)]))))))

(deftest redundant-justification-is-a-no-op-in-both
  (testing "the fast path that keeps a recursive load linear moves nothing"
    (is (= [true :monotonic]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 2 {} :monotonic)))
                 (fn [t]
                   ;; a second witness for an already-believed conclusion, conferring no
                   ;; more than it already holds
                   (jtms/add-justification t (jtms/->just 11 'r [1] 2 {} :monotonic))
                   [(jtms/in? t 2) (jtms/defeat-class t 2)]))))))

(deftest cyclic-support-is-not-self-justifying
  (testing "a cycle with no ground outside it never enters the least fixpoint"
    (is (= [false false]
           (both (fn [t]
                   (jtms/ensure-node t 1 1)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [2] 1 {} :monotonic))
                   (jtms/add-justification t (jtms/->just 11 'r [1] 2 {} :monotonic)))
                 (fn [t] [(jtms/in? t 1) (jtms/in? t 2)]))))))

(deftest whole-graph-relabel-agrees
  (testing "the recover-only relabel, including its blocked/superseded reset"
    (is (= [true true #{} {}]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 2 {} :monotonic))
                   (jtms/set-blocked t #{10})
                   (jtms/supersede t {1 {:rep 9}}))
                 (fn [t]
                   (jtms/relabel t)
                   [(jtms/in? t 1) (jtms/in? t 2)
                    (jtms/blocked t) (jtms/superseded t)]))))))

(deftest retracting-an-unknown-datum-no-ops-in-both
  (is (= {:removed-sentexes [] :removed-justifications []}
         (both (fn [t] (jtms/add-premise t 1 :monotonic))
               (fn [t] (jtms/retract! t 999999))))))

(deftest suspending-a-premise-is-a-retraction-that-deletes-nothing
  (testing "belief goes exactly where a retraction would put it, and comes back"
    ;; 1 is a premise supporting 2 supporting 3.  Suspending 1 must take all three OUT
    ;; in both networks — and leave every node and justification in place, which is what
    ;; `core/preview` rolls back through.  `same?` compares the whole network, so a
    ;; dense implementation that swept here would be caught by the build, not the labels.
    (is (= [[false false false] [true true true]]
           (both (fn [t]
                   (jtms/add-premise t 1 :default)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'r [1] 2 {} :monotonic))
                   (jtms/ensure-node t 3 2)
                   (jtms/add-justification t (jtms/->just 11 'r [2] 3 {} :monotonic)))
                 (fn [t]
                   (jtms/suspend-premise t 1)
                   (let [out (mapv #(jtms/in? t %) [1 2 3])
                         _   (is (= 3 (count (jtms/datums t))) "nothing was swept")
                         _   (is (= 2 (count (jtms/justifications t))))]
                     (jtms/add-premise t 1 :default)
                     [out (mapv #(jtms/in? t %) [1 2 3])])))))))

(deftest suspending-an-unknown-datum-no-ops-in-both
  (testing "no node is materialized for it — the mistake `retract*` documents"
    (is (= [1] (both (fn [t] (jtms/add-premise t 1 :monotonic))
                     (fn [t] (jtms/suspend-premise t 999999) (vec (jtms/datums t))))))))

;; ---- the justification columns ------------------------------------------
;;
;; The dense network stores no justification *object*: the fields belief reads are
;; primitive columns keyed by id, and a record is rebuilt only when a caller asks for
;; one.  The randomized streams above compare `:justs` after every step, so a column
;; that failed to round-trip shows up there — but they issue one shape of
;; justification, so these pin the shapes they do not reach.

(deftest the-network-keeps-the-graph-and-not-the-bindings
  (testing "the firing's variable map is the record store's, not the network's"
    ;; The one field belief never reads, and 80 of 277 bytes per justification
    ;; (`lein bench-jtms`).  Both representations must drop it, or they disagree —
    ;; and `settle` re-reads it from the store when it re-evaluates an exception.
    (is (nil? (both (fn [t]
                      (jtms/add-premise t 1 :monotonic)
                      (jtms/ensure-node t 2 1)
                      (jtms/add-justification
                       t (jtms/->just 10 'r [1] 2 '{?var0 Muffet ?var1 Rex} :monotonic)))
                    (fn [t] (:bindings (jtms/justification t 10))))))))

(deftest a-justification-round-trips-through-the-columns
  (testing "every field belief reads survives being taken apart and put back"
    ;; The informant (7) is also an antecedent, and a *weaker* premise than the rest:
    ;; `conferred-class` has to skip it, so 4 comes out :monotonic instead of capped at
    ;; the rule's own class.  That is the one place the informant is read for something
    ;; other than equality, and the only one that can tell an int column from an
    ;; object one.
    (is (= [10 7 [1 2 7] 4 :monotonic #{3} :monotonic]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/add-premise t 2 :monotonic)
                   (jtms/add-premise t 7 :default)
                   (jtms/ensure-node t 3 0)               ; OUT: the NAF antecedent
                   (jtms/ensure-node t 4 1)
                   (jtms/add-justification
                    t (assoc (jtms/->just 10 7 [1 2 7] 4 {} :monotonic) :out #{3})))
                 (fn [t] (let [j (jtms/justification t 10)]
                           [(:id j) (:informant j) (:antecedents j) (:consequence j)
                            (:strength j) (:out j) (jtms/defeat-class t 4)]))))))
  (testing "a symbolic informant is not a handle, and comes back as itself"
    ;; `special` licenses merges and lifts under a predicate *name* rather than a rule
    ;; handle, so the informant column cannot assume an integer.
    (is (= 'rewriteOf
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification t (jtms/->just 10 'rewriteOf [1] 2 {} :monotonic)))
                 (fn [t] (:informant (jtms/justification t 10))))))))

(deftest a-swept-justification-leaves-no-column-behind
  (testing "an id reused after a sweep inherits nothing from its predecessor"
    ;; Seven columns are torn down by hand where a map holds one entry, so a missed
    ;; one is a stale field waiting for the next justification to take the id.
    ;; Re-issuing 10 with a different informant, strength, antecedents and `out` reads
    ;; back whatever the sweep failed to clear.
    (is (= [(jtms/->just 10 'fresh [5] 6 nil :default) :default #{10} #{10}]
           (both (fn [t]
                   (jtms/add-premise t 1 :monotonic)
                   (jtms/ensure-node t 2 1)
                   (jtms/add-justification
                    t (assoc (jtms/->just 10 'gone [1] 2 {} :monotonic) :out #{1}))
                   (jtms/retract! t 1)                      ; 2 ungroundable => both swept
                   (jtms/add-premise t 5 :default)
                   (jtms/ensure-node t 6 1)
                   (jtms/add-justification t (jtms/->just 10 'fresh [5] 6 {} :default)))
                 (fn [t] [(jtms/justification t 10) (jtms/defeat-class t 6)
                          (jtms/supports t 6) (jtms/dependents t 5)]))))))

(deftest reads-are-total
  (testing "every read answers an unknown datum — nil included — as absent"
    ;; Not hypothetical: `handle-of` returns nil for a sentence that is not stored, and
    ;; `core/defeat-class` is called with exactly that (property_test's `observe` does
    ;; it on every generated scenario).  The reference is total because a persistent map
    ;; is; the dense one has to be made so deliberately.
    (let [absent [nil false false nil 0 #{} #{} nil false false]]
      (is (= [absent absent]
             (both (fn [t] (jtms/add-premise t 1 :monotonic))
                   (fn [t]
                     (vec (for [d [nil 999999]]
                            [(jtms/defeat-class t d) (jtms/in? t d) (jtms/known-datum? t d)
                             (jtms/premise-strength t d) (jtms/depth t d)
                             (jtms/supports t d) (jtms/dependents t d)
                             (jtms/justification t d) (jtms/premise? t d)
                             (jtms/superseded? t d)])))))))))
