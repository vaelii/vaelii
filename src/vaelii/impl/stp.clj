;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.stp
  "A **simple temporal problem** — the metric half of time, where the qualitative calculi
  say only which of two things came first.  A constraint is a bound on the *gap* between
  two instants,

    lo ≤ t(Q) − t(P) ≤ hi

  and a set of them is closed by all-pairs shortest paths over the distance graph they
  describe.  The closure answers the tightest gap the constraints entail between *any* two
  instants, including pairs nobody wrote a constraint for, and a **negative cycle** in that
  graph is the proof that no assignment of times satisfies them all.

  This is not a relation algebra and it is deliberately not forced through
  `vaelii.impl.qcn`: there is no finite set of jointly-exhaustive base relations here, and
  no composition table — the constraint on a pair is an interval of the reals, composition
  is addition and tightening is `min`.  So it is its own small algorithm, written the way
  `qcn` is written: **pure data in, pure data out**, knowing nothing about a KB, with the
  KB reading and the prover in their own marked section below.

  **Constraints are measures**, not bare numbers.  A stated one is the ordinary fact
  `(temporalDistance P Q M)` where `M` is a `(QuantityFn N Unit)` for an exact separation or
  a `(QuantityIntervalFn Lo Hi Unit)` for a bounded one, and a negative magnitude says Q
  falls before P.  Every magnitude normalizes through `provers/normalize-quantity` against
  the KB's `dimensionOf` / `conversionFactor` table, so the arithmetic happens in the
  dimension's base unit and an answer is rendered back in that same unit — exactly the
  contract `vaelii.impl.duration` follows, so a separation and a duration are written the
  same way and compare directly.  Constraints spanning more than one dimension are refused
  rather than mixed.

  **Bind or check**, like `EvaluateProver` and the duration arithmetic: an open measure is
  bound to the tightest separation entailed, and a ground one is *entailed* exactly when the
  derived bound is contained in it — a stated bound is a weaker claim than the derived one,
  so the derived one implies it.

  **The bridge to the interval algebra** is `(startOf I P)` / `(endOf I P)`, which name an
  interval's two bounding instants.  With them a metric fact and an Allen relation are about
  the same thing, and `allen-narrowing` reads the closure back as constraints on the
  *interval* relations: if the closure puts A's end strictly before B's start then A is
  `before` B, and so on for all thirteen.  It narrows and never widens — it answers relation
  sets and mutates nothing — and `vaelii.impl.interval` hands
  `allen-narrowing-with-support` to `qcn-kb/calculus` as the Allen network's second
  reader, so a metric fact narrows the interval network beside the stored Allen facts and
  the derived relation names both.  The dependency therefore runs *interval → stp* and
  never back: the thirteen relations this namespace needs are `endpoint-signature`'s own
  keys (`allen-relations`).

  `vaelii.impl.duration` is the other consumer: `overlap-window-with-support` bounds how
  long two intervals overlap from their endpoints alone, which is what turns an indefinite
  overlap into a real figure.

  The prover is **opt-in**: register it with `vaelii.core/add-prover`, and until then a KB
  stores and retrieves `temporalDistance` facts as ordinary facts without paying for the
  closure.  The vocabulary ships in `kb/upper/CxTime.txt` either way.  See
  docs/stp.md."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

;; =========================================================================
;; THE ALGORITHM — pure data in, pure data out.  No KB, no context, no belief.
;; =========================================================================

;; A **network** is `{[p q] → [lo hi]}`, meaning `lo ≤ t(q) − t(p) ≤ hi`, both directions
;; stored (`[q p]` holds `[-hi -lo]`); an unrecorded pair is unbounded.  So a network is a
;; *value*, which is what lets a caller memoize an expensive closure on its content — the
;; same discipline `qcn` follows.

(def unbounded
  "The constraint on a pair nothing is known about: the whole real line."
  [##-Inf ##Inf])

(defn constraint
  "The bound on `t(q) − t(p)` in `net`: exactly zero on the diagonal, the recorded interval,
  else unbounded.  The diagonal answers zero *whatever* is recorded there, because the only
  gap between an instant and itself is none."
  [net p q]
  (if (= p q) [0 0] (get net [p q] unbounded)))

(defn nodes
  "Every instant named by a constraint in `net`."
  [net]
  (into #{} (mapcat identity) (keys net)))

(defn narrow
  "Intersect the constraint on `[p q]` with `[lo hi]`, writing the converse bound on
  `[q p]` with it.  Intersection is `[max of the los, min of the his]` — commutative and
  associative, so a network is a function of the constraints alone and never of the order
  they were read in."
  [net p q lo hi]
  (let [[lo0 hi0] (get net [p q] unbounded)
        lo* (max lo0 lo)
        hi* (min hi0 hi)]
    (assoc net [p q] [lo* hi*] [q p] [(- hi*) (- lo*)])))

(defn- unsatisfiable-as-given?
  "Is one recorded constraint unsatisfiable *before* any closure?  Two ways, and both are
  the metric echo of what `qcn/unsatisfiable-as-given?` refuses.

  Its bounds are **crossed** — `lo > hi` asks for a gap that is at once too large and too
  small.  The closure does catch this, as the negative cycle p→q→p, but only when both
  nodes are passed to it, and passing every node is the caller's obligation; checking here
  makes the verdict on a single self-contradicting fact independent of what else is present.

  Or it is a **diagonal** constraint excluding zero: a claim that an instant falls some
  non-zero time from itself.  No path ever runs from a node to itself in one step, and
  `constraint` answers zero on the diagonal whatever is recorded, so such a claim would
  otherwise be silently dropped rather than reported.

  Both read to the **tolerance**, and it is the same `provers/*quantity-tolerance*` a
  measure comparison is held to: a crossing narrower than the epsilon is two spellings of
  one figure, not a contradiction — see `close`."
  [[[p q] [lo hi]]]
  (let [eps provers/*quantity-tolerance*]
    (or (> lo (+ hi eps))
        (and (= p q) (not (and (<= lo eps) (>= hi (- eps))))))))

(defn unsatisfiable-pairs
  "The pairs of `net` that `unsatisfiable-as-given?` refuses — what a reader wrote down that
  no assignment of times can satisfy, before any closure.  Empty when the network is
  unsatisfiable only *derivably*, through a cycle, which is the case a report has no single
  pair to blame for."
  [net]
  (into #{} (keep (fn [[pair :as entry]]
                    (when (unsatisfiable-as-given? entry) pair)))
        net))

;; ---- the closure, over a matrix ------------------------------------------
;; The distance graph is a **`double[]` of n², row-major over `node-vec`'s positions**,
;; and the three functions below share that representation: `d[p·n + q]` is the current
;; upper bound on `t(q) − t(p)`, `##Inf` is the absence of an edge, and the diagonal
;; starts at zero so a self-distance that ends up negative is a cycle and nothing else.
;;
;; A persistent map keyed `[p q]` says the same thing and costs a two-element vector per
;; probe: Floyd–Warshall reads and writes n³ of them, which at a hundred instants is two
;; million allocations for one closure.  The array is read and written in place, so the
;; pass allocates nothing at all — and it is *inside* the memo either way
;; (`closure`, keyed on the network value), so what this changes is the cost of a cache
;; miss and never how often one happens.

(defn- node-index
  "`{node → position}` over `node-vec` — how a pair reaches its cell."
  [node-vec]
  (into {} (map-indexed (fn [i x] [x i])) node-vec))

(defn- distance-matrix
  "The network as the `n×n` matrix above.  Only finite weights are edges: an unbounded side
  constrains nothing and is the absence of an edge, which is also what keeps infinities out
  of the arithmetic.  A pair naming an instant outside `node-vec` is dropped — no path is
  ever composed through it and no read-back ever reaches it, so passing every node the
  network mentions is the caller's obligation (`close`)."
  ^doubles [net node-vec]
  (let [n   (long (count node-vec))
        idx (node-index node-vec)
        ^doubles d (double-array (* n n) ##Inf)]
    (dotimes [i n] (aset d (+ (* i n) i) 0.0))
    (doseq [[[p q] [_ hi]] net]
      (let [ip (idx p), iq (idx q), w (double hi)]
        (when (and ip iq (not= ip iq) (Double/isFinite w))
          (let [k (+ (* (long ip) n) (long iq))]
            (when (< w (aget d k)) (aset d k w))))))
    d))

(defn- shortest-paths!
  "Floyd–Warshall in place over `d`: `d[p·n + q]` becomes the least total weight of any path
  from p to q, which is the tightest upper bound on `t(q) − t(p)` the constraints entail.
  An `##Inf` entry is an unbounded gap and takes no part — the guards skip it rather than
  letting `∞ + ∞` into the sum.  Answers `d`, which it has mutated.

  `nxt` is the reconstruction table, or nil for a caller that only wants the distances:
  `nxt[p·n + q]` holds the **next node after p** on the current best p → q path, so a path
  is walked forward one edge at a time rather than reassembled from midpoints.  The
  successor form and not the midpoint one, because the midpoint form is only sound while
  every sub-path is final: an entry improved at a late `k` can name a midpoint whose own
  entry was later rewritten to point back through the pair being reconstructed, and the
  reassembly then recurses forever.  A successor chain cannot do that — it only ever
  walks forward, and `path-edges` bounds the walk besides.

  Maintaining it costs one `aget` and one `aset` on an improvement, so the pass is written
  once and the support caller is the only one that allocates the array.

  The result does not depend on the order of the nodes: a shortest path is a property of
  the graph, and the loop is the textbook triple that computes it in one O(n³) pass."
  (^doubles [^doubles d ^long n] (shortest-paths! d nil n))
  (^doubles [^doubles d ^ints nxt ^long n]
   (dotimes [k n]
     (let [kn (* k n)]
       (dotimes [p n]
         (let [pn  (* p n)
               dpk (aget d (+ pn k))]
           (when (Double/isFinite dpk)
             (dotimes [q n]
               (let [dkq (aget d (+ kn q))]
                 (when (Double/isFinite dkq)
                   (let [w (+ dpk dkq)]
                     (when (< w (aget d (+ pn q)))
                       (aset d (+ pn q) w)
                       (when nxt (aset nxt (+ pn q) (aget nxt (+ pn k))))))))))))))
   d))

(defn- edge-successors
  "The successor table for the **direct** edges of an initialized distance matrix: `j` for
  every finite off-diagonal `d[i·n + j]`, `-1` for the rest.  What `shortest-paths!` grows
  a composed path's successors out of."
  ^ints [^doubles d ^long n]
  (let [nxt (int-array (* n n) -1)]
    (dotimes [i n]
      (let [in (* i n)]
        (dotimes [j n]
          (when (and (not= i j) (Double/isFinite (aget d (+ in j))))
            (aset nxt (+ in j) (int j))))))
    nxt))

(defn- path-edges
  "The edges of the shortest `p → q` path `nxt` records, as `[from to]` index pairs — nil
  when there is no path, and nil when the walk runs past `n` steps.

  The step bound is not belt-and-braces.  A shortest path over a network with no negative
  cycle can be taken simple, and a simple path is at most `n` edges — but a **zero-weight**
  cycle, which is what a chain of gaps that closes exactly is, leaves a successor chain
  free to go round it, and a network of a hundred instants is not a place to find that out
  by recursing.  The caller reads nil as \"say the whole network\" rather than as \"say
  nothing\", so the bound costs breadth and never soundness."
  [^ints nxt ^long n ^long p ^long q]
  (loop [cur p, acc [], steps 0]
    (cond
      (= cur q)     acc
      (>= steps n)  nil
      :else         (let [nx (aget nxt (+ (* cur n) q))]
                      (when-not (neg? nx)
                        (recur (long nx) (conj acc [cur nx]) (inc steps)))))))

(def ^:private ^:const exact-long-double
  "The largest magnitude a `double` still holds every integer below — 2⁵³.  Past it the
  narrowing in `magnitude` would invent digits, so it hands the double back."
  9007199254740992.0)

(defn- magnitude
  "A closed bound read out of the matrix: a **long** where the arithmetic came out whole,
  the double otherwise — the convention `provers/round-magnitude` already renders every
  measure by, so a gap of fifteen seconds reads `15` here and `(QuantityFn 15 Second)`
  there.  An infinite bound is unbounded and stays a double."
  [^double x]
  (if (and (== x (Math/rint x)) (< (- exact-long-double) x exact-long-double))
    (long x)
    x))

(defn- read-back
  "The closed distance matrix as a network again: the bound on `t(q) − t(p)` is `d[p][q]`
  above and `−d[q][p]` below, and a pair bounded on neither side is left unrecorded."
  [^doubles d node-vec]
  (let [n (long (count node-vec))]
    (into {}
          (for [ip    (range n)
                iq    (range n)
                :when (not= ip iq)
                :let  [hi (aget d (+ (* (long ip) n) (long iq)))
                       lo (- (aget d (+ (* (long iq) n) (long ip))))]
                :when (or (Double/isFinite lo) (Double/isFinite hi))]
            [[(nth node-vec ip) (nth node-vec iq)] [(magnitude lo) (magnitude hi)]]))))

(defn negative-cycle-nodes
  "The instants lying on some negative cycle of the closed distance matrix `d` — exactly
  those whose distance to themselves came out below zero.  What a report can name when the
  contradiction is derived rather than written.

  **Below zero by more than the tolerance.**  A cycle is a sum of stored magnitudes, each
  of them a stated figure multiplied by a stored conversion factor, so a chain that closes
  exactly can arrive back a sliver short — ten tenths of a second sum to
  0.9999999999999999, and against a stated second that is a cycle of −1.1e-16.  The band
  is the same one every other magnitude comparison here reads."
  [^doubles d node-vec]
  (let [eps (double provers/*quantity-tolerance*)
        n   (long (count node-vec))]
    (into #{}
          (comp (map-indexed vector)
                (keep (fn [[i x]]
                        (when (< (aget d (+ (* (long i) n) (long i))) (- eps)) x))))
          node-vec)))

(defn close-state
  "All-pairs shortest paths over `net` across `nodes`, as a **closed state** — the network
  the constraints entail together with the distance matrix it was read off and the node
  vector that matrix is laid out over:

      {:net {[p q] → [lo hi]} :node-vec [instant …] :d ^doubles}

  or `:inconsistent`, on the two verdicts `close` describes.

  The matrix rides along for one reason: it is what a *later* constraint is relaxed into
  (`close-state-from`), and rebuilding it from the network costs a map lookup per instant
  pair — which at four hundred instants is more than the update it precedes.  It is written
  once, never after, and every function here that takes a state clones it before touching
  it, so a state is a value like the network in it.

  A caller with no next constraint coming wants `close`, which is this answer's `:net`."
  [net nodes]
  (if (some unsatisfiable-as-given? net)
    :inconsistent
    (let [node-vec (nm/by-print-key nodes)
          closed   (shortest-paths! (distance-matrix net node-vec) (count node-vec))]
      (if (seq (negative-cycle-nodes closed node-vec))
        :inconsistent
        {:net (read-back closed node-vec) :node-vec node-vec :d closed}))))

(defn close
  "All-pairs shortest paths over `net` across `nodes`, returning the tightest network the
  constraints entail — or `:inconsistent` when some instant reaches itself at a negative
  distance, which is a cycle of gaps that must all be closed and cannot be.  A constraint
  unsatisfiable *as given* counts too, whatever the node count: see
  `unsatisfiable-as-given?`.

  `nodes` is what the paths are drawn from, so it is the **caller's** obligation to pass
  every node the network mentions — a node left out is a path never composed.  Passing extra
  nodes is always safe: an isolated one has no finite edge in either direction, so it can
  tighten nothing and can be on no cycle.

  Both verdicts are read to `provers/*quantity-tolerance*`, and that is what makes the
  answer a claim about the *knowledge* rather than about the arithmetic that carried it.  A
  magnitude reaches here multiplied by a stored conversion factor, so one gap written two
  ways — `1.1 Hour` and `66 Minute` — arrives as 3960.0000000000005 and 3960.  Held to an
  exact comparison the pair would cross, a chain of them would close a cycle at −5e-13, and
  a KB whose own `sameQuantity` calls the two equal would have every metric goal in the
  context refused over them.  A contradiction wider than the epsilon is still one.

  `close-state` is the same pass answering the **closure together with the matrix it was
  read off**, for a caller that will be asked again after one more constraint arrives; this
  is that answer's network half, and every caller wanting only the bounds takes it."
  [net nodes]
  (let [s (close-state net nodes)]
    (if (map? s) (:net s) s)))

;; ---- warm-starting: one arriving constraint, not a fresh pass ------------
;;
;; A KB being loaded asks for the closure again after every arriving fact, and all but a
;; handful of the bounds are exactly where the last pass left them.  Closing the whole
;; network again is the cubic loop redoing work it has already done — and the memo above
;; cannot help, because an arriving constraint is a different network and so a different
;; key.
;;
;; The identity that licenses starting from the last answer is the one shortest paths
;; already rest on.  A closed matrix `D` is the least-weight path between every pair; add
;; an edge `p → q` of weight `w` and every path that improves runs `i ⇝ p → q ⇝ j`, so
;;
;;     D'[i][j] = min(D[i][j], D[i][p] + w + D[q][j])
;;
;; is the whole of the update, over every pair at once: O(n²) rather than O(n³), and no
;; approximation — it is the same closure reached without re-deriving what did not move.
;; A path using the new edge *twice* decomposes into two that use it once, so one round is
;; enough unless one of those rounds is negative, which is precisely the case the verdict
;; catches: `D'[p][p]` becomes `min(0, w + D[q][p])`, and that is the weight of the cycle
;; the new edge closes.
;;
;; **It applies to tightening only.**  A retraction, a defeat, a loosened bound — anything
;; that *widens* a constraint — has no such identity: the closed matrix does not record
;; which of its bounds the departing constraint was behind, and a shortest path cannot be
;; run backwards.  `tightening-of?` is the precondition, checked against the network the
;; previous answer was computed from, and a widening pays the whole pass.  That is the
;; honest trade rather than a gap, and it is the same trade `qcn` makes on the qualitative
;; side (docs/qcn.md, "Warm-starting").

(defn tightening-of?
  "Is `net` a pointwise **tightening** of `prior` — is every bound `prior` records at least
  as wide as the one `net` records for the same pair?  A pair `prior` records and `net` does
  not is unbounded in `net`, so it is a tightening only where `prior` left it unbounded too.

  The precondition for `close-state-from`, and separate from it because only the caller
  holds the network the previous answer was computed from."
  [net prior]
  (every? (fn [[pair [lo hi]]]
            (let [[lo* hi*] (get net pair unbounded)]
              (and (>= (double lo*) (double lo)) (<= (double hi*) (double hi)))))
          prior))

(defn- relax-edge!
  "Add the edge `ip → iq` of weight `w` to the closed matrix `d`, in place: every pair whose
  least-weight path now runs through it takes the shorter figure, and `dirty` records which
  cells moved so the read-back can skip the ones that did not.

  `d[i][p]` and `d[q][j]` are **snapshotted** before the sweep.  In the consistent case the
  sweep cannot move either — improving `d[i][p]` through the new edge would mean going round
  a cycle of non-negative weight — but in the inconsistent case it can, and reading a
  half-updated row back into the same update is a reasoning burden the two arrays remove for
  a linear cost.

  The four positions are longs and a double cast in the body rather than hinted in the
  vector: a fn taking primitives is capped at four arguments, and the two arrays have to be
  hinted or every `aget` in the sweep is a reflective call."
  [^doubles d ^booleans dirty n' ip' iq' w']
  (let [n   (long n')
        ip  (long ip')
        iq  (long iq')
        w   (double w')
        col (double-array n)                                ; col[i] = d[i][p]
        row (double-array n)]                               ; row[j] = d[q][j]
    (dotimes [i n] (aset col i (aget d (+ (* i n) ip))))
    (dotimes [j n] (aset row j (aget d (+ (* iq n) j))))
    (dotimes [i n]
      (let [dip (aget col i)]
        (when (Double/isFinite dip)
          (let [base (+ dip w)
                in   (* i n)]
            (dotimes [j n]
              (let [dqj (aget row j)]
                (when (Double/isFinite dqj)
                  (let [cand (+ base dqj)
                        k    (+ in j)]
                    (when (< cand (aget d k))
                      (aset d k cand)
                      (aset dirty k true))))))))))
    d))

(defn- read-back-changed
  "`read-back` restricted to what moved: `prior` with the pairs `dirty` marks rewritten off
  `d`.  A bound only ever tightens, so a pair no cell of touched still reads what `prior`
  says, and no pair is ever dropped.

  The scan runs over **unordered** pairs, and it has to: one closed entry is read off two
  cells — `[p q]` is `d[p][q]` above and `−d[q][p]` below — and the two move independently,
  so a pair either cell of moved has both its entries rewritten and a pair visited twice
  would write both of them twice."
  [prior ^doubles d ^booleans dirty node-vec]
  (let [n (long (count node-vec))]
    (persistent!
     (loop [i 0, acc (transient prior)]
       (if (= i n)
         acc
         (let [p  (nth node-vec i)
               in (* (long i) n)]
           (recur
            (inc i)
            (loop [j (inc i), acc acc]
              (if (= j n)
                acc
                (let [jn (* (long j) n)]
                  (if (or (aget dirty (+ in (long j))) (aget dirty (+ jn (long i))))
                    (let [q  (nth node-vec j)
                          pq (aget d (+ in (long j)))
                          qp (aget d (+ jn (long i)))]
                      (recur (inc j)
                             (-> acc
                                 (assoc! [p q] [(magnitude (- qp)) (magnitude pq)])
                                 (assoc! [q p] [(magnitude (- pq)) (magnitude qp)]))))
                    (recur (inc j) acc))))))))))))

(defn- relaid-matrix
  "The prior state's distance matrix, **copied** onto `node-vec`'s layout — the same figures
  at whatever positions the new vector puts those instants at, with any instant the prior
  never held starting isolated.

  A copy and never the array itself: a state is a value, and two callers reaching one
  cached closure must not be able to see each other's update.  The straight clone is the
  ordinary case, since a constraint usually arrives between instants already there; the
  remap is what an arriving instant costs, and it is quadratic in the *prior* size rather
  than in the new one."
  ^doubles [prior node-vec]
  (let [^doubles old (:d prior)
        old-vec      (:node-vec prior)
        n            (long (count node-vec))]
    (if (= old-vec node-vec)
      (aclone old)
      (let [m     (long (count old-vec))
            idx   (node-index node-vec)
            d     (double-array (* n n) ##Inf)
            remap (int-array m -1)]
        (dotimes [i n] (aset d (+ (* i n) i) 0.0))
        (dotimes [i m] (when-let [ni (idx (nth old-vec i))] (aset remap i (int ni))))
        (dotimes [i m]
          (let [ni (long (aget remap i))]
            (when (>= ni 0)
              (dotimes [j m]
                (let [nj (long (aget remap j))]
                  (when (>= nj 0)
                    (aset d (+ (* ni n) nj) (aget old (+ (* i m) j)))))))))
        d))))

(defn close-state-from
  "`close-state`, **warm-started** off `prior` — a state `close-state` or this function
  returned for a network `net` tightens (`tightening-of?`).  Same value, without the cubic
  pass: only the constraints that moved are relaxed in, one O(n²) update each, and only the
  bounds those updates moved are read back.

  `nodes` carries the obligation `close` states and one more of its own: it must name every
  instant `prior` mentions as well as every one `net` does, since `prior`'s bounds ride into
  the answer and a node left out of the vector is a bound silently kept at whatever `prior`
  said.  A caller warm-starting off its own previous answer gets this for free — a network
  that tightens another names every instant it named.

  **Relaxing more edges than there are instants costs more than one full pass**, so past
  that it takes the pass: `k` updates are `k·n²` against the closure's `n³`.  The branch
  cannot change the answer — that both routes compute the same closure is the invariant
  `stp_incremental_test` asserts over generated networks — so it is a cost decision and
  nothing else.

  Handing it a `prior` that is not an answer for a network `net` tightens gives a wrong
  network rather than an error, which is what `tightening-of?` is for."
  [net prior nodes]
  (if (some unsatisfiable-as-given? net)
    :inconsistent
    (let [node-vec   (nm/by-print-key nodes)
          n          (long (count node-vec))
          idx        (node-index node-vec)
          ^doubles d (relaid-matrix prior node-vec)
          moved      (into []
                           (keep (fn [[[p q] [_ hi]]]
                                   (let [ip (idx p), iq (idx q), w (double hi)]
                                     (when (and ip iq (not= ip iq) (Double/isFinite w)
                                                (< w (aget d (+ (* (long ip) n) (long iq)))))
                                       [ip iq w]))))
                           net)]
      (if (>= (count moved) n)
        (close-state net nodes)
        (let [dirty (boolean-array (* n n))]
          (doseq [[ip iq w] moved] (relax-edge! d dirty n ip iq (double w)))
          (if (seq (negative-cycle-nodes d node-vec))
            :inconsistent
            {:net      (read-back-changed (:net prior) d dirty node-vec)
             :node-vec node-vec
             :d        d}))))))

;; ---- reading a bound back as an ordering ---------------------------------

(defn point-possibilities
  "Which orderings of two instants a metric bound leaves open, as the base relations of
  `vaelii.impl.point`: given `[lo hi]` on `t(q) − t(p)`, p is before q while the gap can be
  positive, coincident while it can be nil, and after while it can be negative.  A bound is
  a closed interval, so at least one always survives.

  A gap sits within the **tolerance** of zero to count as nil, since a magnitude that ought
  to be exactly nil arrives multiplied by a stored conversion factor and can come back a
  last bit off — without the band an interval meeting another would read as overlapping it.
  The same epsilon `unsatisfiable-as-given?` and `negative-cycle-nodes` read, which is what
  keeps one network from being satisfiable and its orderings undecidable at once."
  [[lo hi]]
  (let [eps provers/*quantity-tolerance*]
    (cond-> #{}
      (> hi eps)                            (conj :before)
      (and (<= lo eps) (>= hi (- eps)))     (conj :equal)
      (< lo (- eps))                        (conj :after))))

(def endpoint-signature
  "Each Allen base relation as the four orderings it forces between two intervals' endpoints
  — A's start against B's start, A's start against B's end, A's end against B's start, and
  A's end against B's end.  The keys are `[which-of-A which-of-B]`.

  Writing an interval as `[start end]` with `start < end`, these follow from the endpoint
  inequalities that define the thirteen relations, with the comparisons those inequalities
  leave implicit filled in: `contains` says A starts first and ends last, and *therefore*
  A's start precedes B's end and A's end follows B's start.  All four are pinned for every
  relation, and the thirteen signatures are distinct — which is what makes them a decision
  procedure rather than a filter that could pass two."
  {:before        {[:start :start] :before [:start :end] :before
                   [:end :start]   :before [:end :end]   :before}
   :meets         {[:start :start] :before [:start :end] :before
                   [:end :start]   :equal  [:end :end]   :before}
   :overlaps      {[:start :start] :before [:start :end] :before
                   [:end :start]   :after  [:end :end]   :before}
   :finished-by   {[:start :start] :before [:start :end] :before
                   [:end :start]   :after  [:end :end]   :equal}
   :contains      {[:start :start] :before [:start :end] :before
                   [:end :start]   :after  [:end :end]   :after}
   :starts        {[:start :start] :equal  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :before}
   :equal         {[:start :start] :equal  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :equal}
   :started-by    {[:start :start] :equal  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :after}
   :during        {[:start :start] :after  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :before}
   :finishes      {[:start :start] :after  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :equal}
   :overlapped-by {[:start :start] :after  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :after}
   :met-by        {[:start :start] :after  [:start :end] :equal
                   [:end :start]   :after  [:end :end]   :after}
   :after         {[:start :start] :after  [:start :end] :after
                   [:end :start]   :after  [:end :end]   :after}})

(def allen-relations
  "The thirteen Allen base relations, as `endpoint-signature`'s own keys.

  Read off the table rather than out of `vaelii.impl.interval`, because the dependency
  runs the other way: the interval algebra consumes this namespace's narrowing, so this
  one may not require it.  Nothing is duplicated that could drift unnoticed — a relation
  with no signature is one the narrowing cannot read at all, and `stp_test` holds the two
  sets equal besides."
  (set (keys endpoint-signature)))

(defn endpoint-gaps
  "The four instant pairs an Allen relation between two intervals is decided by, keyed as
  `endpoint-signature` keys them: `{[which-of-A which-of-B] → [p q]}`.

  Named once because two readings depend on being the *same* four.
  `relations-from-endpoints` reads their bounds off the closure, and the narrowing's
  support names the chains those bounds were composed along — a support taken over some
  other set of gaps would name facts the answer did not move with, or miss ones it did."
  [[a-start a-end] [b-start b-end]]
  {[:start :start] [a-start b-start]
   [:start :end]   [a-start b-end]
   [:end :start]   [a-end b-start]
   [:end :end]     [a-end b-end]})

(defn relations-from-endpoints
  "The Allen relations a closed metric network still permits between two intervals, given
  each one's `[start end]` instants.  A relation survives while every one of the four
  orderings its signature demands is still possible.

  Sound but not sharp: the four bounds are read independently, so a set of them that no
  single assignment of times realizes is not noticed here.  That can only leave a relation
  in that the metric network in fact excludes, never take one out that it permits — which is
  the direction a narrowing must err in."
  [closed ea eb]
  (let [poss (update-vals (endpoint-gaps ea eb)
                          (fn [[p q]] (point-possibilities (constraint closed p q))))]
    (into #{}
          (filter (fn [rel]
                    (every? (fn [[slot ordering]] (contains? (poss slot) ordering))
                            (endpoint-signature rel))))
          allen-relations)))

(defn overlap-bounds-from-endpoints
  "How long two intervals overlap, as `[lo hi]`, read off a closed metric network and their
  endpoints alone.

  The shared stretch runs from the later of the two starts to the earlier of the two ends,
  and is nothing at all when that is backwards:

    overlap = max(0, min(a-end, b-end) − max(a-start, b-start))

  and `min(x,y) − max(p,q)` is `min(x−p, x−q, y−p, y−q)`, four gaps the network already
  bounds.  A minimum lies above the least of the lower bounds and below the least of the
  upper ones, so both sides carry through soundly, and clamping at zero is monotone and
  carries through with them."
  [closed [a-start a-end] [b-start b-end]]
  (let [gaps [(constraint closed a-start a-end)
              (constraint closed b-start a-end)
              (constraint closed a-start b-end)
              (constraint closed b-start b-end)]]
    [(max 0 (reduce min (map first gaps)))
     (max 0 (reduce min (map second gaps)))]))

;; =========================================================================
;; THE KB HALF — reading believed facts in, reading answers back out.
;; =========================================================================

(def stp-predicates
  "The metric predicate a constraint is stated with, and the prover claims."
  '#{temporalDistance})

(def endpoint-predicates
  "The two predicates naming an interval's bounding instants — the bridge to the interval
  algebra."
  '#{startOf endOf})

;; ---- measures in and out -------------------------------------------------
;; The rendering policy here is the one `vaelii.impl.duration` applies — the same tolerance
;; grid, and the dimension's base unit read back out of the same `conversionFactor` table
;; the normalization used — so a separation and a duration are written the same way and a
;; caller can compare one against the other.

;; ---- reading the KB into a network ---------------------------------------

(defn- node-term? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- stated-constraints
  "Every believed, visible `(temporalDistance P Q M)` as `[[dimension base-unit] P Q lo hi
  support]`, the magnitudes converted to the dimension's base unit and **snapped to the
  tolerance grid** on the way — `provers/round-magnitude`, the same call
  `duration/interval-length-with-support` makes on a length before comparing it.

  `support` is the constraint's own handle together with the `dimensionOf` /
  `conversionFactor` rows its magnitude was converted through: the conversion is part of
  what the constraint contributes to the network, so a bound composed through it rests on
  the unit table as much as on the fact.

  That is what makes two spellings of one gap arrive as one constraint rather than as two
  that intersect to nothing: `1.1 Hour` normalizes to 3960.0000000000005 and `66 Minute` to
  3960, and unsnapped they cross.  A separation and a duration are written the same way, so
  they are read to the same grid — and the closure's own tolerance (`close`) is then the
  second line rather than the only one, for noise a chain accumulates rather than one a
  conversion introduced."
  [kb context]
  (vec
   (for [m (res/matches-visible kb '(temporalDistance ?p ?q ?m) context)
         :let  [b (second m), p (get b '?p), q (get b '?q), measure (get b '?m)]
         :when (and (node-term? p) (node-term? q) (provers/measure? measure))
         :let  [[[dim lo hi] nsup] (provers/normalize-quantity-with-support kb measure context)
                [base bsup]        (provers/base-unit-with-support kb (last measure) context)]]
     [[dim base] p q
      (provers/round-magnitude lo) (provers/round-magnitude hi)
      (into (conj nsup (first m)) bsup)])))

(defn- file-violation!
  "Append one entry to the KB's accumulating violations ledger, newest 1000 kept — the
  shape `vaelii.impl.violations` keeps, without its chaining-run stamp: nothing here is
  reached from a firing, so there is no run to name."
  [kb entry]
  (when-let [v (reasoning/violations kb)]
    (swap! v (fn [entries]
               (let [e' (conj entries entry) n (count e')]
                 (if (> n 1000) (vec (subvec e' (- n 1000))) e'))))))

(defn- report-mixed-dimensions!
  "Append a refused mixed-dimension constraint set to the violations ledger, and log it at
  :warn.

  A gap in metres is not a duration, and summing the two would give a number that means
  nothing — so a context whose `temporalDistance` facts span more than one dimension gets no
  network at all.  That silences **every** metric goal there, one stated outright included,
  which is a wide consequence for what is usually a single mis-spelt unit.  A refusal that
  wide is content the engine dropped, and it belongs where the engine says what it dropped.

  Not a `wff` check, for the reasons `report-inconsistency!` gives and one of its own:
  which dimension is the intruder depends on how many facts stand in each, so blaming the
  odd one out would make the stored KB depend on what else is present."
  [kb context dims]
  (let [entry {:violation :metric-temporal-mixed-dimensions
               :context   context
               :sentence  nil
               :detail    {:message    (str "the temporalDistance constraints visible from "
                                            context " span more than one dimension, so no"
                                            " metric temporal goal is answered there")
                           ;; a dimension is whatever `dimensionOf` names and may be a NAT;
                           ;; a unit is a symbol by `measure?`'s own check, so it takes the
                           ;; cheaper scalar key
                           :dimensions (nm/by-print-key (map first dims))
                           :units      (into [] (sort-by nm/name-key (map second dims)))}}]
    (trove/log! {:level :warn :id ::metric-temporal-mixed-dimensions :data entry})
    (file-violation! kb entry)))

(defn- support-pair
  "Record `handles` as supporters of both directions of the `[p q]` constraint.  Both,
  because `narrow` writes the converse bound with the bound: one stated gap is an edge each
  way in the distance graph, and a path composed through either rests on the same fact."
  [support handles p q]
  (-> support
      (update [p q] (fnil into #{}) handles)
      (update [q p] (fnil into #{}) handles)))

(defn- build-problem
  "The stated constraints as a problem — or `{:mixed dims}` when they span more than one
  dimension, which is the refusal `problem` reports and answers nil for.  Carried as a value
  rather than decided here so the read stays resident: the reading is a function of the
  believed facts, and whether it has been reported is not.

  `:support` is `{[p q] → #{handle}}`, the sentexes narrowed into each pair, collected on
  the way past for `qcn-kb/build-network`'s reason: the reader is already holding the
  handle it matched, and finding it again later would mean a second read of the same
  content at a different moment."
  [kb context]
  (let [stated (stated-constraints kb context)
        dims   (set (map first stated))]
    (cond
      (empty? stated)    nil
      (= 1 (count dims)) (let [[dim unit] (first dims)
                               {:keys [net support]}
                               (reduce (fn [state [_ p q lo hi sup]]
                                         (-> state
                                             (update :net narrow p q lo hi)
                                             (update :support support-pair sup p q)))
                                       {:net {} :support {}} stated)]
                           {:dimension dim :unit unit :net net :support support})
      :else              {:mixed dims})))

(defn problem
  "Every `temporalDistance` believed and visible from `context`, as `{:dimension :unit :net}`
  — the network together with the dimension and base unit its magnitudes are in.

  nil when nothing is stated, and nil when the stated constraints span **more than one
  dimension**: magnitudes only add up once they are in one unit, so a mixed set is refused
  outright rather than closed into numbers that mean nothing.  That is the same gate
  `duration`'s sum applies, and it fails the same way — no answer, rather than a wrong one.
  The refusal is **reported** (`report-mixed-dimensions!`), once per KB and context, because
  its reach is the whole metric layer there rather than the one goal a sum refuses.

  **Resident** on the KB's `:qcn` atom under a key of this namespace's own, stamped with
  `observe/change-clock` exactly as a qualitative network is (`qcn-kb/read-network`), so a
  rule joining a metric antecedent over many bindings reads the KB once rather than once
  per binding — and so does a settle re-checking one firing after another."
  [kb context]
  (let [prob (observe/cached (reasoning/qcn kb) [::problem context]
                             (fn [_stale] (build-problem kb context)))]
    (if-let [dims (:mixed prob)]
      (do (when (observe/newly-seen? (reasoning/qcn kb) [::reported-mixed context] dims)
            (report-mixed-dimensions! kb context dims))
          nil)
      prob)))

;; ---- the closure, memoized on the network value --------------------------

(def ^:private closure-cache-limit 256)

(defonce ^{:private true
           :doc "The closed network, keyed on the network *value* and the tolerance its verdict was read
  to (`closure`).  Sound across queries because the network is derived from the believed
  facts: any change to them yields a different map and so a different key.  Bounded and
  cleared wholesale when full, like the other caches here."}
  closure-cache
  (atom {}))

(defn- report-inconsistency!
  "Append an unsatisfiable metric network to the KB's violations ledger, and log it at :warn.

  A cycle of gaps that cannot all be closed is a clash among *several* stored facts with
  nothing to prefer between them, so it belongs where the engine reports content it had to
  drop rather than being thrown.  Three reasons it is not a `wff` check, and they are the
  metric reading of the three the qualitative calculi give:

  * `wff` **throws**, and the fact it would throw on is whichever arrived last.  No single
    constraint of a negative cycle is the wrong one — the cycle is a property of the set —
    so blaming a member of it would make the stored KB depend on assertion order.
  * the check costs an all-pairs closure, and `wff` runs per assert.  Every temporal fact
    would pay an O(n³) pass to store.
  * the prover is **opt-in**.  A KB that never registered it would be held to an arithmetic
    it never asked to reason with.

  Recorded on the way past, once per network **per KB and context**: the closure itself is
  shared on the network value across both, so a report keyed on it would fire for whichever
  caller ran the pass and leave the others answering nothing with nothing to read.  A change
  of belief yields a different network and reports again."
  [kb context {:keys [net unit]} cycle-nodes]
  (let [bad   (unsatisfiable-pairs net)
        entry {:violation :metric-temporal-inconsistency
               :context   context
               :sentence  nil
               :detail    (cond-> {:message (str "the temporalDistance constraints visible"
                                                 " from " context " cannot all be"
                                                 " satisfied, so no metric temporal goal"
                                                 " is answered there")
                                   :unit  unit
                                   :nodes (nm/by-print-key (nodes net))}
                            (seq bad)         (assoc :pairs (nm/by-print-key bad))
                            (seq cycle-nodes) (assoc :cycle (nm/by-print-key cycle-nodes)))}]
    (trove/log! {:level :warn :id ::metric-temporal-inconsistency :data entry})
    (file-violation! kb entry)))

(defn- resident-closure
  "Hold the closure on the KB beside the network it is a function of, under `k` and the
  change clock, and answer from there while both still hold.

  This sits *in front of* the content-keyed memo rather than replacing it, and it earns its
  place twice.  A network is a map of a bound per stated pair, so looking one up as a cache
  key costs a full map comparison at every hit; a resident network is the same object read
  after read, and `identical?` decides that in a reference compare.  And `build` is handed
  the entry it replaces — `{:for … :result …}`, the network that was resident before and the
  closed state for it, or nil — which is what lets the pass warm-start off its own previous
  answer.

  A fast path, never an authority: a caller asking about some network other than the one
  resident for this context falls straight through to the content-keyed memo, and so is
  answered about the network it actually asked about."
  [kb k net build]
  (let [entry (observe/cached (reasoning/qcn kb) k (fn [stale] {:for net :result (build stale)}))]
    (if (identical? net (:for entry)) (:result entry) (build nil))))

(defn- cycle-nodes-of
  "The instants on a negative cycle of `net`, for the report.  Recomputed rather than carried
  out of `close`, which answers a verdict and not a diagnosis; it runs once per *newly*
  inconsistent network, never on the answering path."
  [net]
  (let [node-vec (nm/by-print-key (nodes net))]
    (negative-cycle-nodes (shortest-paths! (distance-matrix net node-vec) (count node-vec))
                          node-vec)))

(defn closure
  "The closed network of `prob`, memoized on the network value.  `:inconsistent` when the
  constraints contradict each other, reported through `report-inconsistency!` on the way
  past — the closure has just proved it, and the alternative is a query that silently answers
  nothing.

  The key is the **network alone**, not the nodes a caller adds because its goal names them.
  Such a node is isolated: it has a finite edge in neither direction, so it can tighten no
  pair and lie on no cycle, and `constraint` answers unbounded for a pair the read-back never
  recorded.  So one caller's answer is another's, and the pass runs once per network rather
  than once per shape of question.

  The **tolerance rides in the key** beside the network, because both of `close`'s
  verdicts are read to `provers/*quantity-tolerance*` and it is a dynamic var a caller may
  rebind for a coarser or finer policy.  The magnitudes are already on the grid by then
  (`stated-constraints` snaps them at a fixed scale), so the network alone does not record
  which band the cycle check was made in — and a run under a rebound tolerance would
  otherwise be answered with the verdict reached under the ambient one.  It is one number
  in the key and constant for a whole query loop, so it adds no work that the sharing
  below is for.

  The **report** is deliberately not on that path.  Two KBs, or two contexts of one KB,
  reaching the same network share the pass — and a ledger entry is a claim about a KB and a
  context, so it hangs off `observe/newly-seen?` instead: this KB, this context, this
  network.  A cache hit still reports if the KB has not said it yet.

  The pass is **warm-started** whenever the network last resident for this context is one
  this network tightens, which is what an arriving constraint does and is the ordinary case
  during a load: only the bounds that moved are relaxed in (`close-state-from`), and the
  answer is the one the whole cubic pass would have reached.  A widening — a retraction, a defeat,
  a loosened bound — has no such route and pays the pass."
  [kb context {:keys [net] :as prob} extra-nodes]
  (let [state (resident-closure
               kb [::pass context] net
               (fn [stale]
                 (caches/read-through
                  closure-cache (caches/limit-of :metric-closures closure-cache-limit)
                  [net provers/*quantity-tolerance*]
                  (fn []
                    (let [all  (into (nodes net) extra-nodes)
                          warm (when (and (map? (:result stale))
                                          (tightening-of? net (:for stale)))
                                 (:result stale))]
                      (if warm
                        (close-state-from net warm all)
                        (close-state net all)))))))
        result (if (map? state) (:net state) state)]
    (when (and (= :inconsistent result)
               (observe/newly-seen? (reasoning/qcn kb) [::reported context] net))
      (report-inconsistency! kb context prob (cycle-nodes-of net)))
    result))

(defn closed-network
  "The closed metric network visible from `context`, or nil when nothing is stated (or the
  constraints span more than one dimension), or `:inconsistent` when they contradict."
  [kb context]
  (when-let [prob (problem kb context)]
    (closure kb context prob nil)))

;; ---- what a derived bound rests on ---------------------------------------
;; The closure answers a gap between two instants the constraints entail; this answers
;; *which* constraints entailed it.  A forward rule joining on a derived bound needs the
;; second as much as the first — a conclusion resting on an entailment nothing can
;; withdraw is worse than a conclusion never drawn (docs/nmtms.md) — and the shape is the
;; qualitative one (`qcn-kb/solve-with-support`).
;;
;; **The path, not the network.**  A bound between P and Q is the least-weight chain
;; between them, so the constraints on that chain are what produced it and the rest of the
;; network is not read at all.  Naming the whole network would be sound — every derived
;; bound follows from all of it — but it would withdraw the conclusion when any unrelated
;; constraint anywhere was retracted, which is the locality the engine keeps everywhere
;; else.  So it is the path, reconstructed from the same pass that computed the distance.
;;
;; **Both directions.**  A bound is `[lo hi]`, and `lo` is `−d[q][p]` where `hi` is
;; `d[p][q]` — two different chains in general — so the support of the bound is the union
;; of the two paths' constraints.  A caller reading only one side is not a case worth a
;; second entry point: `solve-distance` binds or checks the pair, never a half of it.
;;
;; It is an **over-approximation of one derivation**, on the same two counts
;; `qcn/path-consistent-with-support` states: a pair narrowed by two facts keeps both, and
;; a second chain that reaches the same figure contributes nothing.  What is guaranteed is
;; the piece a justification needs — every handle named was really read into this network,
;; and the reported set is enough to have produced the bound on its own.

(defonce ^{:private true
           :doc "The closed distance matrix's **reconstruction table**, keyed on the network value alone.

  Its own cache, separate from `closure-cache`, because support is asked for rarely: every
  metric goal would otherwise pay to allocate and fill an `int[n²]` that nothing reads.
  The key omits the tolerance `closure`'s carries, and correctly — `shortest-paths!` reads
  no tolerance, so the table is a function of the network and nothing else; the two
  verdicts that *do* read one are `close`'s, on the other cache."}
  via-cache
  (atom {}))

(defn- reconstruction
  "`{:node-vec :idx :nxt :n}` for `net` — the closed distance matrix's successor table with
  what a pair needs to reach it.  The distances themselves are dropped: `closure` already
  holds those, and this pass exists only to say which edges produced them."
  [net]
  (caches/read-through via-cache (caches/limit-of :metric-reconstructions closure-cache-limit) net
                       (fn []
                         (let [node-vec (nm/by-print-key (nodes net))
                               n        (count node-vec)
                               d        (distance-matrix net node-vec)
                               nxt      (edge-successors d n)]
                           (shortest-paths! d nxt n)
                           {:node-vec node-vec :idx (node-index node-vec) :nxt nxt :n n}))))

(defn- path-support
  "The handles behind the bound `net` entails on `t(q) − t(p)`: the supporters of every
  constraint on the shortest chain each way.

  `#{}` on the diagonal (an instant is no distance from itself, and no constraint says so),
  and `#{}` for an instant the network does not mention — an isolated node has a finite
  edge in neither direction, so it bounds nothing and there is nothing to support.

  **The whole network** when a chain cannot be walked (`path-edges` nil): the bound is
  entailed, so something produced it, and answering `#{}` would be the one wrong answer —
  it would drop the firing, or worse leave it resting on nothing.  The network's own
  supporters are a sound superset of any chain within it, so the conclusion is drawn and is
  withdrawn by any change to the metric facts.  What it costs is locality, in exactly the
  case a local answer is not available."
  [net support p q]
  (let [{:keys [node-vec idx ^ints nxt ^long n]} (reconstruction net)
        ip (idx p)
        iq (idx q)]
    (if (or (nil? ip) (nil? iq) (= ip iq))
      #{}
      (let [there (path-edges nxt n ip iq)
            back  (path-edges nxt n iq ip)]
        (if (and there back)
          (into #{}
                (mapcat (fn [[i j]] (get support [(nth node-vec i) (nth node-vec j)] #{})))
                (into there back))
          (into #{} (mapcat val) support))))))

(defn separation
  "The tightest `[lo hi]` bound on `t(q) − t(p)` the constraints visible from `context`
  entail, in the dimension's base unit, as `[[dimension unit] lo hi]`.

  nil when nothing is stated at all, and nil when the network is inconsistent — an
  unsatisfiable theory is not mined for a number, the same rule the qualitative calculi
  follow.  A pair the constraints reach on neither side comes back `[-∞ ∞]`, which is a real
  answer (\"nothing is known\") and not an absent one."
  [kb context p q]
  (when-let [{:keys [dimension unit] :as prob} (problem kb context)]
    (let [closed (closure kb context prob [p q])]
      (when-not (= :inconsistent closed)
        (into [[dimension unit]] (constraint closed p q))))))

(defn inconsistent?
  "Do the `temporalDistance` constraints visible from `context` contradict each other?"
  [kb context]
  (= :inconsistent (closed-network kb context)))

;; ---- the bridge to intervals ---------------------------------------------

(defn endpoints-with-support
  "An interval's `[[start end] handles]` — the instants `(startOf I P)` and `(endOf I P)`
  state, visible from `context` and believed, together with the two facts that state them.
  Nil when either is missing, or when either is stated of two *different* instants, which
  is a disagreement no reasoning should paper over.

  Restating one endpoint in several contexts of the ancestor set is not a disagreement — the
  matches carry the same instant and collapse to one — and all of them are named, for
  `provers/table-read`'s reason: the reading is a property of the set."
  [kb i context]
  (let [one (fn [pred]
              (let [ms (res/matches-visible kb (list pred i '?p) context)
                    ps (into #{} (comp (map (comp #(get % '?p) second))
                                       (filter node-term?))
                             ms)]
                (when (= 1 (count ps))
                  [(first ps) (into #{} (map first) ms)])))
        [s sh] (one 'startOf)
        [e eh] (one 'endOf)]
    (when (and s e) [[s e] (into sh eh)])))

(defn endpoints-of
  "`endpoints-with-support`'s `[start end]` alone, for a caller with no use for the facts
  that named them."
  [kb i context]
  (first (endpoints-with-support kb i context)))

(defn intervals-with-endpoints
  "Every interval both of whose bounding instants are named and agreed on, as
  `{interval [[start end] #{handle}]}` — `endpoints-with-support`'s answer per interval,
  so the facts that named the instants ride along with them."
  [kb context]
  (into {}
        (keep (fn [i] (when-let [e (endpoints-with-support kb i context)] [i e])))
        (into #{}
              (comp (mapcat #(res/matches-visible kb (list % '?i '?p) context))
                    (map (comp #(get % '?i) second))
                    (filter node-term?))
              endpoint-predicates)))

(def allen-narrowing-sources
  "Every predicate the metric narrowing of the interval algebra reads: the constraints
  themselves, the two endpoint predicates that say which instants an interval is bounded
  by, and the unit table the magnitudes convert through.

  What `vaelii.impl.interval` declares to `qcn-kb/calculus` as the narrowing's sources, so
  one of these arriving re-checks and re-joins the rules that join on an Allen antecedent —
  the network moved, and none of these is a predicate a rule's other antecedents match."
  (into (into stp-predicates endpoint-predicates) provers/unit-table-predicates))

(defn allen-narrowing-with-support
  "What the metric constraints pin down about the *interval* relations, as
  `{:net {[i j] → #{base relations}} :support {[i j] → #{handle}}}` — the same shape
  `qcn-kb/build-network` accumulates, so the interval algebra folds it in beside the
  network it reads from stored Allen facts.

  This is the payoff of the bridge, and it runs one way only: **metric narrows qualitative**.
  A closed gap of `end(A) < start(B)` leaves `before` the only Allen relation A and B can
  stand in, and the thirteen signatures in `endpoint-signature` do the same for every other
  shape of constraint.  Nothing is asserted and nothing is mutated — the result is a value.

  A pair's **support** is what the four gaps were read through: the `startOf` / `endOf`
  facts naming both intervals' instants, and the constraints along the shortest chain each
  gap's bound was composed out of (`path-support`, `endpoint-gaps`).  Not the whole metric
  network, for the reason a derived bound's support is not: a conclusion resting on this
  pair must go when a constraint behind it goes and must *not* go when an unrelated one
  does.

  Only pairs the constraints actually narrow are recorded; a pair still open to all thirteen
  is the absence of a claim, and it would intersect to the same network anyway while naming
  facts nothing rested on.  nil when there is nothing to read: no metric constraints, no
  two intervals with both endpoints named, or an inconsistent network — which narrows
  nothing, since an unsatisfiable theory is not mined for conclusions."
  [kb context]
  (when-let [{:keys [net support] :as prob} (problem kb context)]
    (let [ends (intervals-with-endpoints kb context)]
      (when (>= (count ends) 2)
        (let [closed (closure kb context prob (mapcat (comp first val) ends))]
          (when-not (= :inconsistent closed)
            (reduce
             (fn [acc [[i [ei hi]] [j [ej hj]]]]
               (let [rels (relations-from-endpoints closed ei ej)]
                 (if (= rels allen-relations)
                   acc
                   (-> acc
                       (assoc-in [:net [i j]] rels)
                       (assoc-in [:support [i j]]
                                 (into (into hi hj)
                                       (mapcat (fn [[p q]] (path-support net support p q)))
                                       (vals (endpoint-gaps ei ej))))))))
             {:net {} :support {}}
             (for [a ends b ends :when (not= (key a) (key b))] [a b]))))))))

(defn allen-narrowing
  "`allen-narrowing-with-support`'s relation sets alone — `{[i j] → #{base relations}}`,
  for a caller reading what the metric layer pins down without needing the facts behind
  it."
  [kb context]
  (:net (allen-narrowing-with-support kb context)))

(defn overlap-window-with-support
  "The bounds the metric constraints put on how long intervals `i1` and `i2` overlap, as
  `[[[dimension unit] lo hi] handles]` in the dimension's base unit — `hi` possibly
  infinite, since a network may pin a floor without a ceiling — together with what the
  bound rests on: the two `startOf`/`endOf` facts per interval, and the constraints on the
  chains between the four endpoint pairs `overlap-bounds-from-endpoints` reads.

  nil when there is nothing to read (no constraints, an endpoint missing, an inconsistent
  network) and nil when the answer is the vacuous `[0 ∞]`, which is not a bound at all.
  `vaelii.impl.duration` intersects what comes back with the bound it computes from the
  stored lengths and the qualitative relation set: both are sound, so their intersection is."
  [kb context i1 i2]
  (when-let [{:keys [dimension unit net support] :as prob} (problem kb context)]
    (let [[e1 h1] (endpoints-with-support kb i1 context)
          [e2 h2] (endpoints-with-support kb i2 context)]
      (when (and e1 e2)
        (let [closed (closure kb context prob (concat e1 e2))]
          (when-not (= :inconsistent closed)
            (let [[lo hi] (overlap-bounds-from-endpoints closed e1 e2)]
              (when-not (and (zero? lo) (not (Double/isFinite (double hi))))
                (let [[a-start a-end] e1
                      [b-start b-end] e2
                      ;; the same four gaps the bound was read off, so the support is the
                      ;; union of the four chains and nothing wider
                      gaps [[a-start a-end] [b-start a-end] [a-start b-end] [b-start b-end]]]
                  [[[dimension unit] lo hi]
                   (into (into h1 h2)
                         (mapcat (fn [[p q]] (path-support net support p q)))
                         gaps)])))))))))

;; ---- the prover ----------------------------------------------------------

(defn- contains-bound?
  "Is the derived `[lo hi]` contained in the stated one — is the stated bound *entailed*?
  A bound is a claim that the gap lies within it, so a wider claim follows from a narrower
  one, and the tolerance is the same epsilon the measure comparisons use."
  [[lo hi] [slo shi]]
  (let [eps provers/*quantity-tolerance*]
    (and (>= lo (- slo eps)) (<= hi (+ shi eps)))))

(defn- solve-distance-with-support
  "`(temporalDistance P Q M)` — close the constraints, read the tightest gap between P and Q,
  then bind or check, each answer paired with the constraints it rests on (`path-support`).

  A **bind** needs both bounds finite: a half-bounded separation is a real piece of knowledge
  but not a measure, and there is no honest structural NAT for it, so the goal simply has no answer
  rather than a fabricated one.  A **check** has no such trouble — a stated bound with an
  infinite side is not written, and a finite one is either contained or not.

  The check arm's support carries the **stated** measure's own conversion besides the path:
  whether the derived bound is contained in it is decided after normalizing it through the
  unit table, so a `conversionFactor` retracted there un-decides the comparison exactly as
  one on the path does."
  [kb goal context]
  (let [[_ p q m] goal]
    (when-let [{:keys [dimension unit net support] :as prob} (problem kb context)]
      (let [closed (closure kb context prob [p q])]
        (when-not (= :inconsistent closed)
          (let [[lo hi] (constraint closed p q)
                sup     (delay (path-support net support p q))]
            (cond
              (sx/variable? m)
              (when (and (Double/isFinite (double lo)) (Double/isFinite (double hi)))
                [[{m (provers/render-quantity lo hi unit)} @sup]])

              (provers/measure? m)
              (let [[[dim* slo shi] msup] (provers/normalize-quantity-with-support kb m context)
                    [base bsup]           (provers/base-unit-with-support kb (last m) context)]
                ;; the base unit, not just the dimension: `lo`/`hi` are in the problem's
                ;; `unit` and `slo`/`shi` in the stated measure's base unit, so a unit
                ;; that declares no `conversionFactor` would otherwise read a five-second
                ;; gap as a five-fortnight one
                (if (and (= dimension dim*)
                         (= unit base)
                         (contains-bound? [lo hi] [slo shi]))
                  [[{} (into (into @sup msup) bsup)]]
                  []))

              :else [])))))))

(defn- solve-distance
  "`solve-distance-with-support`'s bindings alone — what `Prover/solve` answers, where the
  forward join asks for the support beside them."
  [kb goal context]
  (map first (solve-distance-with-support kb goal context)))

(defn- answer-slot?
  "Can `m` be the answer argument — a variable to bind, or a ground measure to check?"
  [m]
  (or (sx/variable? m) (provers/measure? m)))

(defrecord TemporalDistanceProver []
  prover-types/Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 4 (count goal))
         (contains? stp-predicates (first goal))
         (node-term? (nth goal 1)) (node-term? (nth goal 2))
         (answer-slot? (nth goal 3))))
  ;; A computation, so at most one answer — and the estimate must not cost what it
  ;; estimates, which here would be the reads plus an all-pairs closure.
  (est-bindings [_ _ _ _] 1)
  ;; A closure over the stored constraints before the first answer, not a search.
  (cost         [_ _ _ _] :compute)
  ;; Authoritative over the constraints it reads: the answer is a property of the
  ;; *whole* set rather than of any one stored fact, and it entails every stated bound
  ;; it is contained in, so unioning a raw fact match in would add nothing this does
  ;; not already answer.  A source it does not read is `provers/sole-prover`'s
  ;; question.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (solve-distance kb goal context))

  prover-types/SupportingProver
  (support-functors [_] stp-predicates)
  ;; The constraints themselves, and the unit table their magnitudes convert through — the
  ;; two reads `stated-constraints` makes.  `startOf` / `endOf` are deliberately absent:
  ;; they bridge to the interval algebra (`allen-narrowing`, `overlap-window-with-support`)
  ;; and decide
  ;; nothing about a `temporalDistance` goal, which names its instants directly.
  (support-sources [_] (into stp-predicates provers/unit-table-predicates))
  (solve-with-support [_ kb goal context] (solve-distance-with-support kb goal context)))

(defn stp-prover
  "The metric temporal prover, to register with `vaelii.core/add-prover`."
  []
  (->TemporalDistanceProver))

;; ---- what the metric side holds, declared -------------------------------
;;
;; Registered here rather than in a central list, so a process that never loaded the
;; metric-time reasoner reports no row for it — which is the honest answer, and better
;; than a row of zeroes for a cache that does not exist.

(caches/register-cache
 {:cache    :metric-closures
  :label    "Metric closures"
  :scope    :process
  :unit     "networks"
  :limit    (caches/limit-thunk :metric-closures closure-cache-limit)
  :counters nil
  :note     (str "The all-pairs shortest-path closure of a metric network, keyed on the "
                 "network value and the measure tolerance the verdict was read to — so "
                 "two contexts stating the same durations share one closure, and any "
                 "change to the believed facts is a different key. Each entry carries the "
                 "distance matrix the bounds were read off beside them, which is what the "
                 "next arriving constraint is relaxed into rather than closing again.")
  :read     (fn [_] {:entries (count @closure-cache)})
  :clear    (fn [_] (let [n (count @closure-cache)] (reset! closure-cache {}) n))
  :trim     (fn [_ target] (caches/trim-map! closure-cache target))})

(caches/register-cache
 {:cache    :metric-reconstructions
  :label    "Metric path reconstructions"
  :scope    :process
  :unit     "networks"
  :limit    (caches/limit-thunk :metric-reconstructions closure-cache-limit)
  :counters nil
  :note     (str "The same shortest-path pass carrying the table that says which edges "
                 "produced each bound, so a forward firing can rest on the constraints "
                 "its bound was composed out of. A separate cache because support is "
                 "asked for rarely and every metric goal would otherwise pay to fill an "
                 "int[n²] nothing reads.")
  :read     (fn [_] {:entries (count @via-cache)})
  :clear    (fn [_] (let [n (count @via-cache)] (reset! via-cache {}) n))
  :trim     (fn [_ target] (caches/trim-map! via-cache target))})
