;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.stp
  "Metric time as a **simple temporal problem**: bounds `lo ≤ t(Q) − t(P) ≤ hi` on the gaps
  between instants, closed by all-pairs shortest paths, unsatisfiable on a negative cycle.
  The algorithm half is pure data; the KB half reads `temporalDistance` measures, answers
  them through `TemporalDistanceProver` (opt-in, `:metric-time`), and bridges the bounds
  onto Allen's intervals through `startOf` / `endOf` for `vaelii.impl.interval` and
  `vaelii.impl.duration`.  See docs/stp.md."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.timepoint :as tp]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations])
  (:import [java.time ZoneOffset]))

;; =========================================================================
;; THE ALGORITHM — pure data in, pure data out.  No KB, no context, no belief.
;; =========================================================================

;; A **network** is `{[p q] → [lo hi]}`, meaning `lo ≤ t(q) − t(p) ≤ hi`, both directions
;; stored; an unrecorded pair is unbounded.

(def unbounded
  "The constraint on a pair nothing is known about: the whole real line."
  [##-Inf ##Inf])

(defn constraint
  "The bound on `t(q) − t(p)` in `net`: `[0 0]` on the diagonal whatever is recorded there,
  else the recorded interval, else unbounded."
  [net p q]
  (if (= p q) [0 0] (get net [p q] unbounded)))

(defn nodes
  "Every instant named by a constraint in `net`."
  [net]
  (into #{} (mapcat identity) (keys net)))

(defn narrow
  "Intersect the constraint on `[p q]` with `[lo hi]`, writing the converse `[q p]` with it.
  Commutative and associative, so a network is a function of its constraints' set."
  [net p q lo hi]
  (let [[lo0 hi0] (get net [p q] unbounded)
        lo* (max lo0 lo)
        hi* (min hi0 hi)]
    (assoc net [p q] [lo* hi*] [q p] [(- hi*) (- lo*)])))

(defn- unsatisfiable-as-given?
  "Is one recorded constraint unsatisfiable before any closure — crossed bounds, or a
  diagonal constraint excluding zero?  Both read to `provers/*quantity-tolerance*`.  The
  diagonal case needs this check because `constraint` answers zero there and no path visits
  it."
  [[[p q] [lo hi]]]
  (let [eps provers/*quantity-tolerance*]
    (or (> lo (+ hi eps))
        (and (= p q) (not (and (<= lo eps) (>= hi (- eps))))))))

(defn unsatisfiable-pairs
  "The pairs of `net` that are unsatisfiable as written; empty when the network is
  unsatisfiable only through a cycle."
  [net]
  (into #{} (keep (fn [[pair :as entry]]
                    (when (unsatisfiable-as-given? entry) pair)))
        net))

;; ---- the closure, over a matrix ------------------------------------------
;; The distance graph is a `double[]` of n², row-major over `node-vec`'s positions:
;; `d[p·n + q]` is the upper bound on `t(q) − t(p)`, `##Inf` is no edge, and the diagonal
;; starts at zero so a negative self-distance is a cycle.  A map keyed `[p q]` would
;; allocate a vector per probe, n³ of them per pass.

(defn- node-index
  "`{node → position}` over `node-vec`."
  [node-vec]
  (into {} (map-indexed (fn [i x] [x i])) node-vec))

(defn- edges
  "`[ip iq w]` for every finite upper bound of `net` between two distinct instants `idx`
  places.  A pair naming an instant outside `idx` is dropped."
  [net idx]
  (keep (fn [[[p q] [_ hi]]]
          (let [ip (idx p), iq (idx q), w (double hi)]
            (when (and ip iq (not= ip iq) (Double/isFinite w)) [ip iq w])))
        net))

(defn- distance-matrix
  "The network as the `n×n` matrix above, over `node-vec`."
  ^doubles [net node-vec]
  (let [n   (long (count node-vec))
        ^doubles d (double-array (* n n) ##Inf)]
    (dotimes [i n] (aset d (+ (* i n) i) 0.0))
    (doseq [[ip iq w] (edges net (node-index node-vec))]
      (let [k (+ (* (long ip) n) (long iq)), w (double w)]
        (when (< w (aget d k)) (aset d k w))))
    d))

(defn- shortest-paths!
  "Floyd–Warshall in place over `d`, answering `d`.  `##Inf` entries take no part.

  `nxt`, when given, is the successor table: `nxt[p·n + q]` is the next node after p on the
  best p → q path.  Successors and not midpoints, because an entry improved at a late `k`
  can name a midpoint whose own entry later points back through the pair, and a midpoint
  reassembly then recurses forever."
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
  "The successor table for the direct edges of an initialized distance matrix: `j` for every
  finite off-diagonal `d[i·n + j]`, `-1` for the rest."
  ^ints [^doubles d ^long n]
  (let [nxt (int-array (* n n) -1)]
    (dotimes [i n]
      (let [in (* i n)]
        (dotimes [j n]
          (when (and (not= i j) (Double/isFinite (aget d (+ in j))))
            (aset nxt (+ in j) (int j))))))
    nxt))

(defn- path-edges
  "The `[from to]` index pairs of the shortest `p → q` path `nxt` records; nil when there is
  no path or the walk passes `n` steps, which a zero-weight cycle allows."
  [^ints nxt ^long n ^long p ^long q]
  (loop [cur p, acc [], steps 0]
    (cond
      (= cur q)     acc
      (>= steps n)  nil
      :else         (let [nx (aget nxt (+ (* cur n) q))]
                      (when-not (neg? nx)
                        (recur (long nx) (conj acc [cur nx]) (inc steps)))))))

(def ^:private ^:const exact-long-double
  "2⁵³, the largest magnitude below which a `double` holds every integer."
  9007199254740992.0)

(defn- magnitude
  "A closed bound read out of the matrix: a long where it is whole and exactly representable,
  the double otherwise — `provers/round-magnitude`'s convention."
  [^double x]
  (if (and (== x (Math/rint x)) (< (- exact-long-double) x exact-long-double))
    (long x)
    x))

(defn- read-back
  "The closed matrix as a network: `[p q]` is `[−d[q][p] d[p][q]]`, and a pair bounded on
  neither side is left unrecorded."
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
  "The instants whose self-distance in the closed matrix `d` is below zero by more than
  `provers/*quantity-tolerance*`."
  [^doubles d node-vec]
  (let [eps (double provers/*quantity-tolerance*)
        n   (long (count node-vec))]
    (into #{}
          (comp (map-indexed vector)
                (keep (fn [[i x]]
                        (when (< (aget d (+ (* (long i) n) (long i))) (- eps)) x))))
          node-vec)))

(defn close-state
  "All-pairs shortest paths over `net` across `nodes`, as a closed state
  `{:net {[p q] → [lo hi]} :node-vec [instant …] :d ^doubles}`, or `:inconsistent` on a
  constraint unsatisfiable as given or a negative cycle.  `:d` is written once; every
  function taking a state copies it before an update."
  [net nodes]
  (if (some unsatisfiable-as-given? net)
    :inconsistent
    (let [node-vec (nm/by-print-key nodes)
          closed   (shortest-paths! (distance-matrix net node-vec) (count node-vec))]
      (if (seq (negative-cycle-nodes closed node-vec))
        :inconsistent
        {:net (read-back closed node-vec) :node-vec node-vec :d closed}))))

(defn close
  "`close-state`'s `:net`, or `:inconsistent`.  The caller passes every node `net`
  mentions; extra nodes are isolated and change nothing."
  [net nodes]
  (let [s (close-state net nodes)]
    (if (map? s) (:net s) s)))

;; ---- warm-starting: one arriving constraint, not a fresh pass ------------
;; docs/stp.md, "Warm-starting", derives the relaxation identity, shows one round is enough,
;; and says why a widening has no warm start.

(defn tightening-of?
  "Is every bound `prior` records at least as wide as the one `net` records for the same
  pair?  The precondition for `close-state-from`."
  [net prior]
  (every? (fn [[pair [lo hi]]]
            (let [[lo* hi*] (get net pair unbounded)]
              (and (>= (double lo*) (double lo)) (<= (double hi*) (double hi)))))
          prior))

(defn- relax-edge!
  "Add the edge `ip → iq` of weight `w` to the closed matrix `d` in place, marking every
  moved cell in `dirty`.  Column p and row q are snapshotted first: in the inconsistent case
  the sweep can move them mid-update.  The positions are cast in the body because a fn
  taking primitives is capped at four arguments."
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
  "`prior` with every pair `dirty` marks rewritten off `d`.  The scan runs over unordered
  pairs because one pair's two entries are read off two cells that move independently."
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
  "A copy of the prior state's matrix laid out over `node-vec`; an instant the prior never
  held starts isolated.  Quadratic in the prior's size."
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
  "`close-state`, warm-started off `prior`, a closed state for a network `net` tightens
  (`tightening-of?`): each moved constraint is relaxed in, and only moved bounds are read
  back.  At `n` or more moved edges it runs the full pass instead.

  `nodes` must name every instant of `prior` as well as of `net`.  A `prior` that `net` does
  not tighten gives a wrong network, not an error."
  [net prior nodes]
  (if (some unsatisfiable-as-given? net)
    :inconsistent
    (let [node-vec   (nm/by-print-key nodes)
          n          (long (count node-vec))
          ^doubles d (relaid-matrix prior node-vec)
          moved      (filterv (fn [[ip iq w]]
                                (< (double w) (aget d (+ (* (long ip) n) (long iq)))))
                              (edges net (node-index node-vec)))]
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
  "The `vaelii.impl.point` base relations a bound `[lo hi]` on `t(q) − t(p)` leaves open:
  `:before` while the gap can be positive, `:equal` while it can be zero, `:after` while it
  can be negative, each read to `provers/*quantity-tolerance*`.  Never empty."
  [[lo hi]]
  (let [eps provers/*quantity-tolerance*]
    (cond-> #{}
      (> hi eps)                            (conj :before)
      (and (<= lo eps) (>= hi (- eps)))     (conj :equal)
      (< lo (- eps))                        (conj :after))))

(def endpoint-signature
  "Each Allen base relation as the ordering it forces on each of the four endpoint
  comparisons, keyed `[which-of-A which-of-B]`.  The thirteen signatures are distinct."
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
  "The thirteen Allen base relations, read off `endpoint-signature` because
  `vaelii.impl.interval` requires this namespace and not the reverse."
  (set (keys endpoint-signature)))

(def interval-denotation
  "Every interval predicate, the thirteen base ones and the seven derived ones, mapped to
  the set of Allen base relations it denotes.  A goal `(P i j)` is entailed exactly when
  the relations still possible between i and j are a subset of P's denotation.  Here for
  `allen-relations`' reason, since the point calculus reads a stated Allen fact too."
  '{before        #{:before}        after         #{:after}
    meets         #{:meets}         metBy         #{:met-by}
    overlaps      #{:overlaps}      overlappedBy  #{:overlapped-by}
    starts        #{:starts}        startedBy     #{:started-by}
    during        #{:during}        contains      #{:contains}
    finishes      #{:finishes}      finishedBy    #{:finished-by}
    intervalEqual #{:equal}
    precedes            #{:before :meets}
    precededBy          #{:after :met-by}
    subintervalOf       #{:during :starts :finishes :equal}
    properSubintervalOf #{:during :starts :finishes}
    hasSubinterval      #{:contains :started-by :finished-by :equal}
    sharesTimeWith      #{:overlaps :overlapped-by :starts :started-by :during :contains
                          :finishes :finished-by :equal}
    temporallyDisjoint  #{:before :after :meets :met-by}})

(defn endpoint-gaps
  "The four instant pairs an Allen relation between intervals `[a-start a-end]` and
  `[b-start b-end]` is decided by, keyed as `endpoint-signature` keys them.  The narrowing
  and its support both read these."
  [[a-start a-end] [b-start b-end]]
  {[:start :start] [a-start b-start]
   [:start :end]   [a-start b-end]
   [:end :start]   [a-end b-start]
   [:end :end]     [a-end b-end]})

(defn relations-from-endpoints
  "The Allen relations the closed network `closed` still permits between intervals with
  `[start end]` instants `ea` and `eb`: those whose every signature ordering is still
  possible.  The reading is sound but not sharp (docs/stp.md)."
  [closed ea eb]
  (let [poss (update-vals (endpoint-gaps ea eb)
                          (fn [[p q]] (point-possibilities (constraint closed p q))))]
    (into #{}
          (filter (fn [rel]
                    (every? (fn [[slot ordering]] (contains? (poss slot) ordering))
                            (endpoint-signature rel))))
          allen-relations)))

(defn- overlap-gaps
  "The four gaps an overlap is bounded by: each end against each start."
  [[a-start a-end] [b-start b-end]]
  [[a-start a-end] [b-start a-end] [a-start b-end] [b-start b-end]])

(defn overlap-bounds-from-endpoints
  "How long two intervals overlap, as `[lo hi]`, read off a closed network and their
  `[start end]` instants (docs/stp.md, \"Sharpening an overlap\")."
  [closed ea eb]
  (let [gaps (map (fn [[p q]] (constraint closed p q)) (overlap-gaps ea eb))]
    [(max 0 (reduce min (map first gaps)))
     (max 0 (reduce min (map second gaps)))]))

;; =========================================================================
;; THE KB HALF — reading believed facts in, reading answers back out.
;; =========================================================================

(def stp-predicates
  "The metric predicate a constraint is stated with, and the prover claims."
  '#{temporalDistance})

(def endpoint-predicates
  "The two predicates naming an interval's bounding instants."
  '#{startOf endOf})

(def network-predicates
  "Every predicate `problem` reads a constraint from: `temporalDistance`, and
  `includesInstant` into a calendar term (`instant-constraints`)."
  '#{temporalDistance includesInstant})

;; ---- reading the KB into a network ---------------------------------------

(defn- node-term? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- metric-term?
  "A term the metric network places: a node term, or a calendar moment (`tp/moment`)."
  [x]
  (or (node-term? x) (some? (tp/moment x))))

(def ^:private epochs
  "The node of each `tp/moment` frame the frame's calendar moments are placed from: the
  term naming 1970-01-01T00:00:00 in it."
  {:local '(InstantFn 1970 1 1 0 0 0)
   :utc   '(StartFn (DatetimeFn "1970-01-01T00:00:00Z"))})

(defn- second-key
  "`[[dimension base-unit] factor handles]` of one `Second` in `context`'s unit table
  (`provers/measure-with-support`): the key and factor a calendar moment's offset is read
  in, and the rows it rests on."
  [kb context]
  (let [[[k f] sup] (provers/measure-with-support kb '(QuantityFn 1 Second) context)]
    [k f sup]))

(defn- anchor
  "`[node offset]` for a metric term `x`: a node term at offset 0, or a calendar moment at
  its frame's epoch node, its seconds after the epoch (`dt/epoch-second`) times `factor`;
  nil for any other term."
  [factor x]
  (if (node-term? x)
    [x 0]
    (when-let [[frame fields] (tp/moment x)]
      (some->> (dt/epoch-second fields) (* factor) provers/round-magnitude (vector (epochs frame))))))

(defn- stated-constraints
  "Every believed, visible `(temporalDistance P Q M)` over two metric terms as `[[dimension
  base-unit] P Q lo hi support]`, the magnitudes in the base unit and snapped by
  `provers/round-magnitude`.  `support` is the fact's handle plus the unit-table rows it
  converted through."
  [kb context]
  (vec
   (for [m (res/matches-visible kb '(temporalDistance ?p ?q ?m) context)
         :let  [b (second m), p (get b '?p), q (get b '?q), measure (get b '?m)]
         :when (and (metric-term? p) (metric-term? q) (provers/measure? measure))
         :let  [[[k lo hi] sup] (provers/measure-with-support kb measure context)]]
     [k p q
      (provers/round-magnitude lo) (provers/round-magnitude hi)
      (conj sup (first m))])))

(defn- instant-constraints
  "Every believed, visible `(includesInstant T X)` with `T` a calendar term or range and `X`
  a node term, as a stated constraint (`stated-constraints`) under the key `k` from the
  epoch node of `T`'s frame to `X`: between `T`'s start and end offsets (`anchor`), closed
  at both ends, resting on the fact and `sup`."
  [kb context k factor sup]
  (vec
   (for [m (res/matches-visible kb '(includesInstant ?t ?x) context)
         :let  [b (second m), t (get b '?t), x (get b '?x)
                [n lo] (anchor factor (list 'StartFn t))
                [_ hi] (anchor factor (list 'EndFn t))]
         :when (and n hi (node-term? x))]
     [k n x lo hi (conj sup (first m))])))

(defn- placed
  "The stated constraint `c` between two node terms: `c` itself when both are nodes, else,
  under `Second`'s key `sk`, the constraint between their anchors (`anchor`), resting also
  on `sup`; nil under another key."
  [[sk factor sup] [k p q lo hi hs :as c]]
  (if (and (node-term? p) (node-term? q))
    c
    (let [[np op] (anchor factor p)
          [nq oq] (anchor factor q)
          d       (when (and np nq (= k sk)) (- oq op))]
      (when d
        [k np nq (provers/round-magnitude (- lo d)) (provers/round-magnitude (- hi d)) (into hs sup)]))))

(defn- epoch-bound
  "The constraint between the two `epochs` nodes when the stated constraints `stated` name
  both: the UTC epoch at most `ZoneOffset/MAX` (18 hours) before or after the wall-clock
  one, the range every zone offset lies in, resting on `Second`'s rows `sup`; else nil."
  [[sk factor sup] stated]
  (let [{:keys [local utc]} epochs
        named (into #{} (mapcat (fn [[_ p q]] [p q])) stated)]
    (when (and (named local) (named utc))
      (let [b (provers/round-magnitude (* factor (.getTotalSeconds ZoneOffset/MAX)))]
        [sk local utc (- b) b sup]))))

(defn- report-mixed-dimensions!
  "File `:metric-temporal-mixed-dimensions` in the violations ledger and log it at :warn."
  [kb context dims]
  (let [entry {:violation :metric-temporal-mixed-dimensions
               :context   context
               :sentence  nil
               :detail    {:message    (str "the temporalDistance constraints visible from "
                                            context " span more than one dimension, so no"
                                            " metric temporal goal is answered there")
                           ;; a dimension may be a NAT; a unit is a symbol (`measure?`), so it
                           ;; takes the scalar key
                           :dimensions (nm/by-print-key (map first dims))
                           :units      (into [] (sort-by nm/name-key (map second dims)))}}]
    (trove/log! {:level :warn :id ::metric-temporal-mixed-dimensions :data entry})
    (violations/report-without-run kb entry)))

(defn- build-problem
  "The stated constraints, each `placed` between two nodes, as `{:dimension :unit :net
  :support}`, nil when none, or `{:mixed dims :handles #{handle} :instants #{instant}}`
  when they span more than one dimension; with `instant-constraints` and `epoch-bound` when
  they span `Second`'s or none.  `:support` is `{[p q] → #{handle}}`, both directions of each pair;
  `:handles` is every stated constraint's support, `:instants` every instant one names."
  [kb context]
  (let [[sk :as unit] (second-key kb context)
        stated        (into [] (keep #(placed unit %)) (stated-constraints kb context))
        stated        (if (every? #(= sk (first %)) stated)
                        (let [s (into stated (apply instant-constraints kb context unit))]
                          (if-let [eb (epoch-bound unit s)] (conj s eb) s))
                        stated)
        dims          (set (map first stated))]
    (cond
      (empty? stated)    nil
      (= 1 (count dims)) (let [[dim unit] (first dims)
                               {:keys [net support]}
                               (reduce (fn [state [_ p q lo hi sup]]
                                         (-> state
                                             (update :net narrow p q lo hi)
                                             (update-in [:support [p q]] (fnil into #{}) sup)
                                             (update-in [:support [q p]] (fnil into #{}) sup)))
                                       {:net {} :support {}} stated)]
                           {:dimension dim :unit unit :net net :support support})
      :else              {:mixed    dims
                          :handles  (into #{} (mapcat peek) stated)
                          :instants (into #{} (mapcat (fn [[_ p q]] [p q])) stated)})))

(defn- problem-or-refusal
  "`build-problem`'s answer for `context`, the refusal `{:mixed dims :handles}` included,
  and the refusal reported once per KB and context.  Resident on the KB's `:qcn` atom,
  keyed by the change clock and on the tolerance the magnitudes are snapped to."
  [kb context]
  (let [prob (observe/cached (reasoning/qcn kb) [::problem context provers/*quantity-tolerance*]
                             (fn [_stale] (build-problem kb context)))]
    (when-let [dims (:mixed prob)]
      (when (observe/newly-seen? (reasoning/qcn kb) [::reported-mixed context] dims)
        (report-mixed-dimensions! kb context dims)))
    prob))

(defn problem
  "Every `temporalDistance` and calendar `includesInstant` believed and visible from
  `context`, as
  `{:dimension :unit :net :support}`.  nil when nothing is stated, and nil — reported once
  per KB and context — when the constraints span more than one dimension."
  [kb context]
  (let [prob (problem-or-refusal kb context)]
    (when-not (:mixed prob) prob)))

;; ---- the closure, memoized on the network value --------------------------

(def ^:private closure-cache-limit 256)

(defonce ^{:private true
           :doc "Closed states keyed on `[network tolerance]` (`closure`).  Bounded, cleared
  wholesale when full."}
  closure-cache
  (atom {}))

(defn- inconsistency-detail
  "What makes the metric network `net` unsatisfiable: `{:pairs #{[p q]} :cycle #{instant}}`,
  the pairs unsatisfiable as written and the instants on a negative cycle.  Either set is
  empty when the other holds the whole clash."
  [net]
  (let [node-vec (nm/by-print-key (nodes net))]
    {:pairs (unsatisfiable-pairs net)
     :cycle (negative-cycle-nodes
             (shortest-paths! (distance-matrix net node-vec) (count node-vec))
             node-vec)}))

(defn- report-inconsistency!
  "File `:metric-temporal-inconsistency` for `prob` in the violations ledger, naming any
  pair unsatisfiable as written and the instants on a negative cycle, and log it at :warn.
  docs/stp.md gives the reasons this is a report and not a `wff` check."
  [kb context {:keys [net unit]}]
  (let [{bad :pairs cycle-nodes :cycle} (inconsistency-detail net)
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
    (violations/report-without-run kb entry)))

(defn- resident-closure
  "`(build stale)` held on the KB under `k` and the change clock beside `net`, where `stale`
  is the entry it replaces (`{:for net :result state}` or nil).  A resident hit is an
  `identical?` compare; a caller asking about another network gets `(build nil)`."
  [kb k net build]
  (let [entry (observe/cached (reasoning/qcn kb) k (fn [stale] {:for net :result (build stale)}))]
    (if (identical? net (:for entry)) (:result entry) (build nil))))

(defn closure
  "The closed network of `prob` across its nodes and `extra-nodes`, or `:inconsistent`.

  Memoized on `[net provers/*quantity-tolerance*]`, and resident per context and tolerance:
  `extra-nodes` are isolated and stay out of the key, so contexts and KBs holding one
  network share one pass.  Warm-started (`close-state-from`) when the network last
  resident for `context` is one this network tightens.  An inconsistency is reported once per KB, context and network
  (`observe/newly-seen?`), never on the memoized path."
  [kb context {:keys [net] :as prob} extra-nodes]
  (let [state (resident-closure
               kb [::pass context provers/*quantity-tolerance*] net
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
      (report-inconsistency! kb context prob))
    result))

(defn closed-network
  "The closed metric network visible from `context`: nil when `problem` is, else `closure`'s
  answer."
  [kb context]
  (when-let [prob (problem kb context)]
    (closure kb context prob nil)))

;; ---- what a derived bound rests on ---------------------------------------
;; The support of a bound is the constraints on its shortest chain each way, not the whole
;; network: docs/stp.md, "What a derived bound rests on".

(defonce ^{:private true
           :doc "The successor table per network value (`reconstruction`).  Its own cache so a
  metric goal that asks for no support allocates no `int[n²]`; no tolerance in the key,
  because `shortest-paths!` reads none."}
  via-cache
  (atom {}))

(defn- reconstruction
  "`{:node-vec :idx :nxt :n}` for `net`: the closed matrix's successor table and what a pair
  needs to reach it."
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
  constraint on the shortest chain each way.  `#{}` on the diagonal and for an instant `net`
  does not mention; every supporter in `support` when a chain cannot be walked."
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

(defn- gaps-support
  "`handles` together with the `path-support` of each `[p q]` in `gaps`."
  [net support handles gaps]
  (into handles (mapcat (fn [[p q]] (path-support net support p q))) gaps))

(defn separation
  "The tightest `[lo hi]` on `t(q) − t(p)` visible from `context`, as
  `[[dimension unit] lo hi]` in the base unit; `[-∞ ∞]` for a pair nothing reaches.  nil
  when nothing is stated or the network is inconsistent."
  [kb context p q]
  (when-let [{:keys [dimension unit] :as prob} (problem kb context)]
    (let [closed (closure kb context prob [p q])]
      (when-not (= :inconsistent closed)
        (into [[dimension unit]] (constraint closed p q))))))

;; ---- the bridge to intervals ---------------------------------------------

(defn stated-endpoint
  "`[endpoint handles]` from the believed `(pred i endpoint)` facts visible in `context`,
  `pred` `startOf` or `endOf`, an endpoint read when `(term? endpoint)`.  nil when they
  name none or two different instants; one instant restated in several visible contexts
  is one reading, all its handles named."
  [kb i context pred term?]
  (let [ms (res/matches-visible kb (list pred i '?p) context)
        ps (into #{} (comp (map (comp #(get % '?p) second)) (filter term?)) ms)]
    (when (= 1 (count ps))
      [(first ps) (into #{} (map first) ms)])))

(defn endpoints-with-support
  "Interval `i`'s `[[start end] handles]` from its `stated-endpoint`s and those facts'
  handles, an endpoint read when `(term? endpoint)`, by default a symbol.  nil when either
  is missing."
  ([kb i context] (endpoints-with-support kb i context node-term?))
  ([kb i context term?]
   (let [[s sh] (stated-endpoint kb i context 'startOf term?)
         [e eh] (stated-endpoint kb i context 'endOf term?)]
     (when (and s e) [[s e] (into sh eh)]))))

(defn- endpoints-of-matches
  "`{interval [[start end] #{handle}]}` for each interval a visible match of one of
  `patterns` binds as `?i` and `endpoints-with-support` reads."
  [kb context patterns]
  (into {}
        (keep (fn [i] (when-let [e (endpoints-with-support kb i context)] [i e])))
        (into #{}
              (comp (mapcat #(res/matches-visible kb % context))
                    (map (comp #(get % '?i) second))
                    (filter node-term?))
              patterns)))

(defn intervals-with-endpoints
  "`{interval [[start end] #{handle}]}` for every interval `endpoints-with-support` reads,
  or with `starts`, for each whose visible stated start is one of `starts`."
  ([kb context]
   (endpoints-of-matches kb context (for [p endpoint-predicates] (list p '?i '?p))))
  ([kb context starts]
   (endpoints-of-matches kb context (for [t starts] (list 'startOf '?i t)))))

(def allen-narrowing-sources
  "Every predicate the metric narrowing of the interval algebra reads: the constraints, the
  endpoint predicates and the unit table.  `vaelii.impl.interval` declares these as the
  narrowing's `:sources`."
  (into (into network-predicates endpoint-predicates) provers/unit-table-predicates))

(def allen-narrowing-bindings
  "The dynamic vars the metric narrowing of the interval algebra reads: the tolerance the
  magnitudes are snapped to.  `vaelii.impl.interval` declares these as the narrowing's
  `:bindings`."
  [#'provers/*quantity-tolerance*])

(defn unsatisfiable-narrowing
  "The narrowing an unsatisfiable or refused source answers over `intervals`, the intervals
  its unsatisfiable component bounds: the pair from the first under `nm/print-key` to each
  other emptied both ways, or the first's diagonal emptied when it is the only one,
  `support` behind each.  An empty constraint is unsatisfiable as given, so the component
  of the interval network holding those intervals is unsatisfiable, and no goal naming one
  is answered (docs/qcn.md, \"Unsatisfiability is per component\").  nil for no intervals.

  `:unsatisfiable-sources` carries `source`, the description of the clash in the source
  network or of its refusal, with the emptied pairs as its `:stand-in`: they stand in for
  the source's clash or refusal and are not pairs any interval fact contradicts
  (`qcn-kb/unsatisfiable-sources`).

  Answering nil instead would widen the interval network when a fact arrives, and an
  entailment drawn through the narrowing would stop holding while the firing that rested
  on it stayed believed (docs/qcn.md, \"A network can have a second reader\")."
  [intervals support source]
  (let [[i & more] (nm/by-print-key (set intervals))]
    (when i
      (let [pairs (if more (into #{} (mapcat (fn [j] [[i j] [j i]])) more) #{[i i]})]
        {:net                   (zipmap pairs (repeat #{}))
         :support               (zipmap pairs (repeat support))
         :unsatisfiable-sources [(assoc source :stand-in pairs)]}))))

(defn merge-narrowings
  "`narrowings` intersected pair by pair, their support unioned and their unsatisfiable
  sources listed in order.  An absent pair is the universe in each, so a pair one of them
  narrows takes that one's set.  nil when every one is nil."
  [narrowings]
  (when-let [ns (seq (remove nil? narrowings))]
    (let [srcs (into [] (mapcat :unsatisfiable-sources) ns)]
      (cond-> {:net     (or (apply merge-with set/intersection (map :net ns)) {})
               :support (or (apply merge-with set/union (map :support ns)) {})}
        (seq srcs) (assoc :unsatisfiable-sources srcs)))))

(defn- inconsistency-source
  "The `:metric` source description of unsatisfiable `prob`: the pairs unsatisfiable as
  written, the instants on a negative cycle, and as `:support` the handles behind the
  constraints among those pairs and instants (`stated-constraints`' support)."
  [{:keys [net support]}]
  (let [{:keys [pairs cycle]} (inconsistency-detail net)]
    {:source  :metric
     :pairs   (nm/by-print-key pairs)
     :cycle   (nm/by-print-key cycle)
     :support (into #{}
                    (mapcat (fn [[[p q :as pair] hs]]
                              (when (or (contains? pairs pair)
                                        (and (contains? cycle p) (contains? cycle q)))
                                hs)))
                    support)}))

(defn- bounded-by
  "The intervals of `ends` (`intervals-with-endpoints`) with an endpoint in `instants`."
  [ends instants]
  (keep (fn [[i [e]]] (when (some #(contains? instants %) e) i)) ends))

(defn- pairwise-narrowing
  "The Allen relations the closed metric network `closed` leaves between each two
  intervals of `ends`, only narrowed pairs recorded.  A pair's support is both intervals'
  endpoint facts and the chains of `net` behind the four `endpoint-gaps`."
  [closed net support ends]
  (reduce
   (fn [acc [[i [ei hi]] [j [ej hj]]]]
     (let [rels (relations-from-endpoints closed ei ej)]
       (if (= rels allen-relations)
         acc
         (-> acc
             (assoc-in [:net [i j]] rels)
             (assoc-in [:support [i j]]
                       (gaps-support net support (into hi hj)
                                     (vals (endpoint-gaps ei ej))))))))
   {:net {} :support {}}
   (for [a ends b ends :when (not= (key a) (key b))] [a b])))

(defn- per-component-narrowing
  "The narrowing of unsatisfiable `prob`, one connected component of its network at a
  time (`qcn/components`): each unsatisfiable component answers `unsatisfiable-narrowing`
  over the intervals it bounds, its source described by `inconsistency-source` over that
  component, and the satisfiable rest narrows the intervals no unsatisfiable component
  bounds as a satisfiable network does."
  [kb context {:keys [net support] :as prob} ends]
  (let [bad   (filterv #(= :inconsistent (close (qcn/select-nodes net %) %))
                       (qcn/components net))
        gone  (into #{} cat bad)
        sat   (qcn/drop-nodes net gone)
        free  (into {} (remove (fn [[_ [e]]] (some #(contains? gone %) e))) ends)
        rest  (when (>= (count free) 2)
                (let [closed (closure kb context (assoc prob :net sat)
                                      (mapcat (comp first val) free))]
                  (when (map? closed)
                    (pairwise-narrowing closed sat (qcn/drop-nodes support gone) free))))]
    (merge-narrowings
     (cons rest
           (for [comp bad
                 :let [sub (qcn/select-nodes support comp)]]
             (unsatisfiable-narrowing (bounded-by ends comp)
                                      (into #{} (mapcat val) sub)
                                      (inconsistency-source
                                       {:net (qcn/select-nodes net comp) :support sub})))))))

(defn allen-narrowing-with-support
  "What the metric layer determines about the Allen relations, as
  `{:net {[i j] → #{base relations}} :support {[i j] → #{handle}}}` in the calculus
  narrowing shape.  A pair's support is both intervals' endpoint facts and the chains behind
  the four `endpoint-gaps`.  Only narrowed pairs are recorded.  nil with no constraints, no
  interval with both endpoints, or one such interval and a satisfiable network.  An
  unsatisfiable network answers `per-component-narrowing`.  A problem refused for spanning
  more than one dimension answers `unsatisfiable-narrowing` over the intervals its
  constraints bound, its `:metric` source naming the `:dimensions` (docs/stp.md,
  \"Constraints are measures\")."
  [kb context]
  (when-let [{:keys [net support mixed handles instants] :as prob} (problem-or-refusal kb context)]
    (let [ends (intervals-with-endpoints kb context)]
      (when (seq ends)
        (if mixed
          (unsatisfiable-narrowing (bounded-by ends instants) handles
                                   {:source     :metric
                                    :dimensions (nm/by-print-key (map first mixed))
                                    :support    handles})
          (let [closed (closure kb context prob (mapcat (comp first val) ends))]
            (cond
              (= :inconsistent closed)  (per-component-narrowing kb context prob ends)
              (>= (count ends) 2)       (pairwise-narrowing closed net support ends))))))))

(defn allen-narrowing
  "`allen-narrowing-with-support`'s relation sets alone."
  [kb context]
  (:net (allen-narrowing-with-support kb context)))

(defn overlap-window-with-support
  "The metric bound on how long intervals `i1` and `i2` overlap, as
  `[[[dimension unit] lo hi] handles]` — `hi` possibly infinite — with the endpoint facts
  and the chains behind the four `overlap-gaps` as its support.  nil when there is nothing
  to read, the network is inconsistent, or the bound is the vacuous `[0 ∞]`."
  [kb context i1 i2]
  (when-let [{:keys [dimension unit net support] :as prob} (problem kb context)]
    (let [[e1 h1] (endpoints-with-support kb i1 context)
          [e2 h2] (endpoints-with-support kb i2 context)]
      (when (and e1 e2)
        (let [closed (closure kb context prob (concat e1 e2))]
          (when-not (= :inconsistent closed)
            (let [[lo hi] (overlap-bounds-from-endpoints closed e1 e2)]
              (when-not (and (zero? lo) (not (Double/isFinite (double hi))))
                [[[dimension unit] lo hi]
                 (gaps-support net support (into h1 h2) (overlap-gaps e1 e2))]))))))))

;; ---- the prover ----------------------------------------------------------

(defn- solve-distance-with-support
  "`(temporalDistance P Q M)` as `[[bindings handles] …]`, between the anchors of `P` and
  `Q` (`anchor`), their offsets added: an open `M` binds the derived bound when both sides
  are finite; a ground `M` checks that the derived bound lies inside it, its support adding
  the stated measure's own unit-table rows.  Two calendar moments of one frame need no
  stated constraint."
  [kb goal context]
  (let [[_ p q m] goal
        nodes?    (and (node-term? p) (node-term? q))
        [sk f us] (when-not nodes? (second-key kb context))
        [np op]   (anchor f p)
        [nq oq]   (anchor f q)
        prob      (problem kb context)
        key       (if prob [(:dimension prob) (:unit prob)] sk)]
    (when (and np nq (or prob (and (not nodes?) (= np nq))) (or nodes? (= key sk)))
      (let [closed (if prob (closure kb context prob [np nq]) {})]
        (when-not (= :inconsistent closed)
          (let [[lo hi] (map #(+ % (- oq op)) (constraint closed np nq))
                sup     (delay (cond-> (if prob (path-support (:net prob) (:support prob) np nq) #{})
                                 (not nodes?) (into us)))]
            (cond
              (sx/variable? m)
              (when (and (Double/isFinite (double lo)) (Double/isFinite (double hi)))
                [[{m (provers/render-quantity lo hi (second key))} @sup]])

              (provers/measure? m)
              (let [[[k slo shi] msup] (provers/measure-with-support kb m context)
                    eps                provers/*quantity-tolerance*]
                (if (and (= key k)
                         (>= lo (- slo eps))
                         (<= hi (+ shi eps)))
                  [[{} (into @sup msup)]]
                  []))

              :else [])))))))

(defrecord TemporalDistanceProver []
  prover-types/Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 4 (count goal))
         (contains? stp-predicates (first goal))
         (metric-term? (nth goal 1)) (metric-term? (nth goal 2))
         (let [m (nth goal 3)] (or (sx/variable? m) (provers/measure? m)))))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (map first (solve-distance-with-support kb goal context)))

  prover-types/SupportingProver
  (support-functors [_] stp-predicates)
  ;; not `startOf` / `endOf`: a `temporalDistance` goal names its instants directly
  (support-sources [_] (into network-predicates provers/unit-table-predicates))
  (solve-with-support [_ kb goal context] (solve-distance-with-support kb goal context)))

(defn stp-prover
  "The metric temporal prover — `(vaelii.core/add-reasoner kb :metric-time)`."
  []
  (->TemporalDistanceProver))

;; ---- cache registration --------------------------------------------------
;; Registered here, so a process that never loaded this namespace reports no row.

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

(caches/register-derived
 {:id :K5 :label "Metric closures and reconstructions" :cache :metric-closures :kind :cache
  :holds-content? false
  :keyed-by :value :reads [] :retired-by {:caches-cleared :W} :computed :read
  :imaged? false :var [#'closure-cache #'via-cache]
  :value (fn [_] [@closure-cache @via-cache])
  :note "content-keyed by network and tolerance (also registered as `:metric-reconstructions`); cleared at the bound"})
