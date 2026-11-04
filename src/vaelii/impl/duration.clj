;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.duration
  "Interval duration arithmetic: `DurationProver` answers `(totalDuration (list I1 I2 …) D)`
  and `(overlapDuration I1 I2 D)` from the stored `(length I M)` facts, on `[lo hi]`
  magnitude bounds, with the overlap sharpened by `stp/overlap-window-with-support`.
  Opt-in, as the `:duration` reasoner.  See docs/duration.md."
  (:require [clojure.set :as set]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.types.prover :as prover-types]))

;; ---- measures in and out -------------------------------------------------

(defn- emit
  "Bind or check the answer slot `d` against the computed `[lo hi]` bounds in `unit`, as
  `[[bindings handles]]` or `[]`.  A variable takes the rendered measure.  A ground measure
  checks when its dimension, base unit and both normalized bounds agree within tolerance,
  and its support adds the stated measure's unit-table rows to `sup`."
  [kb context [dim unit] lo hi d sup]
  (cond
    (sx/variable? d) [[{d (provers/render-quantity lo hi unit)} sup]]
    (provers/measure? d) (let [[[k lo* hi*] msup] (provers/measure-with-support kb d context)]
                           (if (and (= [dim unit] k)
                                    (provers/q= lo lo*) (provers/q= hi hi*))
                             [[{} (into sup msup)]]
                             []))
    :else []))

;; ---- reading an interval's own length ------------------------------------

(defn- interval-length-with-support
  "The believed length of interval `i` as `[[[dimension base-unit] lo hi] handles]`, the
  bounds snapped to the tolerance grid, or nil when the KB states no length for `i` or two
  that differ once normalized.  Only a `length` match whose measure is a structural
  quantity term (`provers/measure?`) is read; a match naming its measure by a symbol is
  skipped.  The handles are each match read and the unit rows each converted through."
  [kb i context]
  (let [ms (res/matches-visible kb (list 'length i '?m) context)
        rs (into []
                 (keep (fn [m]
                         (let [measure (get (second m) '?m)]
                           (when (provers/measure? measure)
                             (let [[[k lo hi] sup] (provers/measure-with-support kb measure context)]
                               [[k (provers/round-magnitude lo) (provers/round-magnitude hi)]
                                (conj sup (first m))])))))
                 ms)
        ls (into #{} (map first) rs)]
    (when (= 1 (count ls))
      [(first ls) (into #{} (mapcat second) rs)])))

;; ---- the two computations ------------------------------------------------

(defn- list-form?
  "Is `x` the `(list I1 I2 …)` term `totalDuration` takes its components as?"
  [x]
  (and (sequential? x) (seq x) (= 'list (first x))))

(defn- interval-term? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- sum-bounds
  "The summed `[dim lo hi]` of several normalized lengths, or nil when they do not all
  share one `dim`."
  [lengths]
  (let [dims (set (map first lengths))]
    (when (= 1 (count dims))
      [(first dims) (reduce + (map second lengths)) (reduce + (map #(nth % 2) lengths))])))

(defn overlap-bounds
  "The `[lo hi]` overlap of two intervals, given the Allen relations `rels` still possible
  between them and each one's `[lo hi]` length:

  * `rels` within `temporallyDisjoint` — `[0 0]`;
  * within `subintervalOf` — the first length;
  * within `hasSubinterval` — the second length;
  * otherwise `[0, min(hi1, hi2)]`.

  Nil for an empty `rels`, which is an inconsistent network."
  [rels [lo1 hi1] [lo2 hi2]]
  (cond
    (empty? rels)                                              nil
    (set/subset? rels (stp/interval-denotation 'temporallyDisjoint)) [0 0]
    (set/subset? rels (stp/interval-denotation 'subintervalOf))      [lo1 hi1]
    (set/subset? rels (stp/interval-denotation 'hasSubinterval))     [lo2 hi2]
    :else                                                      [0 (min hi1 hi2)]))

(defn- solve-total
  "`(totalDuration (list I1 I2 …) D)`: the components' summed lengths, bound or checked,
  resting on every component's length reading."
  [kb goal context]
  (let [[_ components d] goal
        intervals (rest components)]
    (when (and (seq intervals) (every? interval-term? intervals))
      (let [reads (map #(interval-length-with-support kb % context) intervals)]
        (when (every? some? reads)
          (when-let [[dim lo hi] (sum-bounds (map first reads))]
            (emit kb context dim lo hi d (into #{} (mapcat second) reads))))))))

(defn- intersect-bounds
  "The intersection `[max of the los, min of the his]` of two bounds on one quantity.  Bounds
  that cross by no more than the tolerance collapse to the point `[hi hi]`; bounds that cross
  by more give nil."
  [[lo1 hi1] [lo2 hi2]]
  (let [lo (max lo1 lo2), hi (min hi1 hi2)]
    (cond
      (<= lo hi)      [lo hi]
      (provers/q= lo hi) [hi hi]
      :else           nil)))

(defn- sharpen-overlap
  "`bounds` intersected with `stp/overlap-window-with-support`'s overlap window for `i1` and `i2`,
  as `[bounds-or-nil handles]`.  The overlap window is read in only when its `[dimension unit]` is
  `dim`, and its handles join the support only then; otherwise `[bounds #{}]`."
  [kb context dim i1 i2 bounds]
  (if-let [[[wdim wlo whi] wsup] (stp/overlap-window-with-support kb context i1 i2)]
    (if (= dim wdim) [(intersect-bounds bounds [wlo whi]) wsup] [bounds #{}])
    [bounds #{}]))

(defn- solve-overlap
  "`(overlapDuration I1 I2 D)`: `overlap-bounds` over both lengths and the possible Allen
  relations, sharpened, bound or checked.  The support is both length readings,
  `iv/allen-support` for the pair and the metric overlap window's support."
  [kb goal context]
  (let [[_ i1 i2 d] goal]
    (when (and (interval-term? i1) (interval-term? i2))
      (let [[[dim1 lo1 hi1] s1] (interval-length-with-support kb i1 context)
            [[dim2 lo2 hi2] s2] (interval-length-with-support kb i2 context)]
        (when (and dim1 dim2 (= dim1 dim2))
          (when-let [bounds (overlap-bounds (iv/possible-allen-relations kb context i1 i2)
                                            [lo1 hi1] [lo2 hi2])]
            (let [[sharp msup] (sharpen-overlap kb context dim1 i1 i2 bounds)]
              (when-let [[lo hi] sharp]
                (emit kb context dim1 lo hi d
                      (-> (into s1 s2)
                          (into (iv/allen-support kb context i1 i2))
                          (into msup)))))))))))

;; ---- the prover ----------------------------------------------------------

(def duration-predicates
  "The two computed predicates this prover answers — neither ever stored."
  '#{totalDuration overlapDuration})

(defn- solve-with-support-for
  "The prover's answers as `[bindings support]` pairs, dispatched on the goal's functor.
  `Prover/solve` takes its bindings off this, so the two answer alike."
  [kb goal context]
  (case (first goal)
    totalDuration   (solve-total kb goal context)
    overlapDuration (solve-overlap kb goal context)
    nil))

(defn- answer-slot?
  "Can `d` be the answer argument — a variable to bind, or a ground measure to check?"
  [d]
  (or (sx/variable? d) (provers/measure? d)))

(defrecord DurationProver []
  prover-types/Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (seq goal)
         (case (first goal)
           totalDuration   (and (= 3 (count goal))
                                (list-form? (nth goal 1))
                                (answer-slot? (nth goal 2)))
           overlapDuration (and (= 4 (count goal))
                                (interval-term? (nth goal 1))
                                (interval-term? (nth goal 2))
                                (answer-slot? (nth goal 3)))
           false)))
  (est-bindings [_ _ _ _] 1)
  (cost         [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (map first (solve-with-support-for kb goal context)))

  prover-types/SupportingProver
  (support-functors [_] duration-predicates)
  (support-sources [_]
    (-> #{'length}
        (into provers/unit-table-predicates)
        (into stp/network-predicates)
        (into stp/endpoint-predicates)
        (into (iv/allen-predicates))))
  (solve-with-support [_ kb goal context] (solve-with-support-for kb goal context)))

(defn duration-prover
  "The interval-duration arithmetic prover, registered as the `:duration` reasoner."
  []
  (->DurationProver))
