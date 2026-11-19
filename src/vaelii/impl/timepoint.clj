;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.timepoint
  "The six point terms of a temporal thing (`StartFn` … `LatestEndFn`), and
  `constraints-over`, the point network's node-set reader: the order the terms fix among
  themselves, carrying no support.  See docs/time.md, \"The points of a temporal thing\"."
  (:require [clojure.set :as set]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.sentex :as sx]))

(def point-functions
  "Each point function, and which of a thing's bounds it names."
  '{StartFn         :start
    EndFn           :end
    EarliestStartFn :earliest-start
    LatestStartFn   :latest-start
    EarliestEndFn   :earliest-end
    LatestEndFn     :latest-end})

(defn- ground-term? [x]
  (if (sequential? x) (every? ground-term? x) (not (sx/variable? x))))

(defn point-term?
  "Is `x` a ground application of one of the six point functions?"
  [x]
  (and (seq? x) (= 2 (count x)) (contains? point-functions (first x))
       (ground-term? (second x))))

(defn node-term?
  "A term the point network takes as a node: an instant named by a symbol, a point of a
  thing, or a calendar moment."
  [x]
  (or (and (symbol? x) (not (sx/variable? x)))
      (point-term? x)
      (dt/instant-term? x)))

(defn thing-of
  "The thing a point term belongs to, or nil for any other term."
  [x]
  (when (point-term? x) (second x)))

(defn point
  "The term naming `which` point of `thing` — `:start`, `:end`, `:earliest-start` …"
  [which thing]
  (list (some (fn [[f w]] (when (= w which) f)) point-functions) thing))

(def ^:private side-of
  "Each point function's side of its thing."
  '{StartFn :start, EarliestStartFn :start, LatestStartFn :start
    EndFn :end, EarliestEndFn :end, LatestEndFn :end})

(def open-functions
  "The functions whose application `(F W)` names a time with one bound, `{F [bounded
  unbounded]}`: `(IntervalBeforeFn W)` ends at W and has no start, `(IntervalAfterFn W)`
  starts at W and has no end (time.txt)."
  '{IntervalBeforeFn [:end :start], IntervalAfterFn [:start :end]})

(defn open-side
  "`[k W]` for a point term `x` of an application `(F W)` of `open-functions`, else nil.
  `k` is `:bound` for a point on the bounded side, which is W.  It is `:unbounded` for a
  point on the other side, which lies before (a start) or after (an end) every moment."
  [x]
  (let [t (thing-of x)]
    (when (and (seq? t) (= 2 (count t)))
      (when-let [[b u] (open-functions (first t))]
        (condp = (side-of (first x))
          b [:bound (second t)]
          u [:unbounded (second t)]
          nil)))))

(defn moment
  "`[frame fields]` of the moment `x` names, or nil when the calendar does not place it.
  Frame `:local` holds an `(InstantFn …)` term and a point of a calendar term or range,
  and frame `:utc` a point of a time with a UTC offset or zone (`dt/utc-extent`).  A point
  on the bounded side of an `open-functions` application is the moment of its argument."
  [x]
  (if-let [f (dt/instant-fields x)]
    [:local f]
    (or (when-let [[frame [s e]] (when-let [t (thing-of x)]
                                   (or (some->> (dt/extent t) (vector :local))
                                       (some->> (dt/utc-extent t) (vector :utc))))]
          [frame (if (= :start (side-of (first x))) s e)])
        (let [[k w] (open-side x)] (when (= :bound k) (moment w))))))

;; ---- the constraints the terms fix --------------------------------------

(def ^:private strict  [#{:before} #{:after}])
(def ^:private weak    [#{:before :equal} #{:after :equal}])
(def ^:private same    [#{:equal} #{:equal}])

(def ^:private universe #{:before :equal :after})

(defn- add-edge [net [a b [fwd bwd]]]
  (-> net
      (update [a b] (fnil set/intersection universe) fwd)
      (update [b a] (fnil set/intersection universe) bwd)))

(def thing-order
  "The order a thing's six points fix among themselves, `[lower upper strict?]`."
  [[:start :end true] [:earliest-start :start false] [:start :latest-start false]
   [:earliest-end :end false] [:end :latest-end false]
   [:earliest-start :earliest-end false] [:latest-start :latest-end false]])

(defn- thing-edges
  "The order among `x`'s points, over the ones in `present`."
  [x present]
  (for [[lo hi s] thing-order
        :let [a (point lo x) b (point hi x)]
        :when (and (present a) (present b))]
    [a b (if s strict weak)]))

(defn- moment?
  "Does the term `x` name a moment by its spelling — an `(InstantFn …)` term or a point?"
  [x]
  (or (point-term? x) (dt/instant-term? x)))

(defn- moment-edges
  "Each point of the moment `m` in `present`, equal to `m`."
  [m present]
  (for [w (vals point-functions) :let [p (point w m)] :when (present p)] [p m same]))

(defn- calendar-edges
  "Each calendar moment in `present` ordered against the next one in its frame by its
  fields: a moment in no zone and an absolute one are not ordered."
  [present]
  (->> (keep (fn [x] (when-let [m (moment x)] [m x])) present)
       (group-by ffirst)
       (sort-by key)
       (mapcat (fn [[_ ms]]
                 (->> (sort-by first ms)
                      (partition 2 1)
                      (map (fn [[[ma a] [mb b]]] [a b (if (= ma mb) same strict)])))))))

(defn- open-edges
  "The order of each `open-functions` point in `present`.  A point on the bounded side
  equals the argument.  A point on the unbounded side lies at or before (a start) or at
  or after (an end) every other point, and strictly so against a moment the calendar
  places."
  [present]
  (for [p present
        :let [[k w] (open-side p)]
        :when k
        e (if (= :bound k)
            [[p w same]]
            (for [q present :when (not= p q)]
              [p q (cond-> (if (moment q) strict weak) (= :end (side-of (first p))) rseq)]))]
    e))

(defn constraints-over
  "The constraints the point terms among `nodes` fix, as `{:net … :support {}}` in the
  point algebra's relations, or nil when they fix none.  Each thing any of whose points
  is a node brings its start and end in, and each moment any of whose points is a node
  brings itself in, transitively for a point of a point.  A bounded point of an
  `open-functions` application brings its argument in."
  [nodes]
  (let [nodes   (into (set nodes)
                      (mapcat #(take-while point-term? (iterate thing-of (thing-of %))))
                      nodes)
        {moments true things false}
        (group-by moment? (into #{} (keep thing-of) nodes))
        present (-> nodes
                    (into moments)
                    (into (mapcat #(vector (point :start %) (point :end %))) things))
        present (into present (keep #(let [[k w] (open-side %)] (when (= :bound k) w))) present)
        edges   (concat (mapcat #(thing-edges % present) things)
                        (mapcat #(moment-edges % present) moments)
                        (calendar-edges present)
                        (open-edges present))]
    (when (seq edges)
      {:net (reduce add-edge {} edges) :support {}})))
