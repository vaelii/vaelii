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

(defn moment
  "`[frame fields]` of the moment `x` names, or nil when the calendar does not place it:
  an `(InstantFn …)` term or a point of a calendar term or range, in frame `:local`, or a
  point of a time with a UTC offset or zone, in frame `:utc` (`dt/utc-extent`)."
  [x]
  (if-let [f (dt/instant-fields x)]
    [:local f]
    (when-let [[frame [s e]] (when-let [t (thing-of x)]
                               (or (some->> (dt/extent t) (vector :local))
                                   (some->> (dt/utc-extent t) (vector :utc))))]
      [frame (case (point-functions (first x))
               (:start :earliest-start :latest-start) s
               (:end :earliest-end :latest-end)       e)])))

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

(defn constraints-over
  "The constraints the point terms among `nodes` fix, as `{:net … :support {}}` in the
  point algebra's relations, or nil when they fix none.  Each thing any of whose points
  is a node brings its start and end in, and each moment any of whose points is a node
  brings itself in, transitively for a point of a point."
  [nodes]
  (let [nodes   (into (set nodes)
                      (mapcat #(take-while point-term? (iterate thing-of (thing-of %))))
                      nodes)
        {moments true things false}
        (group-by moment? (into #{} (keep thing-of) nodes))
        present (-> nodes
                    (into moments)
                    (into (mapcat #(vector (point :start %) (point :end %))) things))
        edges   (concat (mapcat #(thing-edges % present) things)
                        (mapcat #(moment-edges % present) moments)
                        (calendar-edges present))]
    (when (seq edges)
      {:net (reduce add-edge {} edges) :support {}})))
