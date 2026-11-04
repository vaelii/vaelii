;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.point
  "The point algebra over time instants as a `vaelii.impl.qcn` relation algebra and a
  `qcn-kb` calculus: three base relations, three derived predicates, nodes including a
  thing's point terms and calendar moments (`vaelii.impl.timepoint`), and
  `IncludesInstantProver`, which reads a thing against a moment off the network.  See
  docs/time.md and docs/qcn.md."
  (:require [clojure.set :as set]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.timepoint :as tp]
            [vaelii.impl.types.prover :as prover-types]))

;; ---- the algebra --------------------------------------------------------

(def all-relations
  "The three instant relations: the universe of the algebra."
  #{:before :equal :after})

(def point-converse
  "Each base relation's converse."
  {:before :after, :equal :equal, :after :before})

(defn converse-set
  "The converse of a relation set."
  [rels]
  (into #{} (map point-converse) rels))

(def point-composition
  "`(get-in point-composition [r1 r2])` is the set of base relations possible between a and
  c given `r1`(a,b) and `r2`(b,c)."
  {:before {:before #{:before} :equal #{:before} :after all-relations}
   :equal  {:before #{:before} :equal #{:equal}  :after #{:after}}
   :after  {:before all-relations :equal #{:after} :after #{:after}}})

(def compose
  "The composition of two relation sets: the union of the `point-composition` entries over every
  member pair (`qcn/compose-by`)."
  (qcn/compose-by point-composition))

(def point-algebra
  "The point algebra as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:equal}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under."
  '{:before instantBefore
    :equal  instantEqual
    :after  instantAfter})

(def instant-denotation
  "Every instant predicate — the three base ones and the three derived ones — mapped to the
  set of base relations it denotes.  A goal `(P a b)` is entailed exactly when the relations
  still possible between a and b are a subset of P's denotation."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{instantNotAfter  #{:before :equal}
     instantNotBefore #{:after :equal}
     instantNotEqual  #{:before :after}}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(defn- allen-fact-constraints
  "The constraints the believed Allen facts visible from `context` put on their two
  things' points, as `{:net … :support …}`, or nil when none narrows a pair.  `(P a b)`
  narrows each of the four endpoint comparisons (`stp/endpoint-gaps`) to the union, over
  `P`'s denotation, of `stp/endpoint-signature`'s ordering, both directions, each resting
  on the fact.  It reads the stored facts and not the interval network, which reads this
  one (docs/time.md, \"The points of a temporal thing\")."
  [kb context]
  (let [ends   #(vector (tp/point :start %) (tp/point :end %))
        named? #(and (symbol? %) (not (sx/variable? %)))
        r (reduce
           (fn [acc [hs a b den]]
             (reduce-kv
              (fn [acc k [p q]]
                (let [rels (into #{} (map #(get-in stp/endpoint-signature [% k])) den)]
                  (if (= all-relations rels)
                    acc
                    (-> acc
                        (update-in [:net [p q]] (fnil set/intersection all-relations) rels)
                        (update-in [:net [q p]] (fnil set/intersection all-relations)
                                   (converse-set rels))
                        (update-in [:support [p q]] (fnil into #{}) hs)
                        (update-in [:support [q p]] (fnil into #{}) hs)))))
              acc (stp/endpoint-gaps (ends a) (ends b))))
           {:net {} :support {}}
           (for [[pred den] stp/interval-denotation
                 [hs a b]   (qkb/asserted-pairs kb named? pred context)]
             [hs a b den]))]
    (when (seq (:net r)) r)))

(def instants
  "The point algebra as a `vaelii.impl.qcn-kb` calculus, with `timepoint/constraints-over`
  as its node-set narrowing and `allen-fact-constraints` as its stated-fact one."
  (qkb/calculus :point point-algebra instant-denotation
                {:fn         allen-fact-constraints
                 :over-nodes tp/constraints-over
                 :node?      tp/node-term?
                 :sources    (set (keys stp/interval-denotation))
                 :contexts   (set (keys stp/interval-denotation))}))

(defn possible-point-relations
  "The base relations still possible between instants `i1` and `i2` given everything
  believed in `context` — `#{}` when either lies in an unsatisfiable component."
  [kb context i1 i2]
  (qkb/possible instants kb context i1 i2))

(defn point-prover
  "The point-algebra entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover instants))

;; ---- a thing against a moment -------------------------------------------

(defn- readings
  "A fn of a moment `t` answering `[st te]`, each side a vector of `[rels pairs handles]`
  readings: the relations possible between `thing`'s start and `t` (`st`) and between `t`
  and its end (`te`), the network pairs each rests on, and the stated facts it reads.  The
  network's reading of the two point terms comes first.  A stated `startOf` `m` reads `st`
  as `m` against `t`, and `te` as what an end after `m` leaves, since an interval holds its
  start; a stated `endOf` `n` reads `te` as `t` against `n`.  The bounds are read once."
  [kb context thing]
  (let [rel    #(possible-point-relations kb context %1 %2)
        s      (tp/point :start thing)
        e      (tp/point :end thing)
        [m mh] (stp/stated-endpoint kb thing context 'startOf tp/node-term?)
        [n nh] (stp/stated-endpoint kb thing context 'endOf tp/node-term?)]
    (fn [t]
      (let [mt (when m (rel m t))]
        [(cond-> [[(rel s t) [[s t]] #{}]] m (conj [mt [[m t]] mh]))
         (cond-> [[(rel t e) [[t e]] #{}]]
           n (conj [(rel t n) [[t n]] nh])
           m (conj [(compose (converse-set mt) #{:before}) [[m t]] mh]))]))))

(defn- side-relations [side] (apply set/intersection (map first side)))

(defn- inclusion-verdict
  "Does a thing include the moment `t`, given `readings`' `[st te]` — at or after its start
  and before its end, the calendar terms' half-open convention?  `:true`, `:false` when `t`
  falls before the start or at or after the end, `:unknown` when the readings leave either
  side open, `:inconsistent` when they contradict each other or the network itself."
  [[st te]]
  (let [st (side-relations st)
        te (side-relations te)]
    (cond
      (or (empty? st) (empty? te))                                  :inconsistent
      (and (set/subset? st #{:before :equal}) (= te #{:before}))    :true
      (or (= st #{:after}) (set/subset? te #{:after :equal}))       :false
      :else                                                         :unknown)))

(defn- inclusion-literal
  "`[neg? thing t]` for a goal `(includesInstant thing t)` or its negation, each argument a
  variable or, for `t`, a node term; else nil."
  [goal]
  (let [neg? (and (sequential? goal) (= 2 (count goal)) (= sx/not-functor (first goal)))
        lit  (if neg? (second goal) goal)]
    (when (and (sequential? lit) (= 3 (count lit)) (= 'includesInstant (first lit)))
      (let [[_ x t] lit]
        (when (or (sx/variable? t) (tp/node-term? t)) [neg? x t])))))

(defn- inclusion-contexts [kb context]
  (if (sx/variable? context) (qkb/reader-contexts kb instants) [context]))

(defn- side-support
  "`[pairs handles]` of the first reading in `side` whose relations satisfy `ok?` alone,
  else of every reading in it."
  [side ok?]
  (if-let [[_ ps hs] (first (filter (comp ok? first) side))]
    [ps hs]
    [(mapcat second side) (into #{} (mapcat #(nth % 2)) side)]))

(defn- deciding-support
  "`[pairs handles]` a verdict of `v` rests on: both sides of `readings` for `:true`, and
  for `:false` the one or two that put `t` outside."
  [[st te] v]
  (let [at-or-after? #(set/subset? % #{:after :equal})
        sides (if (= v :true)
                [[st #(set/subset? % #{:before :equal})] [te #(= % #{:before})]]
                (cond-> []
                  (= (side-relations st) #{:after})  (conj [st #(= % #{:after})])
                  (at-or-after? (side-relations te)) (conj [te at-or-after?])))
        sups  (map #(apply side-support %) sides)]
    [(mapcat first sups) (into #{} (mapcat second) sups)]))

(defn- bounded-things
  "The things a believed `startOf` or `endOf` visible in `context` bounds."
  [kb context]
  (into #{} (comp (mapcat #(res/matches-visible kb (list % '?i '?p) context))
                  (map (comp #(get % '?i) second)))
        stp/endpoint-predicates))

(defn- entailed-inclusions
  "The answers `readings` give `goal` as `[bindings support]`, one per reader context that
  answers.  An open thing ranges over the things with a point in that context's network or
  a stated bound visible there (`bounded-things`), and an open moment over its nodes."
  [kb goal context support?]
  (let [[neg? x t] (inclusion-literal goal)
        want  (if neg? :false :true)
        open? sx/variable?]
    (for [c    (inclusion-contexts kb context)
          :let [ns (when (or (open? x) (open? t)) (qkb/nodes (qkb/network kb instants c)))]
          xv   (if (open? x) (into (into #{} (keep tp/thing-of) ns) (bounded-things kb c)) [x])
          :let [read (readings kb c xv)]
          tv   (if (open? t) ns [t])
          :when (or (not= x t) (= xv tv))
          :let [rels (read tv)]
          :when (= want (inclusion-verdict rels))]
      [(cond-> {} (open? x) (assoc x xv) (open? t) (assoc t tv))
       (when support?
         (let [[pairs hs] (deciding-support rels want)]
           (into hs (mapcat (fn [[a b]] (qkb/support instants kb c a b))) pairs)))])))

(defn- solve-inclusion
  "`goal`'s solutions as `[bindings support]` pairs, the one reader behind both prover
  methods.  `support?` false leaves the support nil and reads no support pass.  The
  network's answers come first, their support empty when the terms alone decide; a stored
  `includesInstant` fact the network does not entail follows, supported by its own handles.
  An answer both give carries the network's support alone, since the forward join matches
  the stored fact on its own."
  [kb goal context support?]
  (let [found    (entailed-inclusions kb goal context support?)
        sups     (reduce (fn [m [b s]] (update m b (fnil into #{}) s)) {} found)
        entailed (map (fn [b] [b (when support? (sups b))]) (distinct (map first found)))
        stored   (reduce (fn [m [h b]] (if (sups b) m (update m b (fnil conj #{}) h)))
                         {} (res/matches-visible kb goal context))]
    (concat entailed (map (fn [[b hs]] [b (when support? hs)]) stored))))

(defrecord IncludesInstantProver []
  prover-types/Prover
  ;; both polarities; completeness 100 holds because `solve-inclusion` reads the stored
  ;; literal as well
  (applicable? [_ _ goal _] (some? (inclusion-literal goal)))
  (est-bindings [_ _ goal _]
    (let [[_ x t] (inclusion-literal goal)]
      (if (or (sx/variable? x) (sx/variable? t)) provers/deferred-est 1)))
  (cost [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (map first (solve-inclusion kb goal context false)))
  prover-types/SupportingProver
  (support-functors [_] #{'includesInstant})
  (support-sources [_] (into stp/endpoint-predicates (keys instant-denotation)))
  (solve-with-support [_ kb goal context] (solve-inclusion kb goal context true)))

(defn includes-instant-prover
  "The prover answering `includesInstant` off the point network, to register with
  `vaelii.core/add-prover`."
  []
  (->IncludesInstantProver))
