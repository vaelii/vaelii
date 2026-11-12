;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.interval
  "Allen's interval algebra as a `vaelii.impl.qcn` relation algebra and a `qcn-kb`
  calculus: thirteen base relations, seven derived predicates, the transcribed composition
  table, and the two narrowings, metric (`stp`) and point (`points-narrowing-with-support`).
  See docs/time.md and docs/qcn.md."
  (:require [clojure.set :as set]
            [vaelii.impl.calendar :as cal]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.point :as pt]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.timepoint :as tp]))

;; ---- the algebra --------------------------------------------------------

(def all-relations
  "The thirteen interval relations: the universe of the algebra."
  #{:before :after :meets :met-by :overlaps :overlapped-by
    :starts :started-by :during :contains :finishes :finished-by :equal})

(def allen-converse
  "Each base relation's converse."
  {:before :after,     :after :before
   :meets :met-by,     :met-by :meets
   :overlaps :overlapped-by, :overlapped-by :overlaps
   :starts :started-by, :started-by :starts
   :during :contains,  :contains :during
   :finishes :finished-by, :finished-by :finishes
   :equal :equal})

(defn converse-set
  "The converse of a relation set."
  [rels]
  (into #{} (map allen-converse) rels))

;; Each block is the set of relations agreeing on the endpoint comparisons a composition
;; determines (docs/time.md, "The composition table, and why it is checked").

(def ^:private starts-first  "a-start < c-start" #{:before :meets :overlaps :finished-by :contains})
(def ^:private starts-last   "a-start > c-start" #{:after :met-by :overlapped-by :finishes :during})
(def ^:private ends-first    "a-end   < c-end"   #{:before :meets :overlaps :starts :during})
(def ^:private ends-last     "a-end   > c-end"   #{:after :met-by :overlapped-by :started-by :contains})
(def ^:private same-start    "a-start = c-start" #{:starts :started-by :equal})
(def ^:private same-end      "a-end   = c-end"   #{:finishes :finished-by :equal})
(def ^:private leads         "a-start < c-start and a-end < c-end" #{:before :meets :overlaps})
(def ^:private trails        "a-start > c-start and a-end > c-end" #{:after :met-by :overlapped-by})
(def ^:private ends-inside   "c-start < a-end   < c-end"   #{:overlaps :starts :during})
(def ^:private starts-inside "c-start < a-start < c-end"   #{:overlapped-by :during :finishes})
(def ^:private holds-c-start "a-start < c-start < a-end"   #{:overlaps :contains :finished-by})
(def ^:private holds-c-end   "a-start < c-end   < a-end"   #{:overlapped-by :contains :started-by})
(def ^:private concurrent
  "The nine relations under which two intervals share some time."
  (stp/interval-denotation 'sharesTimeWith))

(def allen-composition
  "The Allen composition table: `(get-in allen-composition [r1 r2])` is the set of base
  relations possible between A and C given `r1`(A,B) and `r2`(B,C)."
  {:before        {:before #{:before}     :after all-relations :meets #{:before}
                   :met-by ends-first    :overlaps #{:before}   :overlapped-by ends-first
                   :starts #{:before}     :started-by #{:before} :during ends-first
                   :contains #{:before}   :finishes ends-first  :finished-by #{:before}
                   :equal #{:before}}
   :after         {:before all-relations :after #{:after}       :meets starts-last
                   :met-by #{:after}      :overlaps starts-last :overlapped-by #{:after}
                   :starts starts-last   :started-by #{:after}  :during starts-last
                   :contains #{:after}    :finishes #{:after}    :finished-by #{:after}
                   :equal #{:after}}
   :meets         {:before #{:before}     :after ends-last      :meets #{:before}
                   :met-by same-end      :overlaps #{:before}   :overlapped-by ends-inside
                   :starts #{:meets}      :started-by #{:meets}  :during ends-inside
                   :contains #{:before}   :finishes ends-inside :finished-by #{:before}
                   :equal #{:meets}}
   :met-by        {:before starts-first  :after #{:after}       :meets same-start
                   :met-by #{:after}      :overlaps starts-inside :overlapped-by #{:after}
                   :starts starts-inside :started-by #{:after}  :during starts-inside
                   :contains #{:after}    :finishes #{:met-by}   :finished-by #{:met-by}
                   :equal #{:met-by}}
   :overlaps      {:before #{:before}     :after ends-last      :meets #{:before}
                   :met-by holds-c-end   :overlaps leads       :overlapped-by concurrent
                   :starts #{:overlaps}   :started-by holds-c-start :during ends-inside
                   :contains starts-first :finishes ends-inside :finished-by leads
                   :equal #{:overlaps}}
   :overlapped-by {:before starts-first  :after #{:after}       :meets holds-c-start
                   :met-by #{:after}      :overlaps concurrent  :overlapped-by trails
                   :starts starts-inside :started-by trails    :during starts-inside
                   :contains ends-last   :finishes #{:overlapped-by} :finished-by holds-c-end
                   :equal #{:overlapped-by}}
   :starts        {:before #{:before}     :after #{:after}       :meets #{:before}
                   :met-by #{:met-by}     :overlaps leads       :overlapped-by starts-inside
                   :starts #{:starts}     :started-by same-start :during #{:during}
                   :contains starts-first :finishes #{:during}  :finished-by leads
                   :equal #{:starts}}
   :started-by    {:before starts-first  :after #{:after}       :meets holds-c-start
                   :met-by #{:met-by}     :overlaps holds-c-start :overlapped-by #{:overlapped-by}
                   :starts same-start    :started-by #{:started-by} :during starts-inside
                   :contains #{:contains} :finishes #{:overlapped-by} :finished-by #{:contains}
                   :equal #{:started-by}}
   :during        {:before #{:before}     :after #{:after}       :meets #{:before}
                   :met-by #{:after}      :overlaps ends-first  :overlapped-by starts-last
                   :starts #{:during}     :started-by starts-last :during #{:during}
                   :contains all-relations :finishes #{:during} :finished-by ends-first
                   :equal #{:during}}
   :contains      {:before starts-first  :after ends-last      :meets holds-c-start
                   :met-by holds-c-end   :overlaps holds-c-start :overlapped-by holds-c-end
                   :starts holds-c-start :started-by #{:contains} :during concurrent
                   :contains #{:contains} :finishes holds-c-end :finished-by #{:contains}
                   :equal #{:contains}}
   :finishes      {:before #{:before}     :after #{:after}       :meets #{:meets}
                   :met-by #{:after}      :overlaps ends-inside :overlapped-by trails
                   :starts #{:during}     :started-by trails    :during #{:during}
                   :contains ends-last   :finishes #{:finishes} :finished-by same-end
                   :equal #{:finishes}}
   :finished-by   {:before #{:before}     :after ends-last      :meets #{:meets}
                   :met-by holds-c-end   :overlaps #{:overlaps} :overlapped-by holds-c-end
                   :starts #{:overlaps}   :started-by #{:contains} :during ends-inside
                   :contains #{:contains} :finishes same-end    :finished-by #{:finished-by}
                   :equal #{:finished-by}}
   :equal         {:before #{:before} :after #{:after} :meets #{:meets} :met-by #{:met-by}
                   :overlaps #{:overlaps} :overlapped-by #{:overlapped-by}
                   :starts #{:starts} :started-by #{:started-by}
                   :during #{:during} :contains #{:contains}
                   :finishes #{:finishes} :finished-by #{:finished-by}
                   :equal #{:equal}}})

(def compose
  "The composition of two relation sets: the union of the `allen-composition` entries over every
  member pair (`qcn/compose-by`)."
  (qcn/compose-by allen-composition))

(def allen-algebra
  "Allen's interval algebra as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:equal}
   :compose  compose
   :converse converse-set})

;; ---- the second readers: metric bounds, point facts and the calendar -----

(defn- node?
  "A term the interval network takes as a node: a symbol that is not a variable, or a term
  the calendar gives an extent in one frame (`dt/extent`, `dt/utc-extent`)."
  [x]
  (if (symbol? x)
    (not (sx/variable? x))
    (some? (or (dt/extent x) (dt/utc-extent x)))))

(defn- calendar-relations
  "The relation the calendar gives each pair of terms among `nodes` it gives an extent in
  one frame (`calendar/relation`), as `{:net … :support {}}`, or nil when it gives none."
  [nodes]
  (let [ts  (vec (remove symbol? nodes))
        net (reduce (fn [m [a b]]
                      (if-let [r (cal/relation a b)]
                        (assoc m [a b] #{r} [b a] #{(allen-converse r)})
                        m))
                    {}
                    (for [i (range (count ts)) j (range (inc i) (count ts))] [(ts i) (ts j)]))]
    (when (seq net) {:net net :support {}})))

(defn- points-narrowing-with-support
  "What the point network determines about the interval relations, as
  `{:net {[i j] → #{base relations}} :support {[i j] → #{handle}}}`, over each thing X whose
  `(StartFn X)` is a node, X a `node?`, or whose stated `startOf` and `endOf` name two symbol
  nodes (`stp/intervals-with-endpoints`), which then stand for its points beside its point
  terms and support its pairs.  An endpoint comparison intersects every reading of the two
  endpoints; a pair's relations are those whose `stp/endpoint-signature` the four admit,
  supported by their support, and only narrowed pairs are recorded.  Each unsatisfiable
  component (`qcn-kb/unsatisfiable-components`) answers `stp/unsatisfiable-narrowing` over
  the things whose points it holds, supported by its culprits, its `:point` source naming
  them and its pairs as written.  The comparisons are read off `qcn-kb/closed-network` and
  the support off one `qcn-kb/closure-with-support` pass."
  [kb context]
  (let [calc    pt/instants
        net     (qkb/network kb calc context)
        on-net  (qkb/nodes net)
        pointed (into #{} (comp (keep tp/thing-of) (filter node?)) on-net)
        stated  (into {} (filter (fn [[_ [[s e]]]] (and (on-net s) (on-net e))))
                      (stp/intervals-with-endpoints kb context (filter symbol? on-net)))
        things  (into pointed (keys stated))
        bad     (qkb/unsatisfiable-components calc kb context)
        gone    (into #{} (mapcat :nodes) bad)
        closed  (qkb/closed-network calc kb context)
        pass    (delay (qkb/closure-with-support calc kb context))
        ends    (into {} (map (fn [x] (let [[s e] (get-in stated [x 0])
                                            own   (pointed x)]
                                        [x {:start (cond-> [] own (conj (tp/point :start x)) s (conj s))
                                            :end   (cond-> [] own (conj (tp/point :end x)) e (conj e))}])))
                      things)
        nodes-of (fn [x] (mapcat val (ends x)))
        free    (into #{} (remove (fn [x] (some #(contains? gone %) (nodes-of x)))) things)
        between (fn [x y] (for [ex [:start :end] ey [:start :end]]
                            [[ex ey] (for [a (get-in ends [x ex]) b (get-in ends [y ey])] [a b])]))
        stand-ins (for [{:keys [nodes pairs culprits]} bad]
                    (stp/unsatisfiable-narrowing
                     (filter (fn [x] (some #(contains? nodes %) (nodes-of x))) things)
                     culprits
                     {:source  :point
                      :pairs   (nm/by-print-key pairs)
                      :support culprits}))]
    (stp/merge-narrowings
     (cons
      (when (map? closed)
        (reduce
         (fn [acc [x y]]
           (let [pts  (between x y)
                 cmp  (into {} (map (fn [[k abs]]
                                      [k (reduce set/intersection
                                                 (map (fn [[a b]] (qkb/constraint calc closed a b)) abs))]))
                            pts)
                 rels (into #{} (keep (fn [[rel sig]]
                                        (when (every? (fn [[k r]] (contains? (cmp k) r)) sig)
                                          rel)))
                            stp/endpoint-signature)]
             (if (= rels stp/allen-relations)
               acc
               (let [support (:support @pass)]
                 (-> acc
                     (assoc-in [:net [x y]] rels)
                     (assoc-in [:support [x y]]
                               (-> #{}
                                   (into (mapcat (fn [[_ abs]] (mapcat #(get support % #{}) abs))) pts)
                                   (into (get-in stated [x 1]))
                                   (into (get-in stated [y 1])))))))))
         {:net {} :support {}}
         (for [x free y free :when (not= x y)] [x y])))
      stand-ins))))

(defn- both-narrowings
  "The metric and the point readings merged (`stp/merge-narrowings`), their unsatisfiable
  sources listed metric first."
  [kb context]
  (stp/merge-narrowings [(stp/allen-narrowing-with-support kb context)
                         (points-narrowing-with-support kb context)]))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def allen
  "Allen's interval algebra as a `vaelii.impl.qcn-kb` calculus over `node?`'s terms,
  narrowed by `both-narrowings` (`:sources` and `:contexts`: docs/stp.md) and by
  `calendar-relations` over its nodes and a goal's.  `subintervalOf` and
  `properSubintervalOf` are typed: the network answers them only over arguments their
  declared types admit."
  (qkb/calculus :allen allen-algebra stp/interval-denotation
                {:fn         both-narrowings
                 :over-nodes calendar-relations
                 :node?      node?
                 :bindings stp/allen-narrowing-bindings
                 :sources  (into stp/allen-narrowing-sources (keys pt/instant-denotation))
                 :contexts (-> stp/network-predicates
                               (into stp/endpoint-predicates)
                               (into (keys pt/instant-denotation)))}
                '#{subintervalOf properSubintervalOf}))

(defn possible-allen-relations
  "The Allen base relations still possible between intervals `i1` and `i2` given
  everything believed in `context` — `#{}` when either lies in an unsatisfiable component."
  [kb context i1 i2]
  (qkb/possible allen kb context i1 i2))

(defn allen-support
  "The handles of the stored sentexes the relation set between `i1` and `i2` rests on —
  `possible-allen-relations`' support (`qcn-kb/support`), `#{}` for an unconstrained
  pair."
  [kb context i1 i2]
  (qkb/support allen kb context i1 i2))

(defn allen-predicates
  "Every predicate the Allen calculus reads: the sources a `SupportingProver` whose
  answer depends on the interval network names."
  []
  (:predicates allen))

(defn allen-prover
  "The interval-algebra entailment prover, to register with `vaelii.core/add-prover`.  It
  estimates an open goal at `provers/deferred-est`, so a conjunction runs the goal after
  the conjunct binding its variable: the calendar orders a calendar term no node is, which
  the open enumeration of the nodes leaves out (docs/time.md, \"The points of a temporal
  thing\")."
  []
  (qkb/prover allen provers/deferred-est))
