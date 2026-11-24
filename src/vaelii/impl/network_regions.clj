;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.network-regions
  "The conflicted regions of the calculus, metric and sign networks, each placed at the
  write as one `(contradicts …)` over its facts with no `defeat` (`chain/place-nogood!`).
  The ledger entry, the feed's entry and `try-assert`'s refusal read that stored sentence.
  See docs/qcn.md, \"An impossible network is a stored contradiction\"."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.region :as region]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.point :as pt]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.sign :as sign]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

;; ---- the networks ---------------------------------------------------------

(def ^:private ground-functors
  "The functors of the support a region rests on without naming it as a member: the edges
  a network read passes through and the unit table a measure converts through."
  (into '#{genl genlCx} provers/unit-table-predicates))

(defn- with-pairs
  "`detail` with the pairs unsatisfiable as written, when there are any."
  [detail pairs]
  (cond-> detail (seq pairs) (assoc :pairs (nm/by-print-key pairs))))

(defn- calculus-network
  "The network of the calculus `calc`: the point algebra's regions are strongly connected
  components (`pt/unsatisfiable-regions`), every other calculus's are connected
  components (`qkb/unsatisfiable-regions`)."
  [calc]
  (let [nm (:name calc)]
    {:name      nm
     :files     :qualitative-inconsistency
     :triggers  (:trigger-predicates calc)
     :own       (:predicates calc)
     :node?     (:node? calc)
     :regions   (if (= :point nm)
                  pt/unsatisfiable-regions
                  #(qkb/unsatisfiable-regions calc %1 %2 %3))
     :entry     (fn [r ctx]
                  {:calculus nm
                   :detail   (cond-> (with-pairs
                                       {:message (str "the " (name nm) " network visible from "
                                                      ctx " is unsatisfiable, so no goal naming"
                                                      " a node of an unsatisfiable component"
                                                      " is answered there")
                                        ;; a node may be a NAT and a pair always is a
                                        ;; vector, so both are keyed through the guarded
                                        ;; printer
                                        :nodes   (nm/by-print-key (:nodes r))}
                                       (:pairs r))
                               (seq (:sources r)) (assoc :sources (:sources r)))})}))

(def ^:private metric-network
  {:name      :metric
   :files     :metric-temporal-inconsistency
   :triggers  (into stp/network-predicates provers/unit-table-predicates)
   :seeds     stp/region-seeds
   :regions   stp/unsatisfiable-regions
   :entry     (fn [r ctx]
                {:detail (cond-> (with-pairs
                                   {:message (str "the temporalDistance constraints visible from "
                                                  ctx " cannot all be satisfied, so no metric"
                                                  " temporal goal is answered there")
                                    :unit    (:unit r)
                                    :nodes   (nm/by-print-key (:nodes r))}
                                   (:pairs r))
                           (seq (:cycle r)) (assoc :cycle (nm/by-print-key (:cycle r))))})})

(def ^:private sign-network
  {:name      :sign
   :files     :sign-inconsistency
   :triggers  sign/sign-sources
   :own       #{}
   :regions   (fn [kb ctx _] (sign/unsatisfiable-regions kb ctx))
   :entry     (fn [r ctx]
                {:detail {:message    (str "the sign facts visible from " ctx " cannot all be"
                                           " satisfied, so no sign goal is answered there")
                          :quantities (nm/by-print-key (:quantities r))}})})

(defn- checked-networks
  "The networks a prover registered on `kb` reads, in name order.  The predicates read are
  the registered calculi's trigger predicates and the supporting provers' sources.  A
  calculus is read when its prover is registered or a read predicate is its own; the
  metric network when `temporalDistance` is read, and the sign network when a sign
  predicate is.  Empty with no such prover."
  [kb]
  (let [cs    (qkb/registered-calculi kb)
        reads (into (into #{} (mapcat :trigger-predicates) cs) (provers/support-source-preds kb))]
    (if (empty? reads)
      []
      (let [named (into #{} (map :name) cs)]
        (sort-by :name
                 (concat (for [c (qkb/built-calculi-values)
                               :when (or (contains? named (:name c)) (some reads (:predicates c)))]
                           (calculus-network c))
                         (when (some reads stp/network-predicates) [metric-network])
                         (when (some reads sign/sign-predicates) [sign-network])))))))

(defn- triggers?
  "Does a fact on `f` move the network `net`: `f` or a predicate it specializes is one of
  its triggers?"
  [tx net f]
  (boolean (and (symbol? f) (some #(contains? (:triggers net) %) (tax/genls-global tx f)))))

(defn- governing
  "The contexts storing a fact on a trigger of `net` or on a predicate specializing one,
  closed under `tax/meet-closure`: every context whose network differs from the
  networks of the contexts it sees through `genlCx`.  Read off the predicate extent's
  children, so the cost is the contexts, not the facts."
  [kb net]
  (let [tx  (reasoning/taxonomy kb)
        idx (:index kb)
        fs  (into #{} (mapcat #(tax/specs-global tx %)) (:triggers net))]
    (tax/meet-closure tx (into #{} (mapcat #(first (reads/as-stored-contexts-with-functor-global idx %))) fs))))

;; ---- what a settle moved --------------------------------------------------

(defn- fact-nodes
  "The nodes the fact `body` names that `net`'s regions are read from: `(:seeds net)`'s
  answer, else the first two arguments of a fact of `net`'s own predicates, or `::all`
  for a fact the network reads some other way."
  [net body]
  (let [[f a b] body]
    (cond
      (:seeds net) (or ((:seeds net) body) ::all)
      (and (contains? (:own net) f) (< 2 (count body)) ((:node? net) a) ((:node? net) b))
      (hash-set a b)
      :else ::all)))

(defn- tasks
  "`{[network context] nodes}`: the networks and governing contexts the handles `hs` move,
  each with the nodes the moving facts name, or `::all`.  A fact moves a network it
  triggers at each governing context that sees its context.  A `genlCx` edge, a `genl` edge
  into a trigger and an `except` hiding a fact move every governing context of the
  networks.  `again` receives the members of each placed `(contradicts …)` among `hs`,
  which the settle reads as moved."
  [kb nets gov hs again]
  (let [tx   (reasoning/taxonomy kb)
        recs (:records kb)
        all  (fn [acc] (reduce (fn [acc net] (reduce #(assoc %1 [net %2] ::all) acc (gov net))) acc nets))
        add  (fn [acc k nodes] (update acc k #(cond (= ::all %) ::all (= ::all nodes) ::all
                                                    :else (into (or % #{}) nodes))))]
    (reduce
     (fn [acc h]
       (let [s (p/get-sentex recs h)
             b (when (and s (nil? (:antecedent s))) (sx/underlying-body (:sentence s)))
             f (when (sequential? b) (first b))]
         (cond
           (not (symbol? f)) acc
           (= 'contradicts f) (do (vswap! again into (keep sx/handle-id) (rest b)) acc)
           (= 'genlCx f)      (reduced (all {}))
           (= 'genl f)        (if (some #(triggers? tx % (nth b 2 nil)) nets) (reduced (all {})) acc)
           (kb/except-target (:sentence s)) (reduced (all {}))
           :else
           (let [c (:context s)]
             (reduce (fn [acc net]
                       (if (triggers? tx net f)
                         (reduce (fn [acc g]
                                   (if (contains? (tax/context-up tx g) c)
                                     (add acc [net g] (fact-nodes net b))
                                     acc))
                                 acc (gov net))
                         acc))
                     acc nets)))))
     {} hs)))

(defn- split-support
  "`[members grounds]` of the handles `hs`: a ground is a `genl` or `genlCx` edge or a
  unit-table row."
  [kb hs]
  (let [recs (:records kb)
        g?   #(contains? ground-functors (some-> (p/get-sentex recs %) :sentence nm/functor))]
    [(into #{} (remove g?) hs) (into #{} (filter g?) hs)]))

(defn- regions-at
  "Every region `(:regions net)` reads at `ctx` over `nodes` (nil for every component), as
  `[members {:net :context :region :grounds}]`."
  [kb net ctx nodes]
  (for [r ((:regions net) kb ctx (when-not (= ::all nodes) nodes))
        :let [[ms gs] (split-support kb (:members r))]
        :when (seq ms)]
    [ms {:net net :context ctx :region r :grounds gs}]))

(defn- members-key
  "The content key of the handle set `hs`: the sentences of its members in content order."
  [kb hs]
  (nm/sort-by-content-key identity (map #(:sentence (p/get-sentex (:records kb) %)) hs)))

(defn- foreign?
  "Is the nogood over `members` one another family places (`decide/placed-kind`)?"
  [kb members]
  (some? (decide/placed-kind kb members)))

(defn- file-entry!
  "File the ledger entry of the placed `(contradicts …)` at `h`, which the region `found`
  holds, and log it at :warn."
  [kb {:keys [net region]} h]
  (let [sx (p/get-sentex (:records kb) h)
        e  (merge {:violation (:files net) :context (:context sx) :sentence (:sentence sx)}
                  ((:entry net) region (:context sx)))]
    (trove/log! {:level :warn :id ::unsatisfiable-region :data e})
    (violations/report-without-run kb e)))

(defn- covering-tasks
  "The `[network context nodes]` triples where the members `ms` can make one region: a
  network a member's functor triggers, at a governing context that sees every member,
  over the nodes the members name (`fact-nodes`)."
  [kb nets gov ms]
  (let [tx   (reasoning/taxonomy kb)
        recs (:records kb)
        sxs  (keep #(p/get-sentex recs %) ms)
        bs   (map #(sx/underlying-body (:sentence %)) sxs)]
    (when (= (count sxs) (count ms))
      (for [net  nets
            :when (some #(triggers? tx net (nm/functor %)) bs)
            g    (gov net)
            :when (let [up (tax/context-up tx g)] (every? #(contains? up (:context %)) sxs))]
        [net g (reduce (fn [acc b] (let [n (fact-nodes net b)]
                                     (if (or (= ::all acc) (= ::all n)) ::all (into acc n))))
                       #{} bs)]))))

(defn place-moved!
  "Place the conflicted regions of the networks the settle moved, and drop each region
  placement that no longer holds.  `region` is a delay of the relabelled handles, forced
  only when a network is registered, and `extra` the members no relabel recorded; the
  members `region/take-left!` returns are read as moved too.  A region is placed with no
  verdict (`chain/place-nogood!`), and a member set another family places is left to it.
  A placement whose members make no region at any context that sees them all is dropped
  (`chain/unplace-nogood!`).  Each placement created files its ledger entry.  Returns true
  when it placed or dropped a placement.  See docs/qcn.md."
  [kb region extra]
  (let [left (region/take-left! kb)
        nets (checked-networks kb)]
    (when (seq nets)
      (let [gov    (memoize #(governing kb %))
            again  (volatile! #{})
            moved  (-> (set @region) (into extra) (into left))
            ts     (tasks kb nets gov moved again)
            ts     (if (seq @again) (merge-with (fn [a b] (if (or (= ::all a) (= ::all b)) ::all (into a b)))
                                                ts (tasks kb nets gov @again (volatile! #{})))
                       ts)
            order  (fn [[net g]] [(:name net) (nm/print-key g)])
            found  (reduce (fn [m [ms f]] (if (contains? m ms) m (assoc m ms f)))
                           {} (for [[k nodes] (sort-by (comp order key) ts)
                                    hit (regions-at kb (first k) (second k) nodes)]
                                hit))
            mine   (into {} (remove (fn [[ms]] (foreign? kb ms))) found)
            made   (into []
                         (mapcat (fn [[ms {:keys [grounds] :as f}]]
                                   (let [hs (chain/place-nogood! kb ms grounds nil {:verdict? false})]
                                     (doseq [h hs] (file-entry! kb f h))
                                     hs)))
                         (nm/sort-by-content-key #(members-key kb (key %)) mine))
            scope  (-> #{} (into (filter #(p/get-sentex (:records kb) %)) moved)
                       (into @again) (into (mapcat key) found))
            stale  (into #{} (comp (mapcat #(chain/placed-member-sets kb %))
                                   (remove #(contains? found %))
                                   (remove #(foreign? kb %)))
                         scope)
            seen   (set (keys ts))
            gone   (into [] (remove (fn [ms]
                                      (some (fn [[net g nodes]] (some #(= ms (first %)) (regions-at kb net g nodes)))
                                            (remove (fn [[net g]] (seen [net g]))
                                                    (covering-tasks kb nets gov ms)))))
                         (nm/sort-by-content-key #(members-key kb %) stale))]
        (doseq [ms gone] (chain/unplace-nogood! kb ms))
        (boolean (or (seq made) (seq gone)))))))

;; ---- reading the stored placements -----------------------------------------

(defn- placement
  "`{:handle :sentence :context :members}` of the believed `(contradicts …)` at `c` when
  it is a region placement of a network `nets` holds: placed under the nogood informant,
  over members no other family places, each on a predicate one of `nets` reads.  nil
  otherwise."
  [kb nets c]
  (let [recs (:records kb)
        tms  (reasoning/tms kb)
        tx   (reasoning/taxonomy kb)
        s    (p/get-sentex recs c)
        ms   (when (and s (= 'contradicts (nm/functor (:sentence s))) (jtms/in? tms c))
               (into #{} (keep sx/handle-id) (rest (:sentence s))))]
    (when (and (seq ms)
               (some #(= chain/nogood-informant (:informant (jtms/justification tms %)))
                     (jtms/supports tms c))
               (every? (fn [m] (let [ms' (p/get-sentex recs m)
                                     f   (some-> ms' :sentence sx/underlying-body nm/functor)]
                                 (some #(triggers? tx % f) nets)))
                       ms)
               (not (foreign? kb ms)))
      {:handle c :sentence (:sentence s) :context (:context s) :members ms})))

(defn- entry-of
  "The ledger entry filed for the placement `pl`, or one naming its sentence and context
  alone when the ledger no longer holds it."
  [kb {:keys [sentence context]}]
  (or (violations/newest-filed kb #(and (= sentence (:sentence %)) (= context (:context %))))
      {:context context :sentence sentence :detail {}}))

(defn write-region
  "The region placement naming a handle of `new` that the write made, the first by its
  members' content key (`members-key`): `{:handle :sentence :context :members :entry}`,
  `:entry` the ledger entry filed for it.  nil when no believed region placement names one."
  [kb new]
  (let [nets (checked-networks kb)
        idx  (:index kb)]
    (when (seq nets)
      (some->> (into #{} (comp (mapcat #(reads/as-stored-with-terms idx [(sx/sentex-handle %)]))
                               (keep #(placement kb nets %)))
                     new)
               (nm/sort-by-content-key #(members-key kb (:members %)))
               first
               (#(assoc % :entry (entry-of kb %)))))))

(defn fed-entries
  "The ledger entries of the region placements among the believed `handles`, by their
  members' content key: what a feed event carries under `:unsatisfiable`."
  [kb handles]
  (let [nets (checked-networks kb)]
    (if (empty? nets)
      []
      (->> (keep #(placement kb nets %) handles)
           (nm/sort-by-content-key #(members-key kb (:members %)))
           (mapv #(entry-of kb %))))))
