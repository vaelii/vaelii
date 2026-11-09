;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.nat-maintenance
  "The reified-NAT maintenance the write paths run once their own work is done:
  `reconcile-assert` after a sentence is stored, `reconcile-revivals!`,
  `collect-orphans!` and `reconcile-formula-positions` after a teardown.  Requires `nat`, `context-nat`, `chain`, `resolution`, `settle` and `special`; the
  teardown entry point `retract!` is an argument, since the engine never requires
  `vaelii.core`.  See docs/nat.md and docs/context-nat.md."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.context-nat :as context-nat]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]))

;; ---- computed genlCx edges: the merges they license -----------------------

(def ^:private max-producer-rounds
  "How many settles' belief moves `settle-computed-edges` reconciles before it logs
  `::producer-rounds` and leaves the last settle's moves unread."
  8)

(defn- settle-computed-edges
  "Settle once when a computed `genlCx` edge was built (`built?`), seeding no chaining
  when `opts` holds `{:chain? false}`: the producer runs after the write that entails the
  edge has settled.  The belief moves that settle makes are reconciled and settled in turn
  (`context-nat/reconcile-moves`), for at most `max-producer-rounds` settles."
  [kb built? opts]
  (loop [built? built? n 0]
    (when built?
      (settle/settle-write kb (:chain? opts true))
      (if (< n max-producer-rounds)
        (recur (context-nat/reconcile-moves kb (special/take-producer-moves!)) (inc n))
        (trove/log! {:level :warn :id ::producer-rounds
                     :msg  (str "structural genlCx reconciliation built an edge in each of "
                                max-producer-rounds " rounds; the last settle's moves are not read")
                     :data {:rounds n}}))))
  nil)

;; ---- the assert path ------------------------------------------------------

(defn- respell-corresponded!
  "Re-spell the rules naming an open application of each function a correspondence
  declaration among `sentences` names, as the declarations believed now read them
  (`chain/reconcile-reified!`, docs/nat.md, The corresponding predicate), then re-chain
  what that made and settle.  `departed?` says the declarations left, so their
  predicates' rules are read too."
  [kb sentences departed?]
  (let [decls (into [] (comp (filter #(and (seq? %) (= res/correspondence-predicate (first %))
                                           (symbol? (second %)) (symbol? (nth % 2 nil))))
                             (distinct))
                    sentences)]
    (when (and (seq decls) (nat-read/any-reifiable-functions? kb))
      (let [new (chain/reconcile-reified! kb (sort (distinct (map second decls)))
                                          (when departed? (map #(nth % 2) decls)))]
        (when (seq new) (settle/rechain-seeds kb new))
        (settle/settle kb)))))

(defn- reconcile-values!
  "Queue the constants whose correspondence derivations the stored or removed
  `sentences` move (`nat-read/note-values`, with the constants a sentence names when
  `uses?`), and settle, which drains them (`chain/sync-values!`, docs/nat.md, The
  corresponding predicate).  `seed?` is the write's `:chain?`."
  [kb sentences uses? seed?]
  (when (nat-read/note-values kb sentences uses?)
    (settle/settle-write kb seed?)))

(defn reconcile-formula-positions
  "Re-decide the hold of the rules a `formula` position moved by the stored or removed
  `sentences` decides (`nat/formula-declared-predicates`,
  `chain/reconcile-formula-positions!`, docs/nat.md, The corresponding predicate), then
  re-chain what that made, settle, and build the structural `genlCx` edges the settle's
  belief moves call for (`settle-computed-edges`)."
  [kb sentences]
  (when-let [preds (seq (nat/formula-declared-predicates kb sentences))]
    (when-let [new (chain/reconcile-formula-positions! kb preds)]
      (when (seq new) (settle/rechain-seeds kb new))
      (settle/settle kb)
      (when (nat/any-reified-constants? kb)
        (settle-computed-edges kb (context-nat/reconcile-moves kb (special/take-producer-moves!)) nil)))))

(defn reconcile-assert
  "The reified-NAT maintenance a just-stored `sentence` calls for, run after its own
  chaining has settled: `nat/reconcile-nats!`, the correspondence derivations it moves
  (`reconcile-values!`), the rules a correspondence declaration respells
  (`respell-corresponded!`), then the structural `genlCx` edges
  `context-nat/reconcile-genlCx` builds, settled, when constants or rewrite rows are stored;
  and on every KB the rules a `formula` position it moves holds or releases
  (`reconcile-formula-positions`).  `opts` is the assert's; the stored context is not
  read."
  [kb sentence _context opts]
  (when (sequential? sentence)
    (when (or (nat/any-reified-constants? kb) (nat-read/named-values-reachable? kb))
      (nat/reconcile-nats! kb sentence)
      (reconcile-values! kb [sentence] true (:chain? opts true))
      (respell-corresponded! kb [sentence] false)
      (settle-computed-edges kb (context-nat/reconcile-genlCx kb sentence (special/take-producer-moves!))
                             opts))
    (reconcile-formula-positions kb [sentence])))

;; ---- the teardown path ----------------------------------------------------

(defn reconcile-revivals!
  "Rebuild the structural `genlCx` edges the belief moves of a teardown and its removed
  sentexes (`sink`) call for, and settle what it built (`context-nat/reconcile-revivals`,
  docs/context-nat.md)."
  [kb sink]
  (settle-computed-edges
   kb (context-nat/reconcile-revivals kb (special/take-producer-moves!) (map :sentence @sink)) nil))

(defn reconcile-moves!
  "Rebuild the structural `genlCx` edges the belief moves a settle recorded call for
  (`context-nat/reconcile-moves`), and settle what it built: the close of a deferred
  batch, whose writes settled nothing."
  [kb]
  (settle-computed-edges kb (context-nat/reconcile-moves kb (special/take-producer-moves!)) nil))

(def ^:dynamic ^:private *in-orphan-removal?*
  "Bound true while `remove-orphaned-nats!` retracts orphaned reified NAT bookkeeping, so
  the nested retractions do not re-enter the sweep."
  false)

(defn- remove-orphaned-nats!
  "Retract the bookkeeping of every reified constant that is an orphan, to a fixpoint
  (docs/nat.md, Rename and remove).  `sink` is the teardown's removal record
  (`integrate/*removed-sink*`): each round's candidates are the constants the sentexes
  removed since the last round named, and this round's retractions append to it.  A nil
  `sink` asks the whole KB each round.  `retract!` takes each handle out.  At most 64
  rounds."
  [kb sink retract!]
  (binding [*in-orphan-removal?* true]
    (loop [mark 0 guard 0]
      (let [removed (when sink @sink)
            orphans (if sink
                      (nat/orphans-named-by kb (subvec removed mark))
                      (nat/orphaned-constants kb))
            ;; realized before the first retraction: the bookkeeping test reads the
            ;; bookkeeping this loop retracts
            handles (vec (distinct (mapcat #(nat/bookkeeping-handles kb %) orphans)))]
        (when (and (seq handles) (< guard 64))
          (doseq [h handles] (retract! kb h))
          (recur (count removed) (inc guard)))))))

(defn- respell-stranded!
  "Re-spell the uses of each object constant whose `natFormula` map is in the removal
  record `sink` and that uses still name (`chain/reconcile-stranded!`), then re-chain
  what that made and settle.  One pass over `sink`."
  [kb sink]
  (let [maps (into [] (comp (keep #(nat/departed-map (:sentence %))) (distinct)) @sink)]
    (when-let [new (and (seq maps) (chain/reconcile-stranded! kb maps))]
      (when (seq new) (settle/rechain-seeds kb new))
      (settle/settle kb))))

(defn collect-orphans!
  "Re-spell the uses a removed `natFormula` map left naming its constant
  (`respell-stranded!`) and the rules a removed correspondence declaration respelled
  (`respell-corresponded!`), re-derive the values a removed declaration or corresponding
  fact moves (`reconcile-values!`), then collect the reified constants a teardown orphaned
  (docs/nat.md, Rename and remove).  `retract!` and `edit!`, and the rollback of a single
  refused `assert`, pass their removal record `sink`; `rollback-batch!` passes none, and
  the sweep asks the whole KB.  The sweep runs only when `nat/any-reified-constants?`
  holds.  Neither runs inside the sweep's own retractions."
  ([kb retract!] (collect-orphans! kb nil retract!))
  ([kb sink retract!]
   (when-not *in-orphan-removal?*
     (when sink
       (respell-stranded! kb sink)
       (respell-corresponded! kb (map :sentence @sink) true)
       (reconcile-values! kb (map :sentence @sink) false true))
     (when (nat/any-reified-constants? kb)
       (remove-orphaned-nats! kb sink retract!)))))
