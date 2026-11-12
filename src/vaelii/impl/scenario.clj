;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.scenario
  "Scenario extraction over a qualitative constraint network: `scenarios` (lazy, with a
  `:limit`), `scenario` and `relations` choose one base relation per pair for any
  `vaelii.impl.qcn-kb` calculus, by fewest-possibilities-first backtracking with path
  consistency after each choice.  Every tie breaks on content.  See docs/scenario.md."
  (:require [vaelii.impl.naming :as nm]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.resolution :as res]))

;; ---- the deterministic orderings ----------------------------------------

(defn- node-order
  "Every node of `net`, ordered by how it is written.  Content-keyed, so it is the same
  order in any KB holding the same facts.

  Printed through `nm/print-key`, never a bare `str`: `qkb/nodes` answers with a **set**,
  and a node can be a compound term, so under an ambient `*print-length*` two nested
  nodes print to one prefix, the key collapses and the order falls back to that set's
  iteration order — which decides `node-pairs`, which pair the search commits to first,
  and therefore *which* scenario is returned."
  [net]
  (nm/sort-by-content-key nm/print-key compare (qkb/nodes net)))

(defn- node-pairs
  "Every unordered pair of nodes, each written once in node order.  A scenario decides all
  of them — including the pairs no fact reaches, which are as much a part of an arrangement
  as the ones that were stated."
  [node-vec]
  (let [n (count node-vec)]
    (for [a (range n) b (range (inc a) n)]
      [(nth node-vec a) (nth node-vec b)])))

(defn- relation-order
  "A constraint's relations, ordered by how they are named — the order the search tries
  them in, and the reason two runs agree on *which* scenario they return."
  [rels]
  ;; relations are unqualified keywords, so a bare sort orders them by name identically
  ;; to a printed key — without an allocation per comparison on this per-branch call
  (sort rels))

(defn- next-pair
  "The still-undecided pair with the fewest possibilities, or nil when every pair is down to
  one and the network *is* a scenario.

  Fewest-first is the standard heuristic and it is also what keeps the answer stable: ties
  are resolved by node order, since the fold keeps the earliest candidate of any given size."
  [calc net prs]
  (reduce (fn [best [i j :as pair]]
            (let [n (count (qkb/constraint calc net i j))]
              (if (and (> n 1) (or (nil? best) (< n (:size best))))
                {:pair pair :size n}
                best)))
          nil
          prs))

;; ---- the search ----------------------------------------------------------

(defn- assign
  "Narrow `pair` to the single relation `rel`, writing the converse on the reversed pair so the
  network stays readable in both directions — the invariant `qcn` maintains."
  [net algebra [i j] rel]
  (assoc net [i j] #{rel} [j i] ((:converse algebra) #{rel})))

(defn- determined
  "The network as an explicit scenario: every pair a singleton, both directions written,
  including the pairs the search never had to decide because tightening determined them."
  [calc net prs]
  (let [converse (:converse (:algebra calc))]
    (into {}
          (mapcat (fn [[i j]]
                    (let [r (qkb/constraint calc net i j)]
                      [[[i j] r] [[j i] (converse r)]])))
          prs)))

(defn- search
  "Every scenario extending `net`, lazily.  Pick the most constrained undecided pair, try
  each of its relations in name order, re-tighten, and recurse; a choice that empties any
  constraint is abandoned there.

  `res/lazy-mapcat` rather than `mapcat`: each branch is a whole subtree, and chunked
  `map` would expand every one of them before yielding the first scenario — which is the
  entire cost this is written to avoid."
  [calc net node-vec prs]
  (let [algebra (:algebra calc)]
    (if-let [{:keys [pair]} (next-pair calc net prs)]
      (res/lazy-mapcat
       (fn [rel]
         (let [pc (qcn/path-consistent (assign net algebra pair rel) node-vec algebra)]
           (when-not (= :inconsistent pc)
             (search calc pc node-vec prs))))
       (relation-order (qkb/constraint calc net (first pair) (second pair))))
      (list (determined calc net prs)))))

;; ---- the public shape ----------------------------------------------------

(defn scenarios
  "Every scenario of `calc` consistent with what is believed in `context`, as a **lazy**
  sequence of singleton-valued networks `{[i j] → #{relation}}`, both directions written.

  Lazy on purpose: the number of scenarios is exponential in the node count, so realizing
  the sequence in full is not something a caller should do by accident.  Take what you need,
  or pass `{:limit n}` and let this do the taking.

  Empty when the believed facts are unsatisfiable — an arrangement nothing rules out cannot
  exist when everything is ruled out.  A context with fewer than two nodes has exactly one
  scenario, the empty one, since there is no pair to decide."
  ([calc kb context] (scenarios calc kb context nil))
  ([calc kb context {:keys [limit]}]
   (let [net      (qkb/network kb calc context)
         node-vec (node-order net)
         pc       (qkb/tighten kb calc context net nil)]
     (when-not (= :inconsistent pc)
       (cond->> (search calc pc node-vec (node-pairs node-vec))
         limit (take limit))))))

(defn scenario
  "One scenario of `calc` consistent with what is believed in `context` — a concrete
  arrangement of every pair — or nil when the believed facts are unsatisfiable.

  Which one is a function of the facts alone: the search is deterministic, so this is
  repeatable and comparable across KBs."
  [calc kb context]
  (first (scenarios calc kb context {:limit 1})))

(defn relations
  "A scenario read as `{[i j] → relation}`, the singletons unwrapped.  The network form is
  what composes with `qcn`; this is what reads."
  [scen]
  (into {} (map (fn [[pair rels]] [pair (first rels)])) scen))
