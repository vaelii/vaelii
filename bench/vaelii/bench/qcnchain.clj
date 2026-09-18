;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.qcnchain
  "What a forward rule over a qualitative antecedent costs at **load** time — the other
  half of `vaelii.bench.qcn`, which sizes one path-consistency pass in isolation.

  Four columns, because the cost appears only when a calculus prover is registered *and* a
  forward rule mentions one of its predicates. Registering a prover alone changes nothing:
  a calculus's facts are then ordinary facts, matched and chained as they always were. The
  moment a rule joins on one of its predicates, every arriving fact of that calculus
  re-joins that rule — over the pairs whose entailment that fact moved, not over every pair
  the network entails.

    no prover           the floor: the same facts with nothing qualitative running
    prover, no rule     registration alone, which should track the floor
    prover + rule       the real cost
    deferred chaining   the same, asserted `{:chain? false}` with one `forward-chain`
                        at the end — the identical conclusions, one big datum

  The shape is a containment chain of *n* regions, which is what makes every pair compose.

  Run: `lein bench-qcnchain`"
  (:require [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.space :as space]))

(defn- fresh-kb
  "A KB with the spatial vocabulary and nothing else.  The in-memory stores are shared per
  space number, so a new handle over the same numbers would see the previous scenario's
  facts — `clear!` is what makes each row independent rather than cumulative."
  []
  (let [kb (v/open-kb {:backend :memory :space 30 :recover? false})]
    (v/clear! kb)
    (core-context/load-into kb)
    (seed/load-context kb 'CxSpace "upper")
    kb))

(defn- ms [f] (let [t (System/nanoTime)] (f) (/ (- (System/nanoTime) t) 1e6)))

(defn- scenario
  "Load `n` regions in the given `shape` and return the milliseconds it took.  `:chain` is
  a containment chain — every pair composes, the dense worst case; `:tree` is the
  branching-3 containment tree `bench-qcn` calls the realistic one, where only pairs
  sharing an ancestor line compose."
  [shape n prover? rule? defer?]
  (let [kb     (fresh-kb)
        ctx    'CxUniverse
        node   #(symbol (str "Reg" % "Node"))
        parent (if (= :tree shape) #(quot (dec %) 3) dec)
        opts   (when defer? {:chain? false})]
    (when prover? (v/add-prover kb (space/spatial-prover)))
    (when rule?
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list 'contained '?x) ctx
                     {:direction :forward}))
    (cond-> (ms #(doseq [i (range 1 n)]
                   (v/assert kb (list 'nonTangentialProperPart (node i) (node (parent i)))
                             ctx opts)))
      defer? (+ (ms #(v/forward-chain kb {}))))))

(defn- best
  "The fastest of two timed runs after a warm one — same discipline as `bench-qcn`."
  [f]
  (f)
  (min (f) (f)))

(defn -main [& args]
  (let [sizes (if (seq args) (map #(Long/parseLong %) args) [10 20 40])]
    (println "vaelii qualitative forward-chaining load cost")
    (println "wall-clock, fastest of two after a warm run — read the ratios, not the values.\n")
    (doseq [shape [:chain :tree]]
      (println (str "  " (name shape) ": "
                    (if (= :tree shape)
                      "a branching-3 containment tree — only pairs sharing an ancestor"
                      "a containment chain — every pair composes, the dense worst case")))
      (println "  regions | no prover | prover, no rule | prover + rule | deferred chaining")
      (println "  --------------------------------------------------------------------------")
      (doseq [n sizes]
        (println (format "  %7d | %9.1f | %15.1f | %13.1f | %17.1f"
                         n
                         (best #(scenario shape n false false false))
                         (best #(scenario shape n true false false))
                         (best #(scenario shape n true true false))
                         (best #(scenario shape n true true true)))))
      (println))
    (println "  Reading:")
    (println "  - three things sit behind the prover+rule column. The network is RESIDENT")
    (println "    on the KB and stamped with the change clock, so it is read out once and")
    (println "    reused until the engine mutates. The pass WARM-STARTS off its own")
    (println "    previous answer whenever the new network narrows the old, which is what")
    (println "    every arriving fact does. And the re-join is SEMI-NAIVE: a rule is joined")
    (println "    over the pairs whose entailment the arriving fact moved, not over every")
    (println "    pair the network entails.")
    (println "  - what is left is the SUPPORT-carrying pass, the one that cannot warm-start")
    (println "    — a kept support would make a firing's antecedents depend on arrival")
    (println "    order — so it runs whole once per arriving fact. Computing support for")
    (println "    the pairs a join asks about, rather than for the network, is the next")
    (println "    thing here, and it is a different algorithm rather than a cache.")
    (shutdown-agents)))
