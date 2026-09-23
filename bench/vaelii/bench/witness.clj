;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.witness
  "How many stored firings rest on a reachability witness that placed them lower than
  another route would have, and how many a reader loses while still reaching, printed per
  corpus.  The counts and the two generated corpora are `vaelii.witness-reading`, which
  `witness_shortfall_test` also reads, so the bench and the test cannot report different
  numbers; what each count means is that namespace's docstring.

  Run: `lein bench-witness [starter|world|generated|generated-fact|generated-short-first|generated-fact-short-first|generated-defeated|generated-fact-defeated|lattice|lattice-short-first|all]`"
  (:require [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.witness-reading :as wr]
            [vaelii.world :as world]))

;; ---- the corpora ---------------------------------------------------------

(defn- fresh [space] (v/open-kb {:backend :memory :space space}))

(defn- literal
  "The `term` the generated corpora take, spelling each name as written."
  [_role base]
  (symbol base))

(def ^:private lattice-base
  '[[(genl chi thing) CxUniverse]
    [(genl mid thing) CxUniverse]
    [(genl dog thing) CxUniverse]
    [(genl cat thing) CxUniverse]
    [(genlCx CxA CxUniverse) CxUniverse]
    [(genlCx CxB CxA) CxUniverse]
    [(largerThan dog cat) CxUniverse]
    [(transitiveInArg largerThan 1 genl) CxUniverse]
    [(set/forwardRule (implies (largerThan ?x ?y) (noted ?x ?y))) CxUniverse]])

(def ^:private lattice-long '[[(genl mid dog) CxUniverse] [(genl chi mid) CxUniverse]])
(def ^:private lattice-short '[[(genl chi dog) CxA]])

(defn- lattice
  "The two-route lattice of docs/nmtms.md, \"Where the layer stops\": a long route stated
  in CxUniverse, a short one in CxA named as the witness, and CxB monotonically denying
  the short one.  `order` decides which route is asserted first, which is what the two
  arms compare."
  [kb order]
  (doseq [[s c] (concat lattice-base
                        (if (= :long-first order)
                          (concat lattice-long lattice-short)
                          (concat lattice-short lattice-long)))]
    (v/assert kb s c))
  (v/assert kb '(not (genl chi dog)) 'CxB {:strength :monotonic})
  kb)

;; ---- the report ----------------------------------------------------------

(defn- row [kind {:keys [named binding above lost silent]}]
  (println (format "  %-22s %8d %9d %8d %7d %8d"
                   (str kind) (or named 0) (or binding 0) (or above 0) (or lost 0) (or silent 0))))

(defn- run-corpus [label build]
  (println)
  (println (str "=== " label))
  (let [kb (build)
        r  (wr/report kb)]
    (println (format "  %-22s %8s %9s %8s %7s %8s"
                     "witness" "named" "binding" "above" "lost" "silent"))
    (doseq [[kind counts] (sort-by (comp str key) r)] (row kind counts))
    (when (empty? r) (println "  (no justification names a reachability witness)"))
    (let [{:keys [shadowed redundant]} (wr/shadowed kb)]
      (println (format "  stored below the same sentence: %d, of which the same firing over another route: %d"
                       shadowed redundant)))
    (println (format "  sentexes %,d   justifications %,d   contexts %,d"
                     (count (v/handles kb))
                     (count (jtms/justifications (reasoning/tms kb)))
                     (count (tax/contexts (reasoning/taxonomy kb)))))
    r))

(def ^:private corpora
  {"starter"   #(doto (fresh 7101) starter/load-into)
   "world"     #(doto (fresh 7102) starter/load-into world/load-into)
   "generated" #(wr/generated (fresh 7103) literal 12 5)
   "generated-fact" #(wr/generated-fact (fresh 7106) literal 12 5)
   "generated-short-first" #(wr/generated (fresh 7107) literal 12 5 {:short-first? true})
   "generated-defeated" #(wr/generated (fresh 7109) literal 12 5 {:defeated? true})
   "generated-fact-defeated" #(wr/generated-fact (fresh 7110) literal 12 5 {:defeated? true})
   "generated-fact-short-first" #(wr/generated-fact (fresh 7108) literal 12 5 {:short-first? true})
   "lattice"   #(lattice (fresh 7104) :long-first)
   "lattice-short-first" #(lattice (fresh 7105) :short-first)})

(defn -main [& args]
  (let [which (or (first args) "all")
        names (if (= "all" which) ["starter" "world" "generated" "generated-fact" "generated-short-first"
                                    "generated-fact-short-first" "generated-defeated"
                                    "generated-fact-defeated" "lattice"
                                    "lattice-short-first"] [which])]
    (doseq [n names]
      (if-let [build (get corpora n)]
        (run-corpus n build)
        (println "unknown corpus:" n)))
    (shutdown-agents)))
