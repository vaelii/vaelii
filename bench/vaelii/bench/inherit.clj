;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.inherit
  "What one **argument-position preservation** question costs.

  `(transitiveInArg P n R)` says a stored `(P … w …)` licenses the same claim about
  anything `R`-related to `w`, so answering a ground `(P a b)` means asking which
  claims *reach* this tuple.  The number that matters is how that cost scales with the
  two things it could scale with: the **reach** of each preserved argument (how deep
  the hierarchy is), and how many **claims** were actually written.  A cost model
  driven by the first is a taxonomy tax paid on every query; one driven by the second
  is the quantity the answer depends on.

  So the harness sizes a chain, declares preservation on 1, 2 or 3 argument positions
  of predicates of matching arity, and asks a ground goal:

    ask?     the whole prover path, which is what a caller pays
    verdict  the same question without the registry around it
    claims   the claims bearing on the goal — the raw material the other two read

  A gap between `claims` and `verdict` is undercutting rather than retrieval.  A
  `positions` and a `witness-terms` row sit under all three, since every layer calls
  both repeatedly.

  Run: `lein bench-inherit [--depth n] [--samples n] [--claims n] [--branching b]`"
  (:require [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.types.prover :as prover-types]))

(def ^:private defaults
  {:depth     8      ; the genl chain each preserved argument walks
   :branching 1      ; 1 is a chain — the structure that makes a reach long
   :claims    1      ; stored (P …) claims per predicate
   :samples   2000})

(defmacro ^:private timed [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (- (System/nanoTime) t0#)]))

(defn- type-name [i] (symbol (str "bi" i "_t")))
(defn- pred-name [k] (symbol (str "biP" k "Of")))   ; k = preserved positions

(def ^:private ctx 'CxInheritBench)

(defn- build!
  "For each arity k in 1..3, a predicate of arity k with all k positions preserved
  along `genl`, and `claims` stored claims at the **most general** end of the chain —
  so a goal at the specific end has to walk the whole reach to find them."
  [kb {:keys [depth branching claims]}]
  (v/assert kb (list 'genlCx ctx 'CxCore) 'CxCore {:chain? false})
  (v/with-deferred-settle kb
    (doseq [i (range depth)]
      (v/assert kb (list 'genl (type-name i)
                         (if (zero? i) 'thing (type-name (quot (dec i) branching))))
                ctx {:chain? false}))
    (doseq [k [1 2 3]]
      (let [p (pred-name k)]
        (doseq [n (range 1 (inc k))]
          (v/assert kb (list 'transitiveInArg p n 'genl) ctx {:chain? false}))
        ;; the claims sit at the general end (index 0 is nearest `thing`)
        (doseq [c (range claims)]
          (v/assert kb (cons p (repeat k (type-name (min c (dec depth))))) ctx
                    {:chain? false})))))
  ctx)

(defn- goals
  "One ground goal per arity, stated at the **specific** end of the chain."
  [{:keys [depth]}]
  (into {} (for [k [1 2 3]]
             [k (cons (pred-name k) (repeat k (type-name (dec depth))))])))

(defn- run-arm [label f n]
  (dotimes [_ (max 1 (quot n 10))] (f))
  (let [[_ ns] (timed (dotimes [_ n] (f)))
        per    (double (/ ns n))]
    (println (format "  %-20s %10.3f ms/call  %,12.0f calls/s"
                     label (/ per 1e6) (/ 1e9 per)))
    per))

(defn- run [{:keys [depth samples] :as opts}]
  (let [kb (v/open-kb {:recover? false})
        _  (v/clear! kb)
        [_ build-ns] (timed (build! kb opts))
        gs (goals opts)]
    (println (format "\nbuilt %,d sentexes in %.1f s — a %d-deep genl chain, %d claim(s)/predicate\n"
                     (long (v/sentex-count kb)) (/ build-ns 1e9)
                     (long depth) (long (:claims opts))))
    (println (format "the reach of one preserved argument is %d terms, so k positions enumerate %d^k tuples"
                     (long depth) (long depth)))
    (println "\nthe primitives every layer calls")
    (let [g (gs 1)]
      (run-arm "positions" #(doall (inherit/positions kb (first g) ctx)) samples)
      (run-arm "witness-terms" #(inherit/witness-terms
                                 kb {:rel 'genl :inverse? false} (second g) ctx)
               samples))
    (doseq [k [1 2 3]]
      (let [g (gs k)
            n (max 20 (quot samples (long (Math/pow depth (dec k)))))]
        (println (format "\n%d preserved position(s) — %,d candidate tuples, goal %s"
                         k (long (Math/pow depth k)) (pr-str g)))
        (run-arm "claims" #(count (inherit/claims kb g ctx)) n)
        (run-arm "verdict" #(inherit/verdict kb g ctx) n)
        (run-arm "ask?" #(v/ask? kb g ctx) n)))
    ;; the control: a predicate declaring nothing must pay none of this
    (println "\nthe control — a predicate with no preserved position")
    (run-arm "ask? (no decl)" #(v/ask? kb (list 'bq_unrelated_of (type-name 0)) ctx) samples)
    (println (format "\nest-bindings reports %s for the 3-position goal"
                     (prover-types/est-bindings (provers/->TransitiveInArgProver) kb (gs 3) ctx)))
    (println)))

(defn- parse-args [args]
  (reduce (fn [m [k v]] (assoc m (keyword (subs k 2)) (Long/parseLong v)))
          defaults
          (partition 2 args)))

(defn -main [& args]
  (run (parse-args args))
  (shutdown-agents)
  (System/exit 0))
