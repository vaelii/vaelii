;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.checks
  "What the **definitional checks** cost, per assert.

  Every `assert` runs `vaelii.impl.checks/constraint-problem` before anything is
  stored, and on a bulk load that is where the time goes — a checked corpus load
  spends the majority of its CPU here rather than in the trie, the records, or the
  TMS.  This harness isolates the two dominant arms so a change to either can be
  measured without loading a corpus:

    disjoint-problem  a type membership against the types the term already holds,
                      closed under genl and scoped to the asserting context
    args-problem      a sentence against the `arg` constraints on its predicate,
                      each argument tested with `isa?`

  Both are driven by *hierarchy* rather than by KB size, so the knobs that matter are
  the depth of the genl tree (`--branching` — 2 is deep, 8 is shallow) and how many
  types a term already holds (`--memberships`).  The KB itself is small on purpose:
  these checks never scan it, and a harness that needed a million records to show the
  cost would be measuring something else.

  Run: `lein bench-checks [--types n] [--branching b] [--individuals n]
                          [--memberships m] [--predicates n] [--disjoints n]
                          [--samples n]`"
  (:require [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private defaults
  {:types        4000
   :branching    2        ; deep, the structure that makes a genl closure long
   :individuals  2000
   :memberships  3        ; types each individual already holds
   :predicates   20
   :disjoints    400
   :samples      20000})

(defmacro ^:private timed [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (- (System/nanoTime) t0#)]))

(defn- type-name [i] (symbol (str "bt" i "_t")))
(defn- ind-name [i] (symbol (str "BI" i)))
(defn- pred-name [i] (symbol (str "bp" i "Of")))

(defn- parent-of [branching i] (if (zero? i) 'thing (type-name (quot (dec i) branching))))

(defn- ancestor-chain
  "The chain of type indices from `i` up to the root, `i` first."
  [branching i]
  (take-while some? (iterate (fn [j] (when (pos? j) (quot (dec j) branching))) i)))

(defn- build!
  "A KB shaped like the hierarchy the checks walk: a deep genl tree, individuals
  holding several types apiece from their own ancestor chain (so nothing is disjoint
  and every sample does the full walk rather than short-circuiting on a refusal), and
  binary predicates with `arg` on both positions."
  [kb {:keys [types branching individuals memberships predicates disjoints]}]
  (let [ctx 'CxBench]
    (v/assert kb (list 'genlCx ctx 'CxCore) 'CxCore {:chain? false})
    (v/with-deferred-settle kb
      (doseq [i (range types)]
        (v/assert kb (list 'genl (type-name i) (parent-of branching i)) ctx {:chain? false}))
      ;; disjointness between types in *different* subtrees of the root's children, so
      ;; wff admits the declaration and no individual below one of them holds the other
      (doseq [d (range disjoints)]
        (let [a (+ 1 (* 2 d)) b (+ 2 (* 2 d))]
          (when (and (< a types) (< b types))
            (v/assert kb (list 'disjoint (type-name a) (type-name b)) ctx {:chain? false}))))
      (doseq [i (range predicates)]
        (v/assert kb (list 'arg (pred-name i) 1 (type-name 0)) ctx {:chain? false})
        (v/assert kb (list 'arg (pred-name i) 2 (type-name 0)) ctx {:chain? false}))
      ;; every individual sits on one leaf's ancestor chain and holds `memberships` of
      ;; the types on it — a term with one type exercises none of the walk
      (doseq [i (range individuals)]
        (let [leaf (+ (quot types 2) (mod i (quot types 2)))]
          (doseq [t (take memberships (ancestor-chain branching leaf))]
            (v/assert kb (list (type-name t) (ind-name i)) ctx {:chain? false})))))
    ctx))

(defn- unary-samples
  "`[sentence context]` pairs for the disjointness arm: another type from the same
  individual's own chain, so the check does the whole walk and admits."
  [{:keys [types branching individuals memberships samples]} ctx]
  (into []
        (for [n (range samples)
              :let [i    (mod n individuals)
                    leaf (+ (quot types 2) (mod i (quot types 2)))
                    anc  (vec (ancestor-chain branching leaf))
                    t    (nth anc (min (dec (count anc)) memberships))]]
          [(list (type-name t) (ind-name i)) ctx])))

(defn- binary-samples
  [{:keys [individuals predicates samples]} ctx]
  (into []
        (for [n (range samples)
              :let [a (mod n individuals)
                    b (mod (+ n 7) individuals)]]
          [(list (pred-name (mod n predicates)) (ind-name a) (ind-name b)) ctx])))

(defn- run-arm [label f samples]
  ;; warm the JIT on a tenth of the work, then measure
  (dotimes [i (max 1 (quot (count samples) 10))]
    (let [[s c] (nth samples i)] (f s c)))
  (let [[hits ns] (timed (reduce (fn [acc [s c]] (if (f s c) (inc acc) acc)) 0 samples))
        per       (double (/ ns (count samples)))]
    (println (format "  %-18s %9.1f µs/call   %,10.0f calls/s   (%,d of %,d flagged)"
                     label (/ per 1000.0) (/ 1e9 per) (long hits) (count samples)))
    per))

(defn- report-shape [kb opts ctx]
  (let [t   (reasoning/taxonomy kb)
        i0  (ind-name 0)
        ts  (v/types-of kb i0 ctx)
        gs  (mapv #(count (tax/genls t % ctx)) ts)]
    (println (format "shape: %,d types (branching %d), %,d individuals, %,d disjoint pairs"
                     (long (:types opts)) (long (:branching opts))
                     (long (:individuals opts)) (long (:disjoints opts))))
    (println (format "       a sampled term holds %d types; their genl closures are %s"
                     (count ts) (pr-str gs)))
    (println (format "       so the disjointness walk is ~%,d pair tests per assert"
                     (long (* (count ts) (apply max 1 gs) (apply max 1 gs)))))))

(defn- run [opts]
  (let [kb  (v/open-kb {:recover? false})
        _   (v/clear! kb)
        [ctx build-ns] (timed (build! kb opts))]
    (println (format "\nbuilt %,d sentexes in %.1f s\n"
                     (long (v/sentex-count kb)) (/ build-ns 1e9)))
    (report-shape kb opts ctx)
    (let [t (reasoning/taxonomy kb)]
      (println "\nthe primitives the checks are built out of")
      (let [u (unary-samples opts ctx)]
        (run-arm "genls (unscoped)" (fn [s _] (seq (tax/genls-global t (first s)))) u)
        (run-arm "genls (scoped)" (fn [s c] (seq (tax/genls t (first s) c))) u)
        (run-arm "specs thing (scoped)" (fn [_ c] (seq (tax/specs t 'thing c))) u)
        (run-arm "disjoint? (unscoped)" (fn [s _] (tax/disjoint? t (first s) 'thing)) u)
        (run-arm "disjoint? (scoped)" (fn [s c] (tax/disjoint? t (first s) 'thing c)) u)))
    ;; the sub-arms take the per-assert membership reader `constraint-problem` builds;
    ;; a fresh one per call is what they see in production
    (let [types #(kb/membership-reader kb %)]
      (println "\ndisjointness arm — a type membership (T X) where X already holds types")
      (let [u (unary-samples opts ctx)]
        (run-arm "types-of" (fn [s c] (seq (v/types-of kb (second s) c))) u)
        (run-arm "disjoint-problem" (fn [s c] (#'checks/disjoint-problem kb s c (types c))) u)
        (run-arm "constraint-problem" (fn [s c] (#'checks/constraint-problem kb s c)) u))
      (println "\nargIsa arm — a binary fact against its predicate's constraints")
      (let [b (binary-samples opts ctx)]
        (run-arm "  the arg lookup" (fn [s c] (seq (res/matches-visible
                                                       kb (list 'arg (first s) '?n '?type) c))) b)
        (run-arm "  memberships x1" (fn [s c] (seq (:types (kb/memberships kb (second s) c)))) b)
        (run-arm "arity-problem" (fn [s c] (#'checks/arity-problem kb s c (types c))) b)
        (run-arm "args-problem" (fn [s c] (#'checks/args-problem kb s c (types c))) b)
        (run-arm "genls-problem" (fn [s c] (#'checks/genls-problem kb s c)) b)
        (run-arm "declaration-problem" (fn [s c] (#'checks/declaration-problem kb s c (types c))) b)
        (run-arm "constraint-problem" (fn [s c] (#'checks/constraint-problem kb s c)) b)))
    (println)))

(defn- parse-args [args]
  (reduce (fn [m [k v]] (assoc m (keyword (subs k 2)) (Long/parseLong v)))
          defaults
          (partition 2 args)))

(defn -main [& args]
  (run (parse-args args))
  (shutdown-agents)
  (System/exit 0))
