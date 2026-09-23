;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.moved-predicates-oracle-test
  "A randomized ordering oracle for the narrowing `inherit/moved-predicates` applies to a
  `genl` edge.

  A `genl` edge, or a monotonic denial of one, re-joins the forward rules of the preserved
  predicates whose claims can cross it (`inherit/crossing-claim?`).  A narrowing that
  leaves out a predicate whose claim does cross the edge makes a conclusion depend on
  whether the edge or the claim arrived first.  `moved_predicates_test` holds one claim on
  one predicate, placed on the chain the edge joins, so a predicate the narrowing leaves
  out has no claim there to lose.

  Each seed generates a small KB: two or three type chains, some with a second route
  through a diamond; two to four predicates, each declared `transitiveInArg` or
  `transitiveInArgInverse` along `genl` at one or two positions; a `symmetric`,
  `commutative`, `commutativeInArgs` or `commutativeInArgAndRest` mark on some of them; a
  sub-predicate holding some of the claims; claims in either polarity on arbitrary chain
  terms; one forward rule per preserved predicate; and on some seeds a monotonic denial of
  a diamond edge, whose lower term still reaches the diamond's top over the other route.

  The orders permute every sentence, the marks included, so a mark arriving after the
  claims it permutes is one of the arrival orders compared.

  The reference is the seed's KB asserted in generation order with the narrowing
  disabled — `crossing-claim?` redefined to answer nil, which keeps every predicate
  preserved along `genl`.  Each subject asserts the same sentences in a seeded random
  order with the narrowing in force.  The believed rule consequents must be equal.  Every
  build gets its own cleared KB on the isolated space.

  `(run-seed seed n-orders)` replays a seed: the KB and its orders are functions of the
  seed alone, and a failure message names the seed, the order's index and the order.
  The sweep over forty seeds is `^:slow`; a sampled twin at `:default` runs three seeds
  through the same harness."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.inherit]
            [vaelii.test-util :as tu]))

(def ^:private ctx 'CxUniverse)

;; ---- generation ----------------------------------------------------------

(defn- pick [^java.util.Random rng xs] (nth xs (.nextInt rng (count xs))))

(defn- chance? [^java.util.Random rng p] (< (.nextDouble rng) p))

(defn- shuffled
  "A permutation of `xs` from `rng`, so an order is replayable from its seed."
  [xs ^java.util.Random rng]
  (let [a (java.util.ArrayList. ^java.util.Collection (vec xs))]
    (java.util.Collections/shuffle a rng)
    (vec a)))

(defn- type-chain
  "Chain `c`'s terms and edges.  A chain is four levels, `tmp_<c>0_t` at the bottom; a
  diamond chain adds `tmp_<c>1b_t` as a second route from level 0 to level 2, and names
  the two edges on the first route as the ones a denial may knock out."
  [c diamond?]
  (let [t     (fn [s] (symbol (str "tmp_" c s "_t")))
        level (mapv t ["0" "1" "2" "3"])
        edges (mapv (fn [[a b]] (list 'genl a b)) (partition 2 1 level))]
    (if diamond?
      {:terms     (conj level (t "1b"))
       :edges     (into edges [(list 'genl (level 0) (t "1b")) (list 'genl (t "1b") (level 2))])
       :deniable  [(edges 0) (edges 1)]}
      {:terms level :edges edges :deniable []})))

(defn- predicate
  "Predicate `k` as `[sentence options]` pairs under `:sentences`: its declarations, its
  permuting mark, an optional sub-predicate, its claims and its rule.  `:consequent` names
  the predicate the rule concludes, with the arity."
  [^java.util.Random rng k terms]
  (let [rel     (symbol (str "tmpRel" k))
        sub     (symbol (str "tmpSubRel" k))
        noted   (symbol (str "tmpNoted" k))
        arity   (pick rng [2 2 3])
        mark    (pick rng (if (= 2 arity)
                            [nil nil :symmetric :commutative :commutative]
                            [nil :commutative :commutative-in-args :commutative-in-args
                             :commutative-in-arg-and-rest]))
        subpred (chance? rng 0.4)
        n-decl  (pick rng [1 1 2])
        decls   (distinct
                 (repeatedly n-decl
                             #(list (pick rng '[transitiveInArg transitiveInArg transitiveInArgInverse])
                                    rel (inc (.nextInt rng arity)) 'genl)))
        claims  (vec
                 (repeatedly (+ 2 (.nextInt rng 3))
                             (fn []
                               (let [s (apply list (if (and subpred (chance? rng 0.5)) sub rel)
                                              (repeatedly arity #(pick rng terms)))]
                                 (if (chance? rng 0.25) (list 'not s) s)))))
        vars    (vec (take arity '[?x ?y ?z]))
        mono    {:strength :monotonic}]
    {:consequent [noted arity]
     :sentences
     (concat
      (map #(vector % mono) decls)
      (case mark
        nil                          []
        :symmetric                   [[(list 'symmetric rel) mono]]
        :commutative                 [[(list 'commutative rel) mono]]
        :commutative-in-args         [[(apply list 'commutativeInArgs rel
                                              (pick rng [[1 2] [1 3] [2 3]]))
                                       mono]]
        :commutative-in-arg-and-rest [[(list 'commutativeInArgAndRest rel (pick rng [1 2]))
                                       mono]])
      (when subpred [[(list 'genl sub rel) mono]])
      (map #(vector % {}) (distinct claims))
      [[(list 'set/forwardRule (list 'implies (apply list rel vars) (apply list noted vars))) {}]])}))

(defn- world
  "The KB seed `seed` generates: `:sentences` in generation order as `[sentence options]`
  pairs, which the orders permute, and the `:consequents` the rules conclude."
  [seed]
  (let [rng    (java.util.Random. seed)
        chains (mapv #(type-chain % (chance? rng 0.5)) (take (pick rng [2 3]) ["a" "b" "c"]))
        terms  (vec (mapcat :terms chains))
        preds  (mapv #(predicate rng % terms) (range (+ 2 (.nextInt rng 3))))
        denied (let [ds (vec (mapcat :deniable chains))]
                 (when (and (seq ds) (chance? rng 0.5)) (pick rng ds)))]
    {:consequents (mapv :consequent preds)
     :sentences   (vec (concat
                        (for [e (mapcat :edges chains)] [e {}])
                        (mapcat :sentences preds)
                        (when denied [[(list 'not denied) {:strength :monotonic}]])))}))

(defn- orders
  "`n` arrival orders of `w`'s sentences, drawn from a generator seeded by `seed` alone."
  [seed w n]
  (let [rng (java.util.Random. (bit-xor seed 0x5DEECE66D))]
    (vec (repeatedly n #(shuffled (:sentences w) rng)))))

;; ---- builds --------------------------------------------------------------

(defn- conclusions
  "The believed rule consequents of `w` built in `order`, in its own cleared KB."
  [w order]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (doseq [[s opts] order] (v/assert kb s ctx opts))
    (into #{}
          (mapcat (fn [[noted arity]]
                    (map :sentence
                         (v/sentexes-matching kb (apply list noted (take arity '[?x ?y ?z])) ctx))))
          (:consequents w))))

(defn- unnarrowed
  "`f` run with `crossing-claim?` answering nil, so a `genl` edge moves every predicate
  preserved along `genl`."
  [f]
  (with-redefs-fn {#'vaelii.impl.inherit/crossing-claim? (constantly nil)} f))

(defn- stated
  "Each positive claim as `[k sorted-arguments]`, `k` the index of its predicate.  A
  conclusion whose rule index and argument multiset appear here follows from a claim as
  stated or permuted, with no preservation."
  [w]
  (into #{}
        (keep (fn [[s _]]
                (when-let [[_ k] (and (seq? s) (re-matches #"tmp(?:Sub)?Rel(\d+)" (str (first s))))]
                  [k (sort (rest s))])))
        (:sentences w)))

(defn- inherited
  "The conclusions in `cs` no stated claim gives without preservation."
  [w cs]
  (let [st (stated w)]
    (into #{}
          (remove #(st [(re-find #"\d+$" (str (first %))) (sort (rest %))]))
          cs)))

(defn- run-seed
  "Build seed `seed`'s reference and `n-orders` narrowed subjects; answer
  `{:seed :reference :inherited :failures}`, a failure being `{:seed :order-index :order
  :missing :extra}`.
  `narrowed?` false disables the narrowing on the subjects too."
  ([seed n-orders] (run-seed seed n-orders true))
  ([seed n-orders narrowed?]
   (let [w         (world seed)
         reference (unnarrowed #(conclusions w (:sentences w)))
         subject   (fn [order] (if narrowed? (conclusions w order) (unnarrowed #(conclusions w order))))]
     {:seed      seed
      :reference reference
      :inherited (inherited w reference)
      :failures  (into []
                       (keep-indexed
                        (fn [i order]
                          (let [got (subject order)]
                            (when (not= reference got)
                              {:seed        seed
                               :order-index i
                               :order       (mapv first order)
                               :missing     (set/difference reference got)
                               :extra       (set/difference got reference)}))))
                       (orders seed w n-orders))})))

(defn- report [{:keys [seed order-index order missing extra]}]
  (str "seed " seed ", order " order-index " disagrees with the unnarrowed reference\n"
       "  missing: " (pr-str missing) "\n"
       "  extra:   " (pr-str extra) "\n"
       "  order:   " (pr-str order) "\n"
       "  replay:  (run-seed " seed " " (inc order-index) ")"))

(defn- agree [seeds n-orders]
  (let [runs     (mapv #(run-seed % n-orders) seeds)
        failures (mapcat :failures runs)]
    (testing "some seed's reference derives a conclusion that no stated claim gives, so
              the orders are compared over preserved reaches"
      (is (some #(seq (:inherited %)) runs)))
    (is (= [] (mapv (juxt :seed :order-index) failures))
        (apply str (interpose "\n\n" (map report failures))))))

(def ^:private sampled-seeds
  "Three seeds whose two sampled orders each carry a `commutative` or `commutativeInArgs`
  mark before the claims it permutes and another after them, and whose references hold
  preserved conclusions.  Seed 38 denies a diamond edge as well."
  [15 25 38])

(deftest a-narrowed-genl-edge-concludes-what-the-unnarrowed-one-does-in-sampled-orders
  (agree sampled-seeds 2))

(deftest ^:slow a-narrowed-genl-edge-concludes-what-the-unnarrowed-one-does-in-every-seed
  (agree (range 40) 8))
