;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-forward-oracle-test
  "The correctness oracle test for forward chaining on an inherited claim.

  Preservation lets a rule fire on a claim nobody stored, so the fixpoint reaches
  conclusions no stored fact unifies with — and every failure on that path is a
  **missing** answer rather than a wrong one.  A KB that is merely less informative
  than it should be reads as correct against anything except a second KB that was told
  the same thing another way, so this file is two of those.

    * **materialization** — a KB handed one general claim and a taxonomy must derive
      exactly what a KB handed every claim that general one licenses derives, over a
      randomized assert/retract stream compared after *every* operation.  The reference
      is rebuilt from the surviving claims each step, so an incremental path that fails
      to re-join, or re-joins what it should not, diverges at the operation that caused
      it.  The **justifications** are compared as well, projected to the conclusion,
      the rule and the strength: their antecedent lists differ by construction — a
      materialized claim rests on itself, an inherited one on the claim, the
      declaration and the reach edges — and that difference is the whole feature.

    * **order** — the same content in eight orders, from nothing each time, must reach
      the identical derived set *and* the identical justifications, antecedent sets
      included.  Which witness a firing names is meant to be a function of the content
      (a shortest reach path, neighbours in term order, ties broken on a context name),
      and this is what says so.  Rules are permuted with the facts, since \"the rule
      arrived last\" is what a rule's own full join would otherwise paper over, and the
      shapes are the awkward ones: a default general claim, an asymmetric predicate's
      converse stated one level down, an explicit denial of one tuple, and a shortcut
      edge, whose route replaces a longer one a firing named before it arrived."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(def ^:private ctx 'CxUniverse)

(defn- chain
  "A `depth`-long genl chain of temporary types, leaf first: `(genl c0 c1)`, `(genl c1
  c2)`, …  A claim stated at `ci` therefore licenses the `i+1` terms at or under it."
  [base depth]
  (mapv (fn [i] (tu/tmp-type (str base i "_t"))) (range depth)))

(defn- below
  "The terms at or under `t` on `c` — the reach a claim stated at `t` licenses."
  [c t]
  (take (inc (.indexOf ^java.util.List c t)) c))

(defn- chain-edges [c]
  (for [[sub sup] (partition 2 1 c)] (list 'genl sub sup)))

;; ---- content snapshots, by content and never by handle ------------------

(defn- sx-content
  "`[sentence context]` of the sentex at `id`, each `(sentexHandle h)` in the sentence
  read as `h`'s own content, since a handle number is the arrival order."
  [kb id]
  (when-let [s (p/get-sentex (:records kb) id)]
    [(walk/postwalk #(if-let [h (sx/handle-id %)] (sx-content kb h) %) (v/sentence-of s))
     (:context s)]))

(defn- derived-content
  "The conclusions the rule drew, as sentences — the half both oracles compare."
  [kb pred]
  (into #{} (map :sentence) (v/sentexes-matching kb (list pred '?x '?y) ctx)))

(defn- firing-shapes
  "Every justification as `[rule-sentence conclusion strength]` — what was concluded,
  by which rule, at what class.  The antecedent list is left out, because the two KBs
  of the first oracle are *meant* to disagree about it."
  [kb]
  (into #{}
        (keep (fn [id]
                (when-let [d (p/get-justification (:records kb) id)]
                  [(first (sx-content kb (:informant d)))
                   (first (sx-content kb (:consequence d)))
                   (:strength d)])))
        (p/justification-ids (:records kb))))

(defn- firing-content
  "The same with the antecedent sets, which the *order* oracle does compare: one
  content set in two orders must name the same witnesses."
  [kb]
  (into #{}
        (keep (fn [id]
                (when-let [d (p/get-justification (:records kb) id)]
                  [(first (sx-content kb (:informant d)))
                   (into #{} (map #(sx-content kb %)) (:antecedents d))
                   (first (sx-content kb (:consequence d)))
                   (:strength d)])))
        (p/justification-ids (:records kb))))

(defn- shuffled
  "A permutation of `xs` from `rng` — `clojure.core/shuffle` reads a global source, and
  a randomized oracle that cannot be replayed from its seed is not one."
  [xs ^java.util.Random rng]
  (let [a (java.util.ArrayList. ^java.util.Collection (vec xs))]
    (java.util.Collections/shuffle a rng)
    (vec a)))

;; ---- oracle 1: one general claim against every claim it licenses --------

(defn- build!
  "The two chains and the forward rule; the declarations too, when `preserving?`."
  [kb {:keys [rel con as bs preserving?]}]
  (v/with-deferred-settle kb
    (doseq [e (concat (chain-edges as) (chain-edges bs))]
      (v/assert kb e ctx {:strength :monotonic}))
    (when preserving?
      (v/assert kb (list 'transitiveInArgInverse rel 1 'genl) ctx {:strength :monotonic})
      (v/assert kb (list 'transitiveInArgInverse rel 2 'genl) ctx {:strength :monotonic})))
  (v/assert kb (list 'implies (list rel '?x '?y) (list con '?x '?y)) ctx {:direction :forward})
  kb)

(defn- materialized
  "A fresh reference KB stating every tuple the surviving general `claims` license,
  outright, with no declaration anywhere."
  [{:keys [rel as bs] :as world} claims]
  (let [kb (build! (tu/isolated-fresh) (assoc world :preserving? false))]
    (v/with-deferred-settle kb
      (doseq [[a b] claims, x (below as a), y (below bs b)]
        (v/assert kb (list rel x y) ctx {:strength :monotonic})))
    kb))

(deftest a-general-claim-derives-what-every-claim-it-licenses-derives
  (tu/with-terms [relOf con]
    (let [as    (chain "oa" 4)
          bs    (chain "ob" 4)
          world {:rel relOf :con con :as as :bs bs}
          pres  (build! (tu/empty-kb) (assoc world :preserving? true))
          rng   (java.util.Random. 20260804)]
      (try
        (loop [step 0, claims #{}]
          (when (< step 20)
            (let [drop?   (and (seq claims) (zero? (.nextInt rng 3)))
                  pair    (if drop?
                            (nth (vec (sort claims)) (.nextInt rng (count claims)))
                            [(nth as (.nextInt rng (count as)))
                             (nth bs (.nextInt rng (count bs)))])
                  claims' (if drop? (disj claims pair) (conj claims pair))
                  sen     (list relOf (first pair) (second pair))]
              (if drop?
                (v/retract! pres (v/handle-of pres sen ctx))
                (v/assert pres sen ctx {:strength :monotonic}))
              (let [mat (materialized world claims')]
                (try
                  (is (= (derived-content mat con) (derived-content pres con))
                      (str "step " step " (" (if drop? "retract " "assert ") (pr-str pair)
                           ") diverged\n  only materialized: "
                           (pr-str (set/difference (derived-content mat con)
                                                   (derived-content pres con)))
                           "\n  only preserved:    "
                           (pr-str (set/difference (derived-content pres con)
                                                   (derived-content mat con)))))
                  (is (= (firing-shapes mat) (firing-shapes pres))
                      (str "step " step ": the same conclusions, drawn by a different "
                           "rule or at a different strength"))
                  (finally (tu/clear-kb! mat))))
              (recur (inc step) claims'))))
        (testing "the stream reached something — an oracle over two empty KBs proves nothing"
          (is (< 1 (count (derived-content pres con)))))
        (finally (tu/clear-kb! pres))))))

;; ---- oracle 2: the same content in eight orders -------------------------

(deftest the-same-content-in-any-order-names-the-same-witnesses
  (tu/with-terms [relOf con]
    (let [as      (chain "pa" 4)
          bs      (chain "pb" 4)
          content (concat
                   (chain-edges as) (chain-edges bs)
                   ;; a shortcut across each chain: the orders that bring it after a
                   ;; firing over the long route must replace that route with it
                   [(list 'genl (nth as 0) (nth as 2))
                    (list 'genl (nth bs 0) (nth bs 3))]
                   [(list 'asymmetric relOf)
                    (list 'transitiveInArgInverse relOf 1 'genl)
                    (list 'transitiveInArgInverse relOf 2 'genl)
                    ;; the general claim: it licenses the whole grid
                    (list relOf (nth as 3) (nth bs 3))
                    ;; its converse one level down, which undercuts the pair it names
                    (list relOf (nth bs 1) (nth as 1))
                    ;; and a flat denial of one tuple, which is a dilemma rather than
                    ;; a licence
                    (list 'not (list relOf (nth as 0) (nth bs 2)))
                    (list 'set/forwardRule (list 'implies (list relOf '?x '?y) (list con '?x '?y)))])
          rng     (java.util.Random. 42424242)
          go      (fn [order]
                    (let [k (tu/isolated-fresh)]
                      (try
                        (doseq [s order] (v/assert k s ctx))
                        {:derived (derived-content k con) :because (firing-content k)}
                        (finally (tu/clear-kb! k)))))
          runs    (mapv (fn [_] (go (shuffled content rng))) (range 8))]
      (testing "the content derived something, and not the two pairs it withholds"
        (is (< 1 (count (:derived (first runs)))))
        (is (not (contains? (:derived (first runs)) (list con (nth as 1) (nth bs 1))))
            "the converse is the more specific claim there, so the general one does not fire")
        (is (not (contains? (:derived (first runs)) (list con (nth as 0) (nth bs 2))))
            "and a denied tuple leaves the claims disagreeing"))
      (doseq [[i r] (map-indexed vector (rest runs))]
        (is (= (:derived (first runs)) (:derived r))
            (str "order " (inc i) " derived a different set:\n"
                 (pr-str (set/difference (:derived (first runs)) (:derived r))) " / "
                 (pr-str (set/difference (:derived r) (:derived (first runs))))))
        (is (= (:because (first runs)) (:because r))
            (str "order " (inc i) " named different witnesses for the same content"))))))
