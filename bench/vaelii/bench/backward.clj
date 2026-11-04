;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.backward
  "Backward-chain rule-path scaling — the axis that matters for this corpus (99% backward
  rules), which RETE does not touch.

  A backward goal on predicate P is answered by expanding the rules that could conclude P:
  `res/concluding-rule-handles` = `specs(P)` ∩ `rules-by-consequent(P)`, an **indexed**
  intersection over the consequent index (`:rule-consequent`).  So the per-goal candidate set is bounded by
  *how many rules conclude P* — not by the total rule count — provided that lookup really is
  indexed and never scans.  This bench verifies that and sizes it:

    - candidate-set size (`reads/as-stored-rules-by-consequent-in`) for a hot vs rare
      consequent predicate, as the rule count N grows — a hot consequent's candidate set
      grows (it is the cost driver of a backward goal on it); a rare one stays flat, and
      neither is O(N)-by-scan.
    - the `:rule-index` posting RAM under the current boxed sets vs a dense `int[]` (the same
      tiering Phase 1 found for fact postings applies to rule postings).

  Structural sizes (candidate counts, posting RAM) are trusted; any wall-clock is untrusted
  under contention.  Rules are indexed via `rules/index-rule` directly (the reference load path,
  as in bench/memory.clj), so this measures the rule INDEX, not assert-rule's checks.

  Run: `lein bench-backward [max-rules]`  (default 200000)."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as rules]))

(defn- gen-rule [^java.util.Random rng preds pred-cum]
  (let [antes (distinct (repeatedly (inc (.nextInt rng 3)) #(nth preds (zipf-sample pred-cum rng))))
        conc  (nth preds (zipf-sample pred-cum rng))]
    [antes conc]))

(defn- index-rules! [kb n rng preds pred-cum]
  (let [ix (:index kb)]
    (dotimes [i n]
      (let [[antes conc] (gen-rule rng preds pred-cum)]
        (rules/index-rule ix (+ 1000000000 i) antes conc (quote CxBench))))))

(defn- ridx-postings [state]
  ;; the consequent index's leaves (`[:rule-consequent :handles [pred ctx]] -> #{rule-handles}`)
  (keep (fn [[k v]] (when (and (vector? k) (= :rule-consequent (first k)) (= :handles (second k)) (set? v)) v)) state))

(defn- ->intarr ^ints [s] (int-array (sort (map #(int (- % 1000000000)) s))))

(defn -main [& args]
  (let [maxn  (or (some-> (first args) Long/parseLong) 200000)
        P     (max 100 (quot maxn 20))
        preds (u/terms "pr" P)
        pcum  (u/zipf-cumulative P 1.2)               ; skewed consequents, like real rules
        hot   (first preds) mid (nth preds (quot P 2)) rare (last preds)]
    (println (format "vaelii backward-chain :rule-index scaling — up to %,d synthetic rules, %,d predicates (Zipf consequents)" maxn P))
    (println "candidate-set sizes + posting RAM are TRUSTED (structural); wall-clock would be untrusted.")
    (println (format "\n  %-10s %14s %14s %14s %12s %12s" "rules(N)" "rules→hot" "rules→mid" "rules→rare" "ridx baseMB" "ridx int[]MB"))
    (println (str "  " (apply str (repeat 80 \-))))
    (doseq [n [10000 50000 (min maxn 200000)]]
      (let [kb (kb/open-kb {:backend :memory :space 30 :recover? false}
                           (fn [_] nil) (fn [_] nil))]
        (p/clear-index! (:index kb))
        (index-rules! kb n (java.util.Random. 7) preds pcum)
        (let [ix    (:index kb)
              state @(:state (:backend (:index kb)))
              c-hot  (count (reads/as-stored-rules-by-consequent-global ix hot))
              c-mid  (count (reads/as-stored-rules-by-consequent-global ix mid))
              c-rare (count (reads/as-stored-rules-by-consequent-global ix rare))
              posts  (vec (ridx-postings state))
              base   (postings/retained posts)
              arr    (postings/retained (mapv ->intarr posts))]
          (println (format "  %-10s %14s %14s %14s %12.1f %12.1f"
                           (format "%,d" n) (format "%,d" c-hot) (format "%,d" c-mid) (format "%,d" c-rare)
                           (/ base 1048576.0) (/ arr 1048576.0))))))
    (println "\n  Reading:")
    (println "  - candidate set for a goal = rules-by-consequent(pred): a hot consequent's set grows")
    (println "    with N (Zipf), a rare one stays ~flat — the lookup is indexed (bounded by the")
    (println "    consequent posting), never an O(N) scan of all rules. A hot-consequent GOAL therefore")
    (println "    reads a large candidate list per backward step — the backward analog of a hot fact posting.")
    (println "  - the :rule-index postings take the same int[] win as fact postings (baseline vs int[] columns).")
    (shutdown-agents)))
