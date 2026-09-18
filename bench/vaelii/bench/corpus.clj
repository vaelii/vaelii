;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.corpus
  "Generate a corpus shaped like the real KB and watch how forward inference **behaves** on
  it — the open question being how a rule set of this shape works at all, not just how fast.

  It cannot use the real rules (they fail `v/assert` wholesale on naming — namespaced `ex/`
  predicates, hyphenated individuals; see bench-forward `real`), so it *synthesizes* rules
  with the measured structure (bench-backward): antecedent count peaking at 3–4, chain joins
  with shared variables (range-restricted), and Zipf-skewed **hot consequents**.  Facts
  populate a base band of predicates; rules draw antecedents Zipf from ALL predicates, so some
  fire straight from facts, some fire only after a cascade, and many (referencing sparse
  predicates) never fire — the real corpus's 37k rule-only predicates in miniature.

  Then it turns a fraction of the rules FORWARD and reports the behaviour: how much fires, the
  materialization factor, cascade depth / recursion truncation, contradictions and dropped
  conclusions (`violations`), and reference-matcher vs RETE.  Derived counts, RAM (jol), and
  the ledgers are trusted; wall-clock is untrusted under contention (the ref:rete ratio is the
  signal).

  Run: `lein bench-corpus [facts] [rules] [forward-fraction]`  (default 5000 5000 0.5).
  With no fraction it sweeps φ ∈ {0, 0.5, 1.0}."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rete :as rete]
            [vaelii.impl.types.reasoning :as reasoning]))

;; antecedent-count distribution from the real audit (bench-survey audit): mode 3–4.
(def ^:private ante-dist
  (vec (mapcat (fn [[k w]] (repeat w k)) [[1 6] [2 16] [3 38] [4 23] [5 12] [6 3] [7 1]])))

(defn- kb-ram [kb]
  (postings/retained [@(:state (:records kb)) @(:state (:backend (:index kb))) (reasoning/tms kb)]))

(defn- ms [t0] (/ (- (System/nanoTime) t0) 1e6))

;; Predicates are STRATIFIED into layers: band 0 gets facts, and a rule concluding a
;; layer-k predicate draws its antecedents only from layers < k.  That makes the rule set
;; acyclic — forward chaining cascades base → derived → further-derived and terminates in
;; ≤ L-1 rounds, instead of the pathological recursion a random (cyclic) rule set produces.
(defn- gen [{:keys [facts rules preds base inds phi seed layers]}]
  (let [rng   (java.util.Random. seed)
        pv    (u/terms "pr" preds)
        iv    (u/terms "Ind" inds)
        icum  (u/zipf-cumulative inds 1.0)
        ind   #(nth iv (zipf-sample icum rng))
        L     (or layers 3)
        bsz   (max 1 (quot (- preds base) (dec L)))
        band  (fn [k] (if (zero? k)
                        (subvec pv 0 base)
                        (subvec pv (min preds (+ base (* (dec k) bsz)))
                                (min preds (+ base (* k bsz))))))
        bcum  (u/zipf-cumulative base 1.1)
        ;; precompute per target-layer: the consequent band (hot within layer) and the
        ;; union of all lower bands to draw antecedents from.
        per-k (into {} (for [k (range 1 L)]
                         (let [cb (band k) lo (vec (mapcat band (range k)))]
                           [k {:cb cb :ccum (u/zipf-cumulative (count cb) 1.3)
                               :lo lo :lcum (u/zipf-cumulative (count lo) 1.1)}])))
        nfwd  (long (* phi rules))]
    {:facts (repeatedly facts (fn [] (list (nth (band 0) (zipf-sample bcum rng)) (ind) (ind))))
     :rules (mapv (fn [i]
                    (let [a    (nth ante-dist (.nextInt rng (count ante-dist)))
                          k    (inc (.nextInt rng (dec L)))         ; target layer 1..L-1
                          {:keys [cb ccum lo lcum]} (per-k k)
                          vars (mapv #(symbol (str "?v" %)) (range (inc a)))
                          antes (mapv (fn [j] (list (nth lo (zipf-sample lcum rng))
                                                    (nth vars j) (nth vars (inc j))))
                                      (range a))
                          conseq (list (nth cb (zipf-sample ccum rng)) (first vars) (last vars))]
                      {:antes antes :conseq conseq :forward? (< i nfwd) :layer k}))
                  (range rules))}))

(defn- load-run [label enable? md {:keys [facts rules]}]
  (if enable? (rete/enable!) (rete/disable!))
  (let [kb (kb/open-kb {:backend :memory :space 36 :recover? false}
                       (fn [k] (require 'vaelii.core) ((resolve 'vaelii.core/recover) k))
                       (fn [k] (require 'vaelii.core) ((resolve 'vaelii.core/reindex) k)))]
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (when enable? (rete/track! kb))
    (v/reset-settle-stats! kb)
    (let [t0 (System/nanoTime)
          nf (atom 0) nr (atom 0)]
      ;; rules first (so a fact fires them on arrival), then facts with a shallow
      ;; :max-depth — a hot-consequent cascade is bounded so an explosion terminates and
      ;; is reported (via :truncated?), not hung.  Non-forward rules are :backward (inert
      ;; to forward chaining), so φ actually controls how much fires.
      (v/with-deferred-settle kb
        (doseq [r rules]
          (try (v/assert-rule kb (:antes r) (:conseq r) 'CxBench {:direction (if (:forward? r) :forward :backward)})
               (swap! nr inc) (catch Exception _ nil)))
        (doseq [f facts] (try (v/assert kb f 'CxBench {:max-depth md}) (swap! nf inc) (catch Exception _ nil))))
      (let [elapsed (ms t0)
            base    @nf
            total   (count (p/sentex-ids (:records kb)))
            ruleN   (count (filter :forward? rules))
            derived (max 0 (- total base @nr))
            derived-preds (count (into #{} (comp (map #(p/get-sentex (:records kb) %))
                                                 (keep #(when (and % (not (:antecedent %)) (sequential? (:sentence %)))
                                                          (first (:sentence %)))))
                                       (p/sentex-ids (:records kb))))
            cs (v/chain-stats kb)]
        {:label label :facts base :rules-fwd ruleN :derived derived
         :factor (/ (double derived) (max 1 base))
         :derived-preds derived-preds
         :truncated? (get-in cs [:last :truncated?])
         :contradictions (count (v/contradictions kb)) :violations (count (v/violations kb))
         :ms elapsed :ram (kb-ram kb)}))))

(defn- report [{:keys [label facts rules-fwd derived factor derived-preds truncated? contradictions violations ms ram]}]
  (println (format "  %-10s facts %,d | fwd-rules %,d | derived %,d (%.1f× base, %,d distinct preds) | truncated %s | contradictions %d, violations %d | %.0f ms | %.1f MB"
                   label facts rules-fwd derived factor derived-preds (boolean truncated?)
                   contradictions violations ms (/ (double ram) 1048576.0))))

(defn -main [& args]
  (let [f   (or (some-> (first args) Long/parseLong) 3000)
        r   (or (some-> (second args) Long/parseLong) 3000)
        phi (some-> (nth args 2 nil) Double/parseDouble)
        layers 3
        md  (or (some-> (nth args 3 nil) Long/parseLong) (inc layers))  ; cascade-depth bound ≥ layers
        cfg {:facts f :rules r :preds (max 100 (quot r 4)) :base (max 20 (quot r 40))
             :inds f :seed 11 :layers layers}                  ; inds=facts → sparse joins
        phis (if phi [phi] [0.0 0.5 1.0])]
    (println (format "vaelii corpus behaviour — %,d facts, %,d rules, %,d preds (%,d base), %d layers; ante mode 3–4, Zipf hot consequents, max-depth %d"
                     f r (:preds cfg) (:base cfg) layers md))
    (println "derived/RAM/ledgers TRUSTED; wall-clock UNTRUSTED (ref:rete ratio is the signal).")
    (flush)
    (doseq [p phis]
      (println (format "\n── φ = %.0f%% rules forward ──" (* 100 p)))
      (flush)
      (let [data (gen (assoc cfg :phi p))
            ref  (load-run "reference" false md data)
            ret  (when (pos? p) (load-run "rete" true md data))]
        (report ref)
        (when ret
          (report ret)
          (println (format "  → RETE forward-match speedup: %.1f×  (derived identical: %s)"
                           (/ (:ms ref) (max 0.01 (:ms ret))) (= (:derived ref) (:derived ret)))))
        (flush)))
    (rete/disable!)
    (shutdown-agents)))
