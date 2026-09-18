;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.forward
  "Budgeting **forward** inference — the direction this KB should probably run, not the
  backward it happens to be loaded as.  Two costs decide the budget:

    - **Materialization** — forward chaining *stores* every derived fact (a record + an
      index entry + a JTMS node + a justification).  How many facts a rule set derives from
      a fact base is the storage budget, and for join rules it can super-scale.
    - **Matching** — finding all firings.  The reference chainer re-joins each candidate
      rule's non-trigger antecedents through the trie per arriving fact (quadratic on a
      leading-variable join); `vaelii.impl.rete` (TREAT alpha memories) answers that with a
      hash lookup.  Whether RETE is enough — or a beta network / something else is needed —
      is what the reference-vs-RETE column measures.

  Workload: the canonical forward-join benchmark — `parentOf` ⇒ `grandparentOf` (a 2-way
  join) and a 3-way `greatGrandparentOf`, matching the real corpus's 3–4-antecedent rule
  shape (`bench-backward`).  A sparse random parent graph keeps materialization bounded and
  measurable.

  RAM (records+index+JTMS retained, jol) and derived counts are trusted; wall-clock is
  untrusted under contention, but the reference-vs-RETE *ratio* — both under the same
  contention — is the signal.

  Run: `lein bench-forward [max-facts]`  (default 4000).  Mode `real [facts] [rules]` turns a
  sample of the real store's rules FORWARD over real facts and reports what fires."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.bench.survey :as survey]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rete :as rete]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- kb-ram [kb]
  (postings/retained [@(:state (:records kb)) @(:state (:backend (:index kb))) (reasoning/tms kb)]))

(defn- ms [t0] (/ (- (System/nanoTime) t0) 1e6))

(defn- gen-parents [^java.util.Random rng n p]
  ;; n parentOf edges over p individuals — a sparse random graph; 2-paths through it are the
  ;; grandparent derivations.
  (repeatedly n (fn [] [(symbol (str "Ind" (.nextInt rng p)))
                        (symbol (str "Ind" (.nextInt rng p)))])))

(defn- run [matcher-label enable? n rng]
  (if enable? (rete/enable!) (rete/disable!))
  (let [kb (kb/open-kb {:backend :memory :space 32 :recover? false}
                       (fn [k] (require 'vaelii.core) ((resolve 'vaelii.core/recover) k))
                       (fn [k] (require 'vaelii.core) ((resolve 'vaelii.core/reindex) k)))]
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (when enable? (rete/track! kb))
    (v/assert-rule kb ['(parentOf ?x ?y) '(parentOf ?y ?z)] '(grandparentOf ?x ?z) 'CxBench {:direction :forward})
    (v/assert-rule kb ['(parentOf ?x ?y) '(parentOf ?y ?z) '(parentOf ?z ?w)] '(greatGrandparentOf ?x ?w) 'CxBench {:direction :forward})
    (let [edges (gen-parents rng n (max 50 (quot n 2)))
          t0    (System/nanoTime)
          _     (v/with-deferred-settle kb
                  (doseq [[a b] edges] (v/assert kb (list 'parentOf a b) 'CxBench)))
          elapsed (ms t0)
          ix    (:index kb)
          gp    (p/count-with-functor ix 'grandparentOf)
          ggp   (p/count-with-functor ix 'greatGrandparentOf)
          derived (+ gp ggp)]
      {:matcher matcher-label :n n :derived derived :gp gp :ggp ggp
       :ms elapsed :per (/ elapsed n) :ram (kb-ram kb)})))

(defn- synthetic [maxn]
  (println "vaelii forward-inference budget — parentOf⇒grandparentOf (2-join) + greatGrandparentOf (3-join)")
  (println "derived counts + RAM are TRUSTED; wall-clock is UNTRUSTED (ratio reference:rete is the signal).")
  (println (format "\n  %-10s %8s %10s %10s %12s %12s %10s" "matcher" "facts" "derived" "µs/fact" "total ms" "reference×" "RAM MB"))
  (println (str "  " (apply str (repeat 78 \-))))
  (doseq [n (take-while #(<= % maxn) [500 1000 2000 4000 8000])]
    (let [ref  (run "reference" false n (java.util.Random. 1))
          ret  (run "rete"      true  n (java.util.Random. 1))]
      (doseq [{:keys [matcher derived per ms ram]} [ref ret]]
        (println (format "  %-10s %8s %10s %10.1f %12.1f %12s %10.1f"
                         matcher (format "%,d" n) (format "%,d" derived) (* 1000.0 per) ms
                         (if (= matcher "rete") (format "%.1f×" (/ (:ms ref) (max 0.01 ms))) "—")
                         (/ ram 1048576.0))))
      (println)))
  (println "  Reading: derived/facts is the MATERIALIZATION factor (storage budget = derived × ~2.3 KB");
  (println "  record+index+JTMS). reference× is RETE's forward-matching speedup; if it grows with N,")
  (println "  the reference matcher is super-scaling and RETE (or a beta network) is required.")
  (rete/disable!))

;; ---- Mode `real`: turn a sample of the real rules FORWARD -----------------

(defn- real-forward [n-facts n-rules]
  (let [dir  survey/default-dir
        _    (survey/ensure-store! dir (max n-facts (* 40 n-rules)))
        recs (survey/uniform-records dir (* 40 n-rules))       ; oversample; rules are ~0.3%
        rules (take n-rules (filter :antecedent recs))
        facts (survey/uniform-pairs dir n-facts)
        kb (kb/open-kb {:backend :memory :space 34 :recover? false}
                       (fn [k] (require 'vaelii.core) ((resolve 'vaelii.core/recover) k))
                       (fn [k] (require 'vaelii.core) ((resolve 'vaelii.core/reindex) k)))]
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (println (format "vaelii forward — REAL: %,d facts + %,d real rules turned FORWARD (READ-ONLY source)"
                     (count facts) (count rules)))
    (rete/enable!) (rete/track! kb)
    (let [loaded (atom 0) rejected (atom 0)
          f-ok (atom 0) f-bad (atom 0) why (atom {})]
      (v/with-deferred-settle kb
        (doseq [[s c] facts] (try (v/assert kb s c) (swap! f-ok inc)
                                  (catch clojure.lang.ExceptionInfo e
                                    (swap! f-bad inc) (swap! why update (:type (ex-data e) :other) (fnil inc 0)))
                                  (catch Exception _ (swap! f-bad inc))))
        (doseq [r rules]
          (let [antes (vec (:antecedent r)) conseq (:consequent r) ctx (:context r)]
            (try (v/assert-rule kb antes conseq ctx {:direction :forward}) (swap! loaded inc)
                 (catch clojure.lang.ExceptionInfo e
                   (swap! rejected inc) (swap! why update (:type (ex-data e) :other) (fnil inc 0)))
                 (catch Exception _ (swap! rejected inc))))))
      (let [base @f-ok
            total (count (p/sentex-ids (:records kb)))
            derived (- total base @loaded)]
        (println (format "  facts asserted: %,d ok, %,d rejected" @f-ok @f-bad))
        (println (format "  rejection reasons (ex-info :type): %s" (pr-str @why)))
        (println (format "  rules asserted forward: %,d  (rejected %,d)" @loaded @rejected))
        (println (format "  derived facts from forward firing: %,d  (%.2f× the fact base)"
                         (max 0 derived) (/ (double (max 0 derived)) (max 1 base))))
        (println (format "  chain-stats: %s" (pr-str (v/chain-stats kb))))
        (println (format "  RAM (records+index+JTMS): %.1f MB" (/ (kb-ram kb) 1048576.0)))))
    (rete/disable!)))

(defn -main [& args]
  (if (= "real" (first args))
    (real-forward (or (some-> (second args) Long/parseLong) 100000)
                  (or (some-> (nth args 2 nil) Long/parseLong) 2000))
    (synthetic (or (some-> (first args) Long/parseLong) 4000)))
  (shutdown-agents))
