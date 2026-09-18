;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.jtms
  "Where the JTMS's bytes are, and what the dense representation recovers.

  Phase 0 measured the JTMS at ~467 B per premise node (~43 GB at 100M) and stopped
  there, and the build plan that followed proposes bitmaps for the belief sets, parallel
  primitive arrays for the per-node scalars, and CSR arrays for the dependency edges.
  Each of those is a guess about *where the 467 bytes are*.  The index and record phases
  both found the plan's guess wrong — blanket Roaring lost to a tiered `int[]`, and the
  frame's cost turned out to be scaffolding rather than content — so this decomposes
  before crediting anything, and then measures the two representations side by side:

    1. **By key** — `:nodes` / `:justs` / the four belief sets / `:classes` /
       `:superseded`, each sized on its own.
    2. **Within `:nodes`, by field** — built by *stripping* one field from a copy of the
       real state and re-measuring, so each number is what removing that field would
       actually release rather than a sum of estimates.
    3. **What the JTMS pins of the record store.**  A node names its datum by handle
       alone, so the always-resident network holds no record resident — the property
       record paging (Phase 4) depends on, measured rather than assumed because the
       field that would break it is an easy one to add back.
    4. **A belief-set bake-off at the real cardinalities.**  `bench-postings` found
       RoaringBitmap a loss (1.07–1.45×) on the index's *tiny* postings.  The belief sets
       are the opposite regime — `:in` holds nearly every node — so the answer there does
       not carry over and has to be taken here.
    5. **The two representations, same KB** — `:reference` against `:dense`
       (`vaelii.impl.dense-jtms`), sized as the object a running KB actually holds, and
       split so what each spends on justifications is visible separately from the node
       graph.
    6. **Within a justification, by field**, on a **rules-heavy** corpus — a fact corpus
       derives about a tenth of a justification per node and cannot say what one costs.
       This is what decided the justification columns.

  Run: `lein bench-jtms [facts] [rule-facts]`  (default 100000 / 20000)."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.bench.util :as u]
            [vaelii.core :as v]
            [vaelii.impl.dense-jtms]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [org.roaringbitmap RoaringBitmap]
           [vaelii.impl.dense_jtms DenseTms]
           [vaelii.impl.types.tms HeapColumns]))

(defn- mb [b] (/ (double b) 1048576.0))
(defn- retained ^long [objs] (postings/retained objs))

(defn- just-structures
  "What each representation actually **holds** for its justifications: the reference's
  map of records, the dense one's columns.

  Never `jtms/justifications`: the dense network stores no justification object and
  rebuilds one on demand, so sizing what that returns would size a temporary and
  credit the dense representation with a cost it does not pay."
  [tms]
  (if (instance? DenseTms tms)
    (let [cols ^HeapColumns (.-cols ^DenseTms tms)]
      [(.-jids ^DenseTms tms) (.-j-conseq cols) (.-j-inf cols)
       (.-j-inf-sym ^DenseTms tms) (.-j-antes cols) (.-j-mono ^DenseTms tms)])
    [(:justs @tms)]))

;; ---- a KB with a JTMS actually built ------------------------------------

(defn- gen-facts
  "Zipfian facts, so the vocabulary repeats the way a real corpus's does."
  [^java.util.Random rng n]
  (let [preds (u/terms "p" 200)
        inds  (u/terms "I" (max 100 (quot n 4)))
        pcum  (u/zipf-cumulative (count preds) 1.1)
        icum  (u/zipf-cumulative (count inds) 1.1)]
    (repeatedly n #(list (nth preds (u/zipf-sample pcum rng))
                         (nth inds (u/zipf-sample icum rng))
                         (nth inds (u/zipf-sample icum rng))))))

(defn- build-kb
  "`n` premise facts plus a forward rule fired over `m` more, so the JTMS holds premise
  nodes, derived nodes, and real justifications — the structure that is being sized."
  ([n m strength] (build-kb n m strength :reference))
  ([n m strength tms]
   (let [kb  (v/open-kb {:backend :memory :space 60
                         :recover? false :tms tms})
         rng (java.util.Random. 20260724)]
     (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
     (doseq [s (gen-facts rng n)]
       (try (v/assert kb s 'CxBench {:chain? false :strength strength})
            (catch Exception _ nil)))
     ;; a rule and facts that fire it, so :justs and the derived nodes are populated
     (v/assert-rule kb '[(likes ?x ?y)] '(knows ?x ?y) 'CxBench {:direction :forward})
     (let [inds (u/terms "J" (max 10 (quot m 2)))
           icum (u/zipf-cumulative (count inds) 1.1)]
       (doseq [_ (range m)]
         (try (v/assert kb (list 'likes
                                 (nth inds (u/zipf-sample icum rng))
                                 (nth inds (u/zipf-sample icum rng)))
                        'CxBench {:strength strength})
              (catch Exception _ nil))))
     kb)))

;; ---- decomposition ------------------------------------------------------

(defn- strip-node-field [state k]
  (update state :nodes (fn [ns] (into {} (map (fn [[d n]] [d (dissoc n k)])) ns))))

(defn- by-key [state]
  (let [total (retained [state])
        rows  (for [k [:nodes :justs :in :groundable :defeated :blocked :touched
                       :classes :superseded]]
                [k (retained [(get state k)]) (count (get state k))])]
    (println "\n══ Phase 3.1: the JTMS by key ══")
    (println (format "  %-12s %10s %12s %8s" "key" "MB" "entries" "%"))
    (println (str "  " (apply str (repeat 46 \-))))
    (doseq [[k b n] rows]
      (println (format "  %-12s %10.1f %12s %7.0f%%"
                       (name k) (mb b) (format "%,d" n) (* 100.0 (/ (double b) total)))))
    (println (format "  %-12s %10.1f  (the whole atom, deduped)" "TOTAL" (mb total)))
    total))

(defn- by-node-field [state total]
  (let [nodes (count (:nodes state))
        base  (retained [state])]
    (println "\n══ Phase 3.2: within :nodes, what each field costs ══")
    (println (format "  %,d nodes; each row is what STRIPPING that field releases" nodes))
    (println (format "  %-20s %10s %12s" "field" "MB" "B/node"))
    (println (str "  " (apply str (repeat 46 \-))))
    (doseq [k [:supports :consequences :depth :premise? :premise-strength :datum]]
      (let [b (- base (retained [(strip-node-field state k)]))]
        (println (format "  %-20s %10.1f %12.1f" (name k) (mb b) (/ (double b) nodes)))))
    ;; what is left once every field is stripped is the per-node map object and the HAMT
    ;; holding it — nothing to do with the fields, and the reason the fix is to stop
    ;; having a map per node rather than to shrink the fields (they are shared objects
    ;; already: stripping a scalar releases nothing at all)
    (let [bare (retained [(reduce strip-node-field state
                                  [:supports :consequences :depth :premise?
                                   :premise-strength :datum])])]
      (println (format "  %-20s %10.1f %12.1f  (the node map + HAMT itself — the residue)"
                       "structure" (mb bare) (/ (double bare) nodes))))
    (println (format "  (the whole JTMS is %.1f MB = %.0f B/node)" (mb total) (/ (double total) nodes)))))

(defn- store-independence
  "A node names its datum by handle and holds no reference to the sentex it labels, so
  the always-resident JTMS pins none of the record store.  That is what makes record
  paging (Phase 4) mean anything: a strong reference from here would hold every record
  in RAM whatever the backend does.  Measured rather than asserted, because the field
  it forbids would be an easy and invisible thing to add back."
  [kb state]
  (let [pinned (into [] (keep :sentex) (vals (:nodes state)))
        recs   (retained [@(:state (:records kb))])]
    (println "\n══ Phase 3.3: what the JTMS pins of the record store ══")
    (println (format "  %,d of %,d nodes hold a record reference; the store is %.1f MB"
                     (count pinned) (count (:nodes state)) (mb recs)))
    (println (if (seq pinned)
               (format "  REGRESSION: the nodes retain %.1f MB of it — record paging is defeated"
                       (mb (retained pinned)))
               "  none — the store is free to page, which is the premise Phase 4 rests on"))))

;; ---- belief-set encodings, at the cardinalities that actually occur ------

(defn- set-bakeoff [state]
  (let [in     (:in state)
        n      (count in)
        ids    (int-array (sort in))
        boxed  (retained [in])
        roar   (let [r (RoaringBitmap.)] (doseq [i ids] (.add r (int i))) (.runOptimize r) r)
        roar-b (retained [roar])
        arr-b  (retained [ids])]
    (println "\n══ Phase 3.4: the belief sets — encodings at the real cardinality ══")
    (println (format "  :in holds %,d of %,d nodes (%.0f%% — the DENSE regime, unlike the index's postings)"
                     n (count (:nodes state)) (* 100.0 (/ (double n) (count (:nodes state))))))
    (println (format "  %-28s %10.2f MB %8s" "PersistentHashSet<Long>" (mb boxed) "—"))
    (println (format "  %-28s %10.2f MB %7.1f×" "sorted int[]" (mb arr-b) (/ (double boxed) arr-b)))
    (println (format "  %-28s %10.2f MB %7.1f×" "RoaringBitmap" (mb roar-b) (/ (double boxed) roar-b)))
    (println "  (bench-postings found Roaring a LOSS on the index's tiny postings; a belief set is")
    (println "   the opposite regime, so that finding does not carry over and this is the one to use.)")))

(defn- representations
  "The measurement the whole phase is for: the same KB, the same facts, the same rule
  firings, held in each TMS representation — sized as the object the KB actually holds,
  never as a deref (the dense one would materialize a snapshot and measure that instead).

  Built twice from scratch rather than converted, because the point is what a running
  KB costs, not what a translation costs."
  [n m st]
  (let [size    (fn [kb] [(retained [(reasoning/tms kb)])
                          (retained (just-structures (reasoning/tms kb)))])
        ref-kb  (build-kb n m st :reference)
        [ref-b ref-j] (size ref-kb)
        nodes   (count (jtms/datums (reasoning/tms ref-kb)))
        _       (p/clear-records! (:records ref-kb))
        dns-kb  (build-kb n m st :dense)
        [dns-b dns-j] (size dns-kb)
        row     (fn [label b j vs]
                  (println (format "  %-28s %8.1f %9.1f %9.1f %8s" label
                                   (mb b) (mb (- b j)) (mb j) vs)))]
    (println "\n══ Phase 3.5: the two representations, same KB ══")
    (println (format "  %-28s %8s %9s %9s %8s"
                     "representation" "total" "graph" "justs" "vs ref"))
    (println (str "  " (apply str (repeat 68 \-))))
    (row ":reference (atom + map)" ref-b ref-j "—")
    (row ":dense (bitmaps + int maps)" dns-b dns-j (format "%.2fx" (/ (double ref-b) dns-b)))
    (println (format "  %,d nodes: %.0f -> %.0f B/node overall, and %.0f -> %.0f on the graph alone"
                     nodes (/ (double ref-b) nodes) (/ (double dns-b) nodes)
                     (/ (double (- ref-b ref-j)) nodes) (/ (double (- dns-b dns-j)) nodes)))
    ;; The justification share, which is where the phase's last lever was spent: the
    ;; reference holds a record per justification, the dense one holds columns and no
    ;; object at all.  3.7 below is what one shape of corpus shows; 3.6/3.7 measure the
    ;; shape where it actually dominates.
    (println (format "  justifications are %.0f%% of the dense network at this (fact-heavy) shape"
                     (* 100.0 (/ (double dns-j) dns-b))))
    (println "  (identical answers: jtms_dense_oracle_test, and the whole suite runs green through it)")))

;; ---- the rules-heavy corpus, and what a justification costs -------------

(defn- build-join-kb
  "A corpus where the *justifications* are the mass rather than the facts.

  A fact corpus derives about a tenth of a justification per node, which cannot say
  what the justification copy costs — so this is a dense binary relation with a **join
  rule** over it, the grandparent shape.  Every 2-path is a separate witness, so a
  derived datum carries many supports and the justifications outnumber the nodes,
  which is the regime a rules-heavy KB is actually in."
  ([inds edges strength] (build-join-kb inds edges strength :reference))
  ([inds edges strength tms]
   (let [kb  (v/open-kb {:backend :memory :space 62
                         :recover? false :tms tms})
         rng (java.util.Random. 20260725)
         who (u/terms "K" inds)]
     (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
     (v/assert-rule kb '[(rel ?x ?y) (rel ?y ?z)] '(linked ?x ?z) 'CxBench {:direction :forward})
     (doseq [_ (range edges)]
       (try (v/assert kb (list 'rel (nth who (.nextInt rng inds)) (nth who (.nextInt rng inds)))
                      'CxBench {:strength strength})
            (catch Exception _ nil)))
     kb)))

(defn- strip-just-field
  "Nil one field of every justification, keeping the record shape — so the delta is
  exactly what that field's *value* retained, and a field holding a shared object
  (a keyword) correctly reads zero."
  [state k]
  (update state :justs (fn [js] (into {} (map (fn [[i j]] [i (assoc j k nil)])) js))))

(defn- by-just-field
  "What each justification field costs, by stripping — the counterpart of 3.2, and the
  measurement the CSR prescription was deferred for.

  This runs on what the **network stores**, which is `jtms/graph-just` and not the
  record: so the `bindings` row reading zero is the regression guard on that, not a
  claim that a firing's variable map is free.  Measured against a network that did
  hold them, they were 80 of 277 B — the largest single field after the record object
  itself, and the reason they now live only in the record store."
  [state]
  (let [;; the baseline is the map REBUILT with the same records, not the original.
        ;; Stripping rebuilds it, and a `PersistentHashMap` grown by `into` is a few
        ;; bytes an entry off one grown by `assoc` — a constant that would otherwise
        ;; land on every row and read as a negative cost for the shared-object fields.
        rebuild (fn [s] (:justs (update s :justs (fn [js] (into {} js)))))
        js   (rebuild state)
        n    (count js)
        base (retained [js])]
    (println "\n══ Phase 3.6: within :justs, what each field costs ══")
    (println (format "  %,d justifications; each row is what STRIPPING that field releases" n))
    (println (format "  %-20s %10s %11s %8s" "field" "MB" "B/just" "%"))
    (println (str "  " (apply str (repeat 52 \-))))
    (doseq [k [:antecedents :bindings :consequence :id :informant :strength :out]]
      (let [b (- base (retained [(:justs (strip-just-field state k))]))]
        (println (format "  %-20s %10.2f %11.1f %7.0f%%"
                         (name k) (mb b) (/ (double b) n) (* 100.0 (/ (double b) base))))))
    (let [bare (retained [(:justs (reduce strip-just-field state
                                          [:antecedents :bindings :consequence :id
                                           :informant :strength :out]))])]
      (println (format "  %-20s %10.2f %11.1f %7.0f%%  (the record object + its map slot)"
                       "structure" (mb bare) (/ (double bare) n) (* 100.0 (/ (double bare) base)))))
    (println (format "  TOTAL                %10.2f %11.1f" (mb base) (/ (double base) n)))))

(defn- join-representations
  "3.5 again on the rules-heavy corpus — where the justification copy, not the node
  graph, is what the network is made of."
  [inds edges st]
  (let [size    (fn [kb] [(retained [(reasoning/tms kb)])
                          (retained (just-structures (reasoning/tms kb)))])
        ref-kb  (build-join-kb inds edges st :reference)
        [ref-b ref-j] (size ref-kb)
        state   @(reasoning/tms ref-kb)
        nodes   (count (:nodes state))
        justs   (count (:justs state))]
    (println (format "\n══ Phase 3.7: the rules-heavy corpus — %,d nodes, %,d justifications (%.1f per node) ══"
                     nodes justs (/ (double justs) nodes)))
    (by-just-field state)
    (p/clear-records! (:records ref-kb))
    (let [dns-kb  (build-join-kb inds edges st :dense)
          [dns-b dns-j] (size dns-kb)
          row     (fn [label b j vs]
                    (println (format "  %-28s %8.1f %9.1f %9.1f %8s" label
                                     (mb b) (mb (- b j)) (mb j) vs)))]
      (println "\n  the two representations at this shape:")
      (println (format "  %-28s %8s %9s %9s %8s"
                       "representation" "total" "graph" "justs" "vs ref"))
      (println (str "  " (apply str (repeat 68 \-))))
      (row ":reference (atom + map)" ref-b ref-j "—")
      (row ":dense (bitmaps + int maps)" dns-b dns-j (format "%.2fx" (/ (double ref-b) dns-b)))
      (println (format "  the justification copy is %.0f%% of the dense network here (%.0f B each)"
                       (* 100.0 (/ (double dns-j) dns-b)) (/ (double dns-j) justs))))))

(defn -main [& args]
  (let [n  (or (some-> (first args) Long/parseLong) 100000)
        m  (or (some-> (second args) Long/parseLong) 20000)
        ;; the assumption strength the facts carry.  It decides how much of `:classes`
        ;; is above the lattice's bottom, and a common-sense KB's content is mostly
        ;; :default — so measure that, not only the monotonic case.
        st (keyword (or (nth args 2 nil) "default"))
        kb (build-kb n m st)
        state @(reasoning/tms kb)]
    (println (format "vaelii Phase-3 JTMS measurement — %,d nodes, %,d justifications, facts at %s"
                     (count (:nodes state)) (count (:justs state)) st))
    (println "Density (jol retained heap) is TRUSTED — structural, so contention-immune.")
    (let [total (by-key state)]
      (by-node-field state total)
      (store-independence kb state)
      (set-bakeoff state))
    (representations n m st)
    (join-representations 120 3000 st)
    (shutdown-agents)))
