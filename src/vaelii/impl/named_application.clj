;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.named-application
  "Supported results and projections of independently used compound rewrite targets."
  (:require [vaelii.impl.checks :as checks]
            [vaelii.impl.except :as exc]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def informant
  "The internal informant of a named application's supported materialization."
  ::named-application)

(defn- target-records
  "Indexed target/application records; maps witness spelling, never independent demand."
  [kb target]
  (let [names (tax/equiv-class (reasoning/taxonomy kb) target)
        tms (reasoning/tms kb)]
    (loop [todo (vec names), seen #{}, rows {}, maps {}]
      (if-let [term (peek todo)]
        (if (contains? seen term)
          (recur (pop todo) seen rows maps)
          (let [rs (kb/find-sentexes kb term)
                ms (filter (fn [{h :id c :context [f k e] :sentence}]
                             (and (= 'natFormula f) (= sx/root-context c) (seq? e)
                                  (nat-read/reified-nat-symbol? k)
                                  (or (jtms/in? tms h)
                                      (and (jtms/premise? tms h) (jtms/network-in? tms h))))) rs)]
            (recur (into (pop todo) (map #(second (:sentence %))) ms)
                   (conj seen term) (into rows (map (juxt :id identity)) rs)
                   (into maps (map (juxt :id identity)) ms))))
        [names (vec (vals rows)) (vec (vals maps))]))))

(defn- independent-handles
  "Candidate handles with finite live proofs not using this target's materialization."
  [kb handles names bookkeeping reader]
  (let [tms (reasoning/tms kb)
        owned? #(and (= informant (:informant %))
                     (contains? names (get (:bindings (p/get-justification (:records kb) (:id %))) '?named-target)))
        {:keys [nodes invalid]}
        (loop [todo (vec handles), nodes #{}, invalid #{}]
          (if-let [h (peek todo)]
            (if (contains? nodes h)
              (recur (pop todo) nodes invalid)
              (let [js (keep #(jtms/justification tms %) (jtms/supports tms h))
                    owned (filter owned? js)]
                (recur (into (pop todo) (mapcat jtms/rests-on (remove owned? js)))
                       (conj nodes h) (into invalid (map :id) owned))))
            {:nodes nodes :invalid invalid}))
        inert (into #{} (filter #(and (not (jtms/known-datum? tms %))
                                      (p/get-sentex (:records kb) %))) nodes)
        out (into #{} (filter #(and (jtms/known-datum? tms %) (not (jtms/network-in? tms %)))) nodes)]
    ;; Intrinsic mint premises are not demand roots, but a separate justification of
    ;; the same row can still prove it. region-in's extra means forced OUT, so use its
    ;; public justification predicate with a target-local, seed-filtered fixpoint.
    (let [eligible? #(and (not (contains? out %)) (not (jtms/forced? tms :out %)))
          seed (into inert (filter #(and (jtms/premise? tms %) (eligible? %)
                                         (not (contains? bookkeeping %)))) nodes)
          js (into [] (comp (mapcat #(jtms/supports tms %)) (distinct)
                            (keep #(jtms/justification tms %))) nodes)
          invalid (into invalid (keys (when reader (exc/invalid-supports-at kb nodes reader))))
          valid? (jtms/region-valid-fn tms nodes nil invalid)]
      (loop [in seed]
        (let [next-in (reduce (fn [acc j]
                                (let [h (:consequence j)]
                                  (if (and (eligible? h) (valid? acc j)) (conj acc h) acc))) in js)]
          (if (= in next-in) in (recur next-in)))))))

(defn- used-spellings
  "Semantic target spellings and map witnesses; quoting is not an application use.
  Reads modal marks globally: whether a payload is a mention is sentence syntax,
  not the reader's belief-projection policy (docs/belief.md)."
  [kb names mappings form]
  (let [modal (:modal (tax/mention-marks (reasoning/taxonomy kb)))]
    (letfn [(used? [seen x]
              (cond
                (contains? names x) #{[x #{}]}
                (and (symbol? x) (contains? mappings x) (not (contains? seen x)))
                (let [{:keys [expression handles]} (get mappings x)]
                  (into #{} (map (fn [[spelling hs]] [spelling (into hs handles)]))
                        (used? (conj seen x) expression)))
                (vector? x) (into #{} (mapcat #(used? seen %)) x)
                (seq? x) (cond
                           (or (sx/quoting-functor? (first x))
                               (contains? res/nat-quoting-predicates (first x))) #{}
                           (res/attitude-application? modal x)
                           (into (used? seen (first x)) (used? seen (second x)))
                           :else (into #{} (mapcat #(used? seen %)) x))
                :else #{}))]
      (used? #{} form))))

(defn- proof-placements
  "Readers and equality/topology witnesses for a use spelling and original conclusion."
  [kb target spelling sentence base local-handles]
  (let [tx (reasoning/taxonomy kb)
        probe (list 'and sentence (list 'equals target spelling))
        readers (distinct (cons base (special/reader-contexts-at kb base probe)))]
    (for [reader readers
          :let [visible? (res/visible-supporter-fn kb reader)]
          :when (and (res/same-class-in? kb target spelling reader)
                     (every? #(res/supporter-visible? kb % reader false) local-handles))
          :let [paths (concat
                       (when (not= target spelling)
                         [(tax/scoped-path-supporters tx target spelling visible?)])
                       (keep (fn [[a b]] (tax/scoped-path-supporters tx a b visible?))
                             (kb/displaced-terms* kb sentence visible?)))
                rule-handles (into #{} (keep #(when (and (visible? (:handle %))
                                                         (rewrite/rule-applies? % sentence)) (:handle %)))
                                   (tax/rewrite-rules tx))
                alternatives (reduce (fn [acc path]
                                       (for [a acc, b (tax/path-alternatives path)] (into a b)))
                                     [rule-handles] paths)]
          witnesses alternatives
          :let [hs (into (set local-handles) witnesses)
                topology (mapcat #(checks/visibility-support kb % reader) hs)]]
      [reader (into witnesses topology)])))

(defn- rewrites
  "Stored compound rewrite rows naming this target."
  [kb target]
  (into [] (comp (keep #(p/get-sentex (:records kb) %))
                 (filter #(let [[f t e] (:sentence %)]
                            (and (= 'rewriteOf f) (= target t) (seq? e)
                                 (nat-read/reifiable-ground-nat? kb e)))))
        (reads/as-stored-with-args (:index kb) 'rewriteOf {1 target})))

(defn- wanted
  "The named facts and support sets the current independent uses and rewrites warrant."
  [kb target names rows maps]
  (let [bookkeeping (into #{} (mapcat #(nat/bookkeeping-handles kb (second (:sentence %)))) maps)
        mappings (into {} (map (fn [[k ms]]
                                 [k {:expression (nm/min-by-content-key #(nth (:sentence %) 2) ms)
                                     :handles (mapv :id ms)}]))
                       (group-by #(second (:sentence %)) maps))
        mappings (into {} (map (fn [[k m]] [k (update m :expression #(nth (:sentence %) 2))])) mappings)
        handles (mapv :id rows)
        independent (independent-handles kb handles names bookkeeping nil)
        independent-at (memoize #(independent-handles kb handles names bookkeeping %))
        uses (for [row rows
                   :when (and (contains? independent (:id row))
                              (not (kb/equality-sentence? (:sentence row)))
                              (not= 'natFormula (nm/functor (:sentence row))))
                   [spelling map-handles] (used-spellings kb names mappings (sx/sentence-of row))]
               [row spelling map-handles])
        recs (:records kb)
        at #(res/exception-aware-placements kb %1 %2)
        add (fn [want sentence base antes local-handles spelling e use-h]
              (reduce (fn [want [reader witnesses]]
                        (if (and (contains? (independent-at reader) use-h)
                                 (= (res/normal-form kb target (res/visible-supporter-fn kb reader))
                                    (nat-read/rewrite-target kb e nat-read/nat-namespace reader)))
                          (let [normalized (kb/rewrite-term kb sentence reader)
                                s (kb/canonical-sentence kb (nat-read/reify-existing kb normalized reader) reader)
                                supports (into (set antes) witnesses)
                                h (kb/find-sentex-handle kb s reader)]
                            (if (contains? supports h)
                              want
                              (update want [s reader] (fnil conj #{}) supports)))
                          want))
                      want (proof-placements kb target spelling sentence base local-handles)))]
    (reduce
     (fn [want {rh :id rc :context [_ _ e] :sentence}]
       (let [e (nat-read/sorted-expression kb e)
             f (first e)
             declarations (concat (kb/sentexes-matching kb (list 'result f '?t) '?ctx)
                                  (kb/sentexes-matching kb (list 'genlResult f '?t) '?ctx))
             projections (keep #(p/get-sentex recs %)
                               (reads/as-stored-with-args (:index kb) res/correspondence-predicate {1 f}))]
         (reduce
          (fn [want [{uh :id uc :context} spelling map-handles]]
            (let [want (reduce
                        (fn [want {dh :id [pred _ kind] :sentence}]
                          (reduce #(add %1 (if (= pred 'result) (list kind target) (list 'genl target kind))
                                        %2 (into [rh uh dh] map-handles) (into [rh uh] map-handles) spelling e uh)
                                  want (at (into [rh uh] map-handles) [rc uc])))
                        want declarations)]
              (reduce
               (fn [want {dh :id dc :context [_ _ pred :as declaration] :sentence}]
                 (let [pos (res/stated-position declaration)]
                   (if (and pos (<= pos (inc (count (rest e)))))
                     (reduce #(add %1 (apply list pred (res/insert-at (rest e) pos target))
                                   %2 (into [rh uh dh] map-handles) (into [rh uh dh] map-handles) spelling e uh)
                             want (at (into [rh uh dh] map-handles) [rc uc dc]))
                     want))) want projections)))
          want uses)))
     {} (rewrites kb target))))

(defn sync!
  "Reconcile owned facts for target; place! derives one fact, defer! postpones drops."
  [kb target place! defer!]
  (let [tms (reasoning/tms kb)
        recs (:records kb)
        [names rows maps] (target-records kb target)
        want (wanted kb target names rows maps)
        mine? #(when-let [j (p/get-justification recs %)]
                 (and (= informant (:informant j)) (= target (get (:bindings j) '?named-target))))
        ids (into #{} (filter mine?)
                  (mapcat #(concat (jtms/supports tms (:id %)) (jtms/dependents tms (:id %))) rows))
        wanted? #(when-let [j (jtms/justification tms %)]
                   (when-let [c (p/get-sentex recs (:consequence j))]
                     (contains? (get want [(sx/sentence-of c) (:context c)]) (set (:antecedents j)))))
        stale (remove wanted? ids)]
    (if defer!
      (when (seq stale) (defer!))
      (doseq [jid stale :when (jtms/justification tms jid)]
        (let [r (jtms/drop-justification! tms jid)]
          (p/delete-justification! recs jid)
          (integrate/apply-removals! kb r))))
    (into []
          (mapcat (fn [[[sentence context] supports]]
                    (mapcat (fn [antes]
                              (let [h (kb/find-sentex-handle kb sentence context)]
                                (when-not (and h (some #(let [j (jtms/justification tms %)]
                                                          (and (mine? %) (= (set antes) (set (:antecedents j)))))
                                                       (jtms/supports tms h)))
                                  (place! sentence context (kb/antecedent-order kb antes) {'?named-target target}))))
                            (sort-by nm/print-key supports))))
          (sort-by (comp nm/print-key key) want))))
