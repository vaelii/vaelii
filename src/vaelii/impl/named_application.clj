;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.named-application
  "Supported results and projections of independently used compound rewrite targets."
  (:require [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def informant
  "The internal informant of a named application's supported materialization."
  ::named-application)

(defn- target-records
  "Target-index rows, including the target's spellings in the contexts naming it."
  [kb target]
  (let [rows (vec (kb/find-sentexes kb target))
        names (into #{target} (map #(res/normal-form kb target (res/visible-supporter-fn kb (:context %)))) rows)]
    [names (vec (distinct (mapcat #(kb/find-sentexes kb %) names)))]))

(defn- independent-handles
  "Candidate handles with finite live proofs not using this target's materialization."
  [kb handles names]
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
    (jtms/region-in tms nodes nodes inert out nil invalid)))

(defn- uses-name?
  "Does a sentence use a target spelling outside quoting and modal mention positions?"
  [kb names form]
  (let [modal (:modal (tax/mention-marks (reasoning/taxonomy kb)))]
    (letfn [(used? [x]
              (cond
                (contains? names x) true
                (vector? x) (boolean (some used? x))
                (seq? x) (cond
                           (or (sx/quoting-functor? (first x))
                               (contains? res/nat-quoting-predicates (first x))) false
                           (res/attitude-application? modal x) (or (used? (first x)) (used? (second x)))
                           :else (boolean (some used? x)))
                :else false))]
      (used? form))))

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
  [kb target names rows]
  (let [independent (independent-handles kb (map :id rows) names)
        uses (filter #(and (contains? independent (:id %))
                           (not (contains? '#{rewriteOf natFormula} (nm/functor (:sentence %))))
                           (uses-name? kb names (sx/sentence-of %))) rows)
        recs (:records kb)
        at #(res/exception-aware-placements kb %1 %2)
        add (fn [want sentence context antes]
              (update want [(kb/canonical-sentence kb sentence context) context] (fnil conj #{}) (set antes)))]
    (reduce
     (fn [want {rh :id rc :context [_ _ e] :sentence}]
       (let [f (first e)
             declarations (concat (kb/sentexes-matching kb (list 'result f '?t) '?ctx)
                                  (kb/sentexes-matching kb (list 'genlResult f '?t) '?ctx))
             projections (keep #(p/get-sentex recs %)
                               (reads/as-stored-with-args (:index kb) res/correspondence-predicate {1 f}))
             unique? (fn [c] (= (res/normal-form kb target (res/visible-supporter-fn kb c))
                                (nat-read/rewrite-target kb e nat-read/nat-namespace c)))]
         (reduce
          (fn [want {uh :id uc :context}]
            (let [want (reduce
                        (fn [want {dh :id [pred _ kind] :sentence}]
                          (reduce #(if (unique? %2)
                                     (add %1 (if (= pred 'result) (list kind target) (list 'genl target kind))
                                          %2 [rh uh dh]) %1)
                                  want (at [rh uh] [rc uc])))
                        want declarations)]
              (reduce
               (fn [want {dh :id dc :context [_ _ pred :as declaration] :sentence}]
                 (let [pos (res/stated-position declaration)]
                   (if (and pos (<= pos (inc (count (rest e)))))
                     (reduce #(if (unique? %2)
                                (add %1 (apply list pred (res/insert-at (rest e) pos target)) %2 [rh uh dh]) %1)
                             want (at [rh uh dh] [rc uc dc]))
                     want))) want projections)))
          want uses)))
     {} (rewrites kb target))))

(defn sync!
  "Reconcile owned facts for target; place! derives one fact, defer! postpones drops."
  [kb target place! defer!]
  (let [tms (reasoning/tms kb)
        recs (:records kb)
        [names rows] (target-records kb target)
        want (wanted kb target names rows)
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
