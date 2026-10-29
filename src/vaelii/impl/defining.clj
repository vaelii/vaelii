;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.defining
  "Ordinary defining contexts of a term, selected from its stored mentions."
  (:require [vaelii.impl.budget :as budget]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- mentions-term?
  [kb term sentence]
  (letfn [(visit [form root?]
            (budget/spend!)
            (cond
              (and (sequential? form) (= 'Quote (first form))) false
              (and (sequential? form) (not root?)
                   (or (contains? provers/formula-heads (first form))
                       (kb/isa? kb (first form) 'predicate))) false
              (= term form) true
              (sequential? form)
              (or (= term (first form))
                  (boolean
                   (some (fn [[n arg]]
                           (when-not (res/formula-position? kb (first form) n)
                             (visit arg false)))
                         (map-indexed (fn [i arg] [(inc i) arg]) (rest form)))))
              :else false))]
    (visit (sx/underlying-body sentence) true)))

(defn- bookkeeping-test
  [kb]
  (let [owners (volatile! {})]
    (fn [record]
      (some (fn [owner]
              (budget/spend!)
              (let [handles (if-let [entry (find @owners owner)]
                              (val entry)
                              (let [hs (into #{} (budget/checked-seq
                                                  (budget/checked-call
                                                   #(nat/bookkeeping-handles kb owner))))]
                                (vswap! owners assoc owner hs)
                                hs))]
                (contains? handles (:id record))))
            (budget/checked-call #(nat/reified-nats-in (sx/sentence-of record)))))))

(defn- support-role
  [candidates roles justification]
  (budget/spend!)
  (let [informant (:informant justification)
        antecedents (budget/checked-seq (:antecedents justification))
        source (first antecedents)
        content (filter candidates antecedents)
        prerequisites (budget/checked-seq (jtms/rests-on justification))]
    (cond
      (or (= 'decontextualized_predicate informant)
          (= chain/arity-class-informant informant)) :skeletal
      (or (special/mint-informant? informant) (= jtms/respell-informant informant))
      (get roles source)
      (some #(= :ordinary (get roles %)) content) :ordinary
      (and (seq content) (every? #(= :skeletal (get roles %)) content)) :skeletal
      (and (seq antecedents) (every? #(= :ordinary (get roles %)) prerequisites)) :ordinary
      (and (seq antecedents) (every? #(= :skeletal (get roles %)) antecedents)
           (or (not (integer? informant)) (contains? roles informant))) :skeletal)))

(defn- reachable-supports
  [kb initial valid?]
  (let [tms (reasoning/tms kb)]
    (loop [todo (into [] (budget/checked-seq (keys initial))), seen #{}, records initial, supports {}]
      (budget/spend!)
      (if-let [h (peek todo)]
        (if (contains? seen h)
          (recur (pop todo) seen records supports)
          (let [record (get records h)
                verdicts (budget/checked-call #(exc/justification-verdicts kb h (:context record)))
                js (into []
                         (comp (keep #(jtms/justification tms %))
                               (filter #(and (budget/checked-call (fn [] (valid? #{} %)))
                                             (= :supports (get verdicts (:id %))))))
                         (budget/checked-seq (jtms/supports tms h)))
                dependencies (into #{} (mapcat #(budget/checked-seq (jtms/rests-on %)))
                                   (budget/checked-seq js))
                added (into {} (keep (fn [dependency]
                                       (budget/spend!)
                                       (when-not (contains? records dependency)
                                         (when-let [s (p/get-sentex (:records kb) dependency)]
                                           [dependency s])))) dependencies)]
            (recur (into (pop todo) (remove seen) (keys added))
                   (conj seen h) (into records added) (assoc supports h js))))
        [records supports]))))

(defn definition-evidence
  "The ordinary contexts and whether nonempty stored defining evidence is skeletal-only.
  An absent assertion is not evidence of skeletal-only definition."
  [kb term]
  (let [term (sx/canon term)
        tms (reasoning/tms kb)
        mentions (into {} (map (juxt :id identity)) (budget/checked-seq (kb/find-sentexes kb term)))
        hidden? (or (budget/checked-call #(exc/own-hidden-fn kb)) (constantly false))
        live? #(and (jtms/in? tms %) (not (hidden? %)))
        candidates (into #{} (keep (fn [[h record]]
                                     (when (mentions-term? kb term (sx/sentence-of record)) h)))
                         (budget/checked-seq mentions))
        valid? (jtms/region-valid-fn tms #{} nil #{})
        [records supports] (reachable-supports kb mentions valid?)
        bookkeeping? (bookkeeping-test kb)
        seeds (into {} (keep (fn [[h record]]
                               (budget/spend!)
                               (when (and (live? h) (jtms/premise? tms h))
                                 [h (if (bookkeeping? record) :skeletal :ordinary)]))) records)
        roles (loop [roles seeds]
                (let [next (reduce-kv
                            (fn [result h js]
                              (budget/spend!)
                              (if (or (= :ordinary (get result h)) (not (live? h)))
                                result
                                (let [rs (keep #(support-role candidates roles %) js)]
                                  (cond
                                    (some #{:ordinary} rs) (assoc result h :ordinary)
                                    (some #{:skeletal} rs) (assoc result h :skeletal)
                                    :else result))))
                            roles supports)]
                  (if (= roles next) roles (recur next))))
        relevant (into [] (filter (fn [[h record]]
                                    (and (live? h)
                                         (mentions-term? kb term (sx/sentence-of record)))))
                       (budget/checked-seq mentions))
        unresolved (into []
                         (keep (fn [[h _]]
                                 (when (and (not= :ordinary (get roles h))
                                            (or (nil? (get roles h))
                                                (some #(nil? (support-role candidates roles %))
                                                      (get supports h))))
                                   h))) (budget/checked-seq relevant))]
    (when (seq unresolved)
      (throw (ex-info "Defining-context support is incomplete."
                      {:type :incomplete-defining-contexts :term term :handles unresolved})))
    {:contexts (budget/checked-call
                #(tax/maximal-contexts (reasoning/taxonomy kb)
                                       (into #{} (keep (fn [[h record]]
                                                         (when (= :ordinary (get roles h)) (:context record))))
                                             (budget/checked-seq relevant))))
     :skeletal-only? (boolean (and (seq relevant)
                                   (every? #(= :skeletal (get roles (first %)))
                                           (budget/checked-seq relevant))))}))

(defn defining-contexts
  "The maximal ordinary defining contexts. Unclassified support throws
  :incomplete-defining-contexts; an empty set does not certify skeletal-only evidence."
  [kb term]
  (:contexts (definition-evidence kb term)))
