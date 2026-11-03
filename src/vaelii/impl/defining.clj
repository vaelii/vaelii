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
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(declare mentions-in-sentence?)

(defn- mentions-term?
  "Does `record` name `term` as content?  A literal answers for its own sentence; a rule
  answers for each of its antecedent literals and its consequent, each read as a sentence
  of its own, so a rule that names `term` in its body mentions it."
  [kb term record]
  (if-let [antecedent (:antecedent record)]
    (boolean (some #(mentions-in-sentence? kb term %)
                   (cons (:consequent record)
                         (if (sequential? (first antecedent)) antecedent [antecedent]))))
    (mentions-in-sentence? kb term (sx/sentence-of record))))

(defn- mentions-in-sentence?
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

(defn- walked-handles
  "What the leaf walk descends to from justification `j`: every handle it rests on
  (`jtms/rests-on`), its antecedents and its rule alike, so an asserted rule is a leaf and
  a deduced one is walked down to its own support.  The mark `:computed` joins them when
  `j` names no antecedent: a firing whose literals are all computed (`evaluate`,
  `lessThan`, a prover's answer) records no handle for them."
  [j]
  (cond-> (vec (budget/checked-seq (jtms/rests-on j)))
    (empty? (:antecedents j)) (conj :computed)))

(defn- support-leaves
  "`{:leaves #{h} :marks #{k}}`: the premises (`premise?`) the items `hs` reach through the
  justifications `supports` maps each handle to, `step` giving what each justification
  descends to, and the keywords met among those items.  A premise is a leaf and is not
  descended past; a handle `supports` gives no justification adds nothing.  Each handle is
  walked once, so a shared node or a cycle is safe."
  [supports premise? step hs]
  (loop [todo (vec (remove keyword? hs)), seen #{}, leaves #{}, marks (into #{} (filter keyword?) hs)]
    (budget/spend!)
    (if-let [h (peek todo)]
      (let [todo (pop todo)]
        (cond
          (contains? seen h) (recur todo seen leaves marks)
          (premise? h) (recur todo (conj seen h) (conj leaves h) marks)
          :else (let [[todo marks] (reduce (fn [[todo marks] j]
                                             (reduce (fn [[todo marks] x]
                                                       (cond (keyword? x) [todo (conj marks x)]
                                                             (contains? seen x) [todo marks]
                                                             :else [(conj todo x) marks]))
                                                     [todo marks] (step j)))
                                           [todo marks] (budget/checked-seq (get supports h)))]
                  (recur todo (conj seen h) leaves marks))))
      {:leaves leaves :marks marks})))

(defn- leaf-walk
  "`{:leaves #{h} :marks #{k} :unsupported #{h}}`: one walk down from the handles `hs` to
  the premises their support bottoms out in.  Each handle's justifications are read once,
  filtered to the valid ones its own context reads as `:supports`
  (`exc/justification-verdicts`); `step` gives what each descends to.  `keep?` sees every
  node the walk meets (a handle, a justification, a mark of `step`'s) before it is used:
  a rejected node halts the walk there, neither descended nor kept.  A kept premise is a
  leaf; a kept mark is collected; a non-premise with no such justification is
  `:unsupported`.  Each node is visited once, so many starts share the work and a cycle
  is safe."
  [kb keep? step hs]
  (let [tms (reasoning/tms kb)
        records (:records kb)
        valid? (jtms/region-valid-fn tms #{} nil #{})]
    (loop [todo (into [] (budget/checked-seq hs)), seen #{}, leaves #{}, marks #{}, unsupported #{}]
      (budget/spend!)
      (if-let [x (peek todo)]
        (let [todo (pop todo), seen' (conj seen x)]
          (cond
            (contains? seen x) (recur todo seen leaves marks unsupported)
            (not (budget/checked-call #(keep? x))) (recur todo seen' leaves marks unsupported)
            (keyword? x) (recur todo seen' leaves (conj marks x) unsupported)
            (jtms/premise? tms x) (recur todo seen' (conj leaves x) marks unsupported)
            :else
            (let [record (p/get-sentex records x)
                  verdicts (when record
                             (budget/checked-call
                              #(exc/justification-verdicts kb x (:context record))))
                  js (when record
                       (into []
                             (comp (keep #(jtms/justification tms %))
                                   (filter #(and (budget/checked-call (fn [] (valid? #{} %)))
                                                 (= :supports (get verdicts (:id %))))))
                             (budget/checked-seq (jtms/supports tms x))))
                  todo (reduce (fn [todo j]
                                 (budget/spend!)
                                 (if (budget/checked-call #(keep? j))
                                   (into todo (remove seen') (step j))
                                   todo))
                               todo js)]
              (recur todo seen' leaves marks
                     (cond-> unsupported (and record (empty? js)) (conj x))))))
        {:leaves leaves :marks marks :unsupported unsupported}))))

(defn asserted-leaves-such-that
  "`{:leaves #{h} :computed? b}`: the premises the support of `h-or-hs` (a handle or a
  collection of them, walked together) bottoms out in, read through the justifications
  that are valid and that each handle's own context reads as `:supports`
  (`exc/justification-verdicts`), so a guard-covered or blocked alternative contributes
  nothing.  `keep?` is a unary filter on every node the walk meets — a handle, a
  justification, or the mark `:computed` that stands for the literals of a firing that
  names no antecedent — defaulting to keeping all; a rejected node halts the walk there
  and contributes nothing.  A premise is its own leaf.  A firing's rule is a node like its
  antecedents: an asserted rule is a leaf, a deduced one is walked.  `:computed?` is true
  when a kept `:computed` mark is met.  Cycle-safe; each handle is read once."
  ([kb h-or-hs] (asserted-leaves-such-that kb (constantly true) h-or-hs))
  ([kb keep? h-or-hs]
   (let [{:keys [leaves marks]} (leaf-walk kb keep? walked-handles
                                           (if (coll? h-or-hs) h-or-hs [h-or-hs]))]
     {:leaves leaves :computed? (contains? marks :computed)})))

(defn asserted-leaves
  "`asserted-leaves-such-that` handle `h`, keeping every node."
  [kb h]
  (asserted-leaves-such-that kb h))

(defn- skeletal-informant?
  "Does `informant` store engine scaffolding: a lifted copy or an arity-class copy?"
  [informant]
  (or (= 'decontextualized_predicate informant) (= chain/arity-class-informant informant)))

(defn- spelling-informant?
  "Does `informant` store a spelling of its first antecedent: a mint or a respelling?"
  [kb informant]
  (or (kb/mint-informant? kb informant) (= jtms/respell-informant informant)))

(defn- role-step
  "`walked-handles` for the defining walk: a scaffolding copy is skeletal without
  descending to the fact it copies, and a spelling descends to its source alone."
  [kb]
  (fn [j]
    (let [informant (:informant j)]
      (cond
        (skeletal-informant? informant) [:skeletal]
        (spelling-informant? kb informant) [(first (:antecedents j))]
        :else (walked-handles j)))))

(defn- defining-step
  "`walked-handles` for the defining walk, except that a spelling descends to its source
  alone: the rest of its antecedents are the marks or declaration that spell it."
  [kb]
  (fn [j]
    (if (spelling-informant? kb (:informant j))
      [(first (:antecedents j))]
      (walked-handles j))))

(defn- non-skeletal-fn
  "The defining walk's filter: false for a skeletal node.  Skeletal are a premise that is
  another NAT's bookkeeping, a scaffolding copy's justification (a lift or an arity-class
  copy), and the `:computed` mark, the implicit leaf a computed literal stands for."
  [kb]
  (let [tms (reasoning/tms kb)
        records (:records kb)
        bookkeeping? (bookkeeping-test kb)]
    (fn [x]
      (cond
        (keyword? x) false
        (integer? x) (not (and (jtms/premise? tms x)
                               (some-> (p/get-sentex records x) bookkeeping?)))
        :else (not (skeletal-informant? (:informant x)))))))

(defn asserted-defining-leaves
  "`asserted-leaves-such-that` handle or handles `h-or-hs`, ignoring skeletal things: the
  walk halts at a skeletal node (`non-skeletal-fn`) instead of recursing, and a spelling is
  walked to its source alone.  One walk, however many starts."
  [kb h-or-hs]
  (let [{:keys [leaves marks]} (leaf-walk kb (non-skeletal-fn kb) (defining-step kb)
                                          (if (coll? h-or-hs) h-or-hs [h-or-hs]))]
    {:leaves leaves :computed? (contains? marks :computed)}))

(defn- leaf-role
  "The role the asserted leaves `{:leaves :marks}` give a derivation: ordinary when a leaf
  is, skeletal when every leaf is and every mark is skeletal (computed support is the
  engine's own knowledge), else nil."
  [roles {:keys [leaves marks]}]
  (cond
    (some #(= :ordinary (get roles %)) leaves) :ordinary
    (and (or (seq leaves) (seq marks))
         (every? #(= :skeletal (get roles %)) leaves)
         (every? #{:computed :skeletal} marks)) :skeletal))

(defn- support-role
  [kb candidates roles leaves-of justification]
  (budget/spend!)
  (let [informant (:informant justification)
        antecedents (budget/checked-seq (:antecedents justification))
        content (filter candidates antecedents)]
    (cond
      (skeletal-informant? informant) :skeletal
      (spelling-informant? kb informant) (get roles (first antecedents))
      (some #(= :ordinary (get roles %)) content) :ordinary
      (and (seq content) (every? #(= :skeletal (get roles %)) content)) :skeletal
      ;; a content antecedent not yet classified may still decide: wait for it
      (some #(nil? (get roles %)) content) nil
      :else (leaf-role roles (leaves-of justification)))))

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
                                     (when (mentions-term? kb term record) h)))
                         (budget/checked-seq mentions))
        valid? (jtms/region-valid-fn tms #{} nil #{})
        [records supports] (reachable-supports kb mentions valid?)
        bookkeeping? (bookkeeping-test kb)
        premise? #(jtms/premise? tms %)
        step (role-step kb)
        leaf-memo (volatile! {})
        leaves-of (fn [j]
                    (if-let [e (find @leaf-memo (:id j))]
                      (val e)
                      (let [r (support-leaves supports premise? step (step j))]
                        (vswap! leaf-memo assoc (:id j) r)
                        r)))
        ;; a premise an equality merge superseded seeds the role its rewritten twin reads
        seeds (into {} (keep (fn [[h record]]
                               (budget/spend!)
                               (when (and (or (live? h) (jtms/superseded? tms h)) (premise? h))
                                 [h (if (bookkeeping? record) :skeletal :ordinary)]))) records)
        roles (loop [roles seeds]
                (let [next (reduce-kv
                            (fn [result h js]
                              (budget/spend!)
                              (if (or (= :ordinary (get result h)) (not (live? h)))
                                result
                                (let [rs (keep #(support-role kb candidates roles leaves-of %) js)]
                                  (cond
                                    (some #{:ordinary} rs) (assoc result h :ordinary)
                                    (some #{:skeletal} rs) (assoc result h :skeletal)
                                    :else result))))
                            roles supports)]
                  (if (= roles next) roles (recur next))))
        relevant (into [] (filter (fn [[h record]]
                                    (and (live? h)
                                         (mentions-term? kb term record))))
                       (budget/checked-seq mentions))
        unresolved (into []
                         (keep (fn [[h _]]
                                 (when (and (not= :ordinary (get roles h))
                                            (or (nil? (get roles h))
                                                (some #(nil? (support-role kb candidates roles leaves-of %))
                                                      (get supports h))))
                                   h))) (budget/checked-seq relevant))]
    (when (seq unresolved)
      (throw (ex-info "Defining-context support is incomplete."
                      {:type :incomplete-defining-contexts :term term :handles unresolved})))
    {:contexts (budget/checked-call
                #(tax/max-cxs (reasoning/taxonomy kb)
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
