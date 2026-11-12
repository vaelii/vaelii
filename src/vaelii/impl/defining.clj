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

(defn- walked-handles
  "What the leaf walk descends to from justification `j`: every handle it rests on
  (`jtms/rests-on`), its antecedents and its rule alike, so an asserted rule is a leaf and
  a deduced one is walked down to its own support.  The mark `:computed` joins them when
  `j` names no antecedent: a firing whose literals are all computed (`evaluate`,
  `lessThan`, a prover's answer) records no handle for them."
  [j]
  (cond-> (vec (budget/checked-seq (jtms/rests-on j)))
    (empty? (:antecedents j)) (conj :computed)))

(defn- leaf-walk
  "`{:leaves #{h} :marks #{k} :unsupported #{h}}`: one walk down from the handles `hs` to
  the premises their support bottoms out in.  Each handle's justifications are read once,
  filtered to the valid ones its own context reads as `:supports`
  (`exc/justification-verdicts`); `step` gives what each descends to.  `keep?` sees every
  node the walk meets (a handle, a justification, a mark of `step`'s) before it is used:
  a rejected node halts the walk there, neither descended nor kept.  A kept premise is a
  leaf; a kept mark is collected; a non-premise with no such justification is
  `:unsupported`.  Each node is visited once: many starts share the work, cycles are safe."
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

;; A guard-covered or blocked alternative contributes nothing, because only justifications
;; the handle's own context reads as `:supports` (`exc/justification-verdicts`) are walked.
;; A firing's rule is a node like its antecedents: an asserted rule is a leaf, a deduced one
;; is walked.  `:computed` stands for the literals of a firing that names no antecedent.
(defn asserted-leaves-such-that
  "`{:leaves #{h} :computed? b}`: the premises the valid, supporting justifications of
  `h-or-hs` (a handle or a collection, walked together) bottom out in.  `keep?` filters
  every node met (a handle, a justification, or the mark `:computed`), default all; a
  rejected node halts the walk there.  A premise is its own leaf.  `:computed?` is true
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
  (or (contains? '#{decontextualized_predicate eternal_predicate} informant)
      (= chain/arity-class-informant informant)))

(defn- spelling-informant?
  "Does `informant` store a spelling of its first antecedent: a mint or a respelling?"
  [kb informant]
  (or (kb/mint-informant? kb informant) (= jtms/respell-informant informant)))

(defn- defining-step
  "`walked-handles` for the defining walk, except that a spelling descends to its source
  alone: the rest of its antecedents are the marks or declaration that spell it."
  [kb]
  (fn [j]
    (if (spelling-informant? kb (:informant j))
      [(first (:antecedents j))]
      (walked-handles j))))

;; An equation mentions its arguments rather than using them: read as a use, every equation
;; would define `A` by `(equals A A)`.  So it is skeletal for defining.  Skeletality reads the
;; literal's predicate whatever its polarity (`sx/underlying-body`).
(defn- equation?
  "Is `record` an equation (`kb/equality-predicates`), of either polarity?"
  [record]
  (boolean (some-> record sx/sentence-of sx/underlying-body kb/equality-sentence?)))

(defn- non-skeletal-fn
  "The defining walk's filter: false for a skeletal node.  Skeletal are a premise that is
  another NAT's bookkeeping, an equation (`equation?`), stated or derived, negated or not, a scaffolding
  copy's justification (a lift or an arity-class copy), and the `:computed` mark, the
  implicit leaf a computed literal stands for."
  [kb]
  (let [tms (reasoning/tms kb)
        records (:records kb)
        bookkeeping? (bookkeeping-test kb)]
    (fn [x]
      (cond
        (keyword? x) false
        (integer? x) (let [record (p/get-sentex records x)]
                       (not (or (equation? record)
                                (and (jtms/premise? tms x)
                                     (some-> record bookkeeping?)))))
        :else (not (skeletal-informant? (:informant x)))))))

(defn- defining-walk
  [kb hs]
  (leaf-walk kb (non-skeletal-fn kb) (defining-step kb) hs))

(defn asserted-defining-leaves
  "`asserted-leaves-such-that` handle or handles `h-or-hs`, ignoring skeletal things: the
  walk halts at a skeletal node (`non-skeletal-fn`) instead of recursing, and a spelling is
  walked to its source alone.  One walk, however many starts."
  [kb h-or-hs]
  (let [{:keys [leaves marks]} (defining-walk kb (if (coll? h-or-hs) h-or-hs [h-or-hs]))]
    {:leaves leaves :computed? (contains? marks :computed)}))

(defn- definition-evidence*
  [kb term]
  (let [term (sx/canon term)
        tms (reasoning/tms kb)
        hidden? (or (budget/checked-call #(exc/own-hidden-fn kb)) (constantly false))
        live? #(and (jtms/in? tms %) (not (hidden? %)))
        mentions (into {} (keep (fn [record]
                                  (budget/spend!)
                                  (when (mentions-term? kb term record) [(:id record) record])))
                       (budget/checked-seq (kb/find-sentexes kb term)))
        relevant (into [] (filter live?) (budget/checked-seq (keys mentions)))
        {:keys [leaves unsupported]} (defining-walk kb relevant)
        unresolved (filterv unsupported relevant)]
    (when (seq unresolved)
      (throw (ex-info "Defining-context support is incomplete."
                      {:type :incomplete-defining-contexts :term term :handles unresolved})))
    ;; a premise an equality merge superseded stays the leaf its respelled twin reads
    (let [homes (into #{} (keep #(when (or (live? %) (jtms/superseded? tms %))
                                   (:context (get mentions %))))
                      (budget/checked-seq leaves))]
      {:contexts (budget/checked-call
                  #(tax/max-cxs (reasoning/taxonomy kb) homes))
       :skeletal-only? (boolean (and (seq relevant) (empty? homes)))})))

(defn definition-evidence
  "`{:contexts #{c} :skeletal-only? b}`: the maximal contexts of the ordinary asserted
  leaves that mention `term`, read in one walk (`asserted-defining-leaves`) down from all
  its believed mentions, and whether it has such mentions but no such leaf, every way in
  being skeletal.  A believed derived mention with no supporting justification throws
  :incomplete-defining-contexts.  An absent assertion is not evidence of skeletal-only
  definition.  An unrepresented term (`sx/indexable-term?` false) is defined in CxUniverse."
  [kb term]
  (if (not (sx/indexable-term? (sx/canon term)))
    {:contexts #{'CxUniverse} :skeletal-only? false}
    (definition-evidence* kb term)))

(defn defining-contexts
  "The maximal ordinary defining contexts. Unsupported believed mentions throw
  :incomplete-defining-contexts; an empty set does not certify skeletal-only evidence."
  [kb term]
  (:contexts (definition-evidence kb term)))
